(* Copyright 2014 Baharak Saberidokht <baharak1364@gmail.com> *)

(* Licensed under the Apache License, Version 2.0 (the "License"); *)
(* you may not use this file except in compliance with the License. *)
(* You may obtain a copy of the License at *)

(*     http://www.apache.org/licenses/LICENSE-2.0 *)

(* Unless required by applicable law or agreed to in writing, software *)
(* distributed under the License is distributed on an "AS IS" BASIS, *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and *)
(* limitations under the License. *)

Require Export SfLib.

(* Node in a graph (tree). [@node X id data] means node with id [id]
   that stores some data (properties) of type [X] *)
Inductive node {X : Type} : Type :=
| nd : nat -> X -> node.

Definition data {X : Type} (n : @node X) : X :=
  match n with
    | nd k d => d
  end
.


Inductive bt {X : Type} : Type :=
| btnil : bt
| btsub : @node X -> bt -> bt -> bt
.

Check (btnil).
Check (btsub (nd 2 _) btnil btnil).
Check (btsub (nd 3 _)
  (btsub (nd 1 _) btnil btnil)
  (btsub (nd 2 _) btnil btnil)).


Fixpoint height {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub _ l r =>
      match l, r with
        | btnil, btnil => 0
        | btnil, btsub _ _ _ => S (height r)
        | btsub _ _ _, btnil => S (height l)
        | _, _ => S (max (height l) (height r))
      end
  end
.
Example test_height_0_empty : @height nat btnil = 0.
Proof. reflexivity.
Qed.
Example test_height_0_single : @height nat (btsub (nd 3 0) btnil btnil) = 0.
Proof. reflexivity.
Qed.
Example test_height_1_bal : @height nat
  (btsub (nd 3 0)
    (btsub (nd 1 0) btnil btnil)
    (btsub (nd 4 0) btnil btnil)
  ) = 1.
Proof. reflexivity.
Qed.
Example test_height_1_hil : @height nat
  (btsub (nd 3 0) (btsub (nd 1 0) btnil btnil) btnil) = 1.
Proof. reflexivity.
Qed.
Example test_height_1_hir : @height nat
  (btsub (nd 3 0) btnil (btsub (nd 4 0) btnil btnil)) = 1.
Proof. reflexivity.
Qed.
Example test_height_2lr : @height nat
  (btsub (nd 5 0)
    (btsub (nd 3 0)
      btnil
      (btsub (nd 4 0) btnil btnil))
    (btsub (nd 6 0) btnil btnil)
  ) = 2.
Proof. reflexivity.
Qed.

Lemma height_S_max {X : Type} : forall n l ln ll lr r rn rl rr,
  l = (btsub ln ll lr) ->
  r = (btsub rn rl rr) ->
  S (max (height l) (height r)) = height (@btsub X n l r).
Proof.
  intros.
  destruct l;
    destruct r;
      try reflexivity.
  inversion H.
  inversion H0.
Qed.


(* Size of a binary tree = the number of nodes in it *)
Fixpoint size {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub _ l r =>
      S ((size l) + (size r))
  end
.
Example test_size_0_empty : @size nat btnil = 0.
Proof. reflexivity.
Qed.
Example test_size_1_single : @size nat (btsub (nd 3 0) btnil btnil) = 1.
Proof. reflexivity.
Qed.
Example test_size_2 : @size nat
  (btsub (nd 5 0)
    btnil
    (btsub (nd 3 0) btnil btnil)
  ) = 2.
Proof. reflexivity.
Qed.
Example test_size_4 : @size nat
  (btsub (nd 5 0)
    (btsub (nd 3 0)
      btnil
      (btsub (nd 4 0) btnil btnil))
    (btsub (nd 6 0) btnil btnil)
  ) = 4.
Proof. reflexivity.
Qed.

Lemma le_relax_l : forall ls' ls l r,
  ls' <= ls ->
  ls + l <= r ->
  ls' + l <= r.
Proof. intros. omega.
Qed.

Lemma le_relax_r : forall l r rs rs',
  l <= r + rs ->
  rs <= rs' ->
  l <= r + rs'.
Proof. intros. omega.
Qed.

Lemma le_either : forall a b, {a <= b} + {b <= a}.
Proof.
    intros. generalize dependent b.
    induction a;
      destruct b;
        try (left; omega);
          try (right; omega).
      remember (IHa b) as IHa'. inversion IHa'.
      left. omega.
      right. omega.
Qed.

Fixpoint twopow (exp : nat) :=
  match exp with
    | 0 => 1
    | S exp' => (twopow exp') + (twopow exp')
  end
.
Example twopow_0 : twopow 0 = 1. Proof. reflexivity. Qed.
Example twopow_1 : twopow 1 = 2. Proof. reflexivity. Qed.
Example twopow_10 : twopow 10 = 1024. Proof. reflexivity. Qed.

Lemma twopow_nondec : forall a b,
  a <= b -> twopow a <= twopow b.
Proof.
  intros. induction H. reflexivity.
  simpl. omega.
Qed.

(* The number of nodes in a binary tree is less than 2^(h + 1) *)
Theorem bound_size {X : Type} : forall (t : @bt X),
  S (size t) <= twopow (S (height t)).
Proof.
  intros. induction t.
  Case "btnil".
    unfold size. unfold height. subst.
    unfold twopow. omega.

  Case "btsub".
    assert (forall a b, a <= twopow b -> S a <= twopow (S b)) as Hah.
      assert (forall e, 1 <= twopow e). induction e. reflexivity. simpl. omega.
    intros. simpl. assert (1 <= twopow b) by apply H. omega.

    destruct t1;
      destruct t2.
    simpl. omega.

    SCase "no left".
    remember (btsub n0 t2_1 t2_2) as r.
    replace (height (btsub n btnil r)) with (S (height r)).
    replace (size (btsub n btnil r)) with (S (size r)).
    apply Hah. apply IHt2.
    reflexivity.
    destruct r. inversion Heqr. reflexivity.

    SCase "no right".
    remember (btsub n0 t1_1 t1_2) as l.
    replace (height (btsub n l btnil)) with (S (height l)).
    replace (size (btsub n l btnil)) with (S (size l)).
    apply Hah. apply IHt1.
    simpl. omega.
    destruct l. inversion Heql. reflexivity.

    SCase "both".
    remember (btsub n0 t1_1 t1_2) as l.
    remember (btsub n1 t2_1 t2_2) as r.
    replace (size (btsub n l r)) with (S ((size l) + (size r)));
      try reflexivity.
    replace (height (btsub n l r)) with (S (max (height l) (height r)));
      try (eapply height_S_max; eassumption).
    assert (forall e, twopow (S e) = twopow e + twopow e) as Hp by reflexivity.

    destruct (le_either (height l) (height r)) as [Hhi | Hhi];
      rewrite plus_n_Sm; rewrite plus_comm;
        rewrite plus_n_Sm;
          rewrite plus_comm.

    SSCase "higher right".
      assert ((height l) <= (height r)) as Hmax by apply Hhi.
      apply le_n_S in Hhi. apply twopow_nondec in Hhi.
      rewrite max_r;
        try assumption.
      assert (S (size l) <= twopow (S (height r))) as H.
      eapply le_trans; eassumption.
      (* apply le_trans with (p := twopow (S (height r))) in IHt1. *)
      rewrite Hp. eapply le_relax_l. eassumption. omega.

    SSCase "higher left".
      assert ((height r) <= (height l)) as Hmax by apply Hhi.
      apply le_n_S in Hhi. apply twopow_nondec in Hhi.
      rewrite max_l;
        try assumption.
      rewrite Hp. omega.            (* a more automated way *)
Qed.



(* For search trees, [id] can serve as a key (used for ordering) *)
Definition key {X : Type} (n : @node X) : nat :=
  match n with
    | nd k d => k
  end
.

Fixpoint minkey {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub (nd k _) l r =>
      match l, r with
        | btnil, btnil => k
        | btnil, btsub _ _ _ => min k (minkey r)
        | btsub _ _ _, btnil => min k (minkey l)
        | _, _ => min k (min (minkey l) (minkey r))
      end
  end
.

Fixpoint maxkey {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub (nd k _) l r =>
      match l, r with
        | btnil, btnil => k
        | btnil, btsub _ _ _ => max k (maxkey r)
        | btsub _ _ _, btnil => max k (maxkey l)
        | _, _ => max k (max (maxkey l) (maxkey r))
      end
  end
.

Inductive bst {X : Type} : @bt X -> Prop :=
| bstnil : bst btnil
| bstleaf : forall k d,
  bst (btsub (nd k d) btnil btnil)
| bstbal : forall k d l lk ld ll lr r rk rd rl rr,
  l = (btsub (nd lk ld) ll lr) ->
  (maxkey l) < k ->
  bst l ->
  r = (btsub (nd rk rd) rl rr) ->
  (minkey r) > k ->
  bst r ->
  bst (btsub (nd k d) l r)
| bsthil : forall k d l lk ld ll lr,
  l = (btsub (nd lk ld) ll lr) ->
  (maxkey l) < k ->
  bst l ->
  bst (btsub (nd k d) l btnil)
| bsthir : forall k d r rk rd rl rr,
  r = (btsub (nd rk rd) rl rr) ->
  (minkey r) > k ->
  bst r ->
  bst (btsub (nd k d) btnil r)
.

Example test_bst_0 : bst (
  (btsub (nd 5 0)
    (btsub (nd 3 0)
      btnil
      (btsub (nd 4 0) btnil btnil))
    (btsub (nd 6 0) btnil btnil))).
Proof.
  eapply bstbal;
    try (simpl; omega);
      try constructor.
  eapply bsthir;
    constructor. (* constructor also solves inequality - no need for omega *)
Qed.

Definition hbal (h1 h2 : nat) : Prop :=
  h1 = h2 \/ ((S h1) = h2 \/ h1 = (S h2))
.

Example test_hbal_bal : hbal 2 2. left. reflexivity. Qed.
Example test_hbal_hil : hbal 1 0. right. right. reflexivity. Qed.
Example test_hbal_hir : hbal 3 4. right. left. reflexivity. Qed.
Example test_hbal_none_hil : ~ hbal 4 2. unfold hbal. omega. Qed.
Example test_hbal_none_hir : ~ hbal 2 4. unfold hbal. omega. Qed.


(* AVL tree - a Binary Search Tree s.t. height diff of every subtree <= 1 *)
Inductive avlt {X : Type} : @bt X -> Prop :=
| avltnil : avlt btnil
| avltsub : forall k d l r,
  hbal (height l) (height r) ->
  avlt l ->
  avlt r ->
  bst (btsub (nd k d) l r) ->
  avlt (btsub (nd k d) l r)
.

(* Q: Would proofs be easier if we separate bal and bst as requirements
   and define AVL tree as a combination of both (see below)? *)

Inductive bal {X : Type} : @bt X -> Prop :=
| balnil : bal btnil
| balsub : forall k d l r,
  hbal (height l) (height r) ->
  bal l ->
  bal r ->
  bal (btsub (nd k d) l r)
.

Definition avl2 {X : Type} (t : @bt X) := bst t /\ bal t.

(* Q: If we add height as parameter, it becomes simpler. Is this a good idea? *)
Inductive avl3 {X : Type} : @bt X -> nat -> Prop :=
| avlnil' : avl3 btnil 0
| avlbal : forall k d h l r,
  avl3 l h ->
  avl3 r h ->
  bst (btsub (nd k d) l r) ->
  avl3 (btsub (nd k d) l r) (S h)
| avlhil : forall k d h l r,
  avl3 l (S h) ->
  avl3 r h ->
  bst (btsub (nd k d) l r) ->
  avl3 (btsub (nd k d) l r) (S (S h))
| avlhir : forall k d h l r,
  avl3 l h ->
  avl3 r (S h) ->
  bst (btsub (nd k d) l r) ->
  avl3 (btsub (nd k d) l r) (S (S h))
.
