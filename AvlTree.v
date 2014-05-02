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

Require Import Arith.Max.
Require Import Arith.Min.
Require Import GenericMinMax.

(* Node in a graph (tree). [@node X id data] means node with id [id]
   that stores some data (properties) of type [X] *)
Inductive node {X : Type} : Type :=
| nd : nat -> X -> node.
Hint Constructors node.

Definition data {X : Type} (n : @node X) : X :=
  match n with
    | nd k d => d
  end
.


Inductive bt {X : Type} : Type :=
| btnil : bt
| btsub : @node X -> bt -> bt -> bt
.
Hint Constructors node.

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
  k < (minkey r) ->
  bst r ->
  bst (btsub (nd k d) l r)
| bsthil : forall k d l lk ld ll lr,
  l = (btsub (nd lk ld) ll lr) ->
  (maxkey l) < k ->
  bst l ->
  bst (btsub (nd k d) l btnil)
| bsthir : forall k d r rk rd rl rr,
  r = (btsub (nd rk rd) rl rr) ->
  k < (minkey r) ->
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

(* It is easier to work with successors of [height] because the case when
   [height t = 0] is ambiguous - t is either [btnil] or [btsub _ btnil btnil].*)

Fixpoint bthsucc {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub _ l r => S (max (bthsucc l) (bthsucc r))
  end.

Lemma bthsucc_Sheight {X : Type} : forall n l r,
  (bthsucc (@btsub X n l r)) = S (height (@btsub X n l r)).
Proof.
  intros. remember (btsub n l r) as t.
  induction t. inversion Heqt.
 (*  destruct t1; *)
 (*    destruct t2; *)
 (*      simpl. *)
 (*  reflexivity.  simpl. *)
 (*  simpl. destruct (le_either (height t1) (height t2)). *)
 (*  rewrite max_r. *)
 (* rewrite max_l. *)
               (* STUCK *)
Admitted.

(* Inductive propositions [btleanl] and [btleanr] tell if the tree leans
   to the left/right with a balance factor (height difference) of at [f].

   Note that the first constructor is necessary to prove the case
   when one child is nil (because height of both leaf and nil is 0). *)

Inductive btleanl {X : Type} (f : nat) : @bt X -> Prop :=
| btleanlnil :
  f = 0 ->
  btleanl f btnil
| btleanlsub : forall n l r,
  f + bthsucc r = bthsucc l ->
  btleanl f (@btsub X n l r)
.
Hint Constructors btleanl.

Inductive btleanr {X : Type} (f : nat) : @bt X -> Prop :=
| btleanrnil :
  f = 0 ->
  btleanr f btnil
| btleanrsub : forall n l r,
  f + bthsucc l = bthsucc r ->
  btleanr f (@btsub X n l r)
.
Hint Constructors btleanr.

Example test_btleanr_5_nil : ~ btleanr 5 (@btnil nat).
Proof. intro. solve by inversion 2.
Qed.
Example test_btleanr_0_leaf : btleanr 0 (btsub (nd 0 0) btnil btnil).
Proof. constructor. reflexivity.
Qed.
Example test_btleanr_0_nil : btleanr 0 (@btnil nat).
Proof. auto.
Qed.
Example test_btleanr_0_bal : btleanr 0 (btsub (nd 2 0)
  (btsub (nd 1 0) btnil btnil)
  (btsub (nd 3 0) btnil btnil)).
Proof. constructor. simpl. reflexivity.
Qed.
Example test_btleanr_1_l : ~ btleanr 1
(btsub (nd 2 0) (btsub (nd 1 0) btnil btnil) btnil).
Proof. intro. solve by inversion 2.
Qed.
Example test_btleanr_1_r : btleanr 1
(btsub (nd 2 0) btnil (btsub (nd 1 0) btnil btnil)).
Proof. auto.
Qed.

Inductive ndbal {X : Type} : @bt X -> Prop :=
| ndbalnil :
  ndbal btnil
| ndbalbal : forall n l r,
  bthsucc l = bthsucc r ->
  ndbal (btsub n l r)
| ndbalhil : forall n l r,
  btleanl 1 (btsub n l r) ->
  ndbal (btsub n l r)
| ndbalhir : forall n l r,
  btleanr 1 (btsub n l r) ->
  ndbal (btsub n l r)
.

(*     g             p     *)
(*    / \           / \    *)
(*   u   p   -->   g   r   *)
(*      / \       / \      *)
(*     l   r     u   l     *)
Inductive btrotl {X : Type} : @bt X -> @bt X -> Prop :=
| btrotl0 : forall gn pn l u r, btrotl
  (btsub gn u (btsub pn l r))
  (btsub pn (btsub gn u l) r)
.

(*     g             p     *)
(*    / \           / \    *)
(*   p   u   -->   l   g   *)
(*  / \               / \  *)
(* l   r             r   u *)
Inductive btrotr {X : Type} : @bt X -> @bt X -> Prop :=
| btrotr0 : forall gn pn l u r, btrotr
  (btsub gn (btsub pn l r) u)
  (btsub pn l (btsub gn r u))
.

Inductive btrebal {X : Type} : @bt X -> @bt X -> Prop :=
| btrebalbal : forall t,        (*  *)
  ndbal t ->
  btrebal t t
| btreballl : forall n l r t',  (*                     g (2)         p (-1|0) *)
  btleanl 2 (btsub n l r) ->    (*                    /             / \       *)
  btleanl 1 l \/ btleanl 0 l -> (*                   p (1|0)  -->  l   g      *)
  btrotr (btsub n l r) t' ->    (*                  /                         *)
  btrebal (btsub n l r) t'      (*                 l                          *)
| btrebalrr : forall n l r t',  (*                     g (-2)        p (1|0)  *)
  btleanr 2 (btsub n l r) ->    (*                      \           / \       *)
  btleanr 1 r \/ btleanr 0 r -> (*                (-1|0) p    -->  g   r      *)
  btrotr (btsub n l r) t' ->    (*                        \                   *)
  btrebal (btsub n l r) t'      (*                         r                  *)
| btreballr : forall n l r l' t', (*   g (2)           g (2)         r (-1|0) *)
  btleanl 2 (btsub n l r) -> (*       /               /             / \       *)
  btleanr 1 l ->  (*                 p (-1)   -->    r (1|0)  -->  p   g      *)
  btrotl l l' -> (*                   \             /                         *)
  btrotr (btsub n l' r) t' -> (*       r           p                          *)
  btrebal (btsub n l r) t'
| btrebalrl : forall n l r r' t', (*   g (-2)          g (-2)        l (1|0)  *)
  btleanl 2 (btsub n l r) -> (*         \               \           / \       *)
  btleanl 1 r ->  (*                 (1) p    --> (-1|0) l    -->  g   p      *)
  btrotr r r' -> (*                     /                 \                   *)
  btrotr (btsub n l r') t' -> (*       l                   p                  *)
  btrebal (btsub n l r) t'
.

(* I decided to separete the rebalancing operation from the insertion beacuse:
   1) there would be twice as many constructors because we would repeat
   the same rebalancing logic for both the case when I insert left and right
   2) to avoid repeating it when I implement AVL deletion *)

Lemma bst_maxkey_nd {X : Type} : forall k d l,
  @bst X (btsub (nd k d) l btnil) ->
  maxkey (btsub (nd k d) l btnil) = k.
Proof.
  intros.
  induction l as [| [lk ld]]. reflexivity.
  inversion H; subst. inversion H7.
  clear H3 lk0 ld0 ll lr.
  (* STUCK *)
Admitted.

Lemma bst_minkey_nd {X : Type} : forall k d r,
  @bst X (btsub (nd k d) btnil r) ->
  minkey (btsub (nd k d) btnil r) = k.
Proof.
Admitted.

Lemma bst_maxkey_r {X : Type} : forall k d l r,
  @bst X (btsub (nd k d) l r) ->
  r <> @btnil X ->
  maxkey (btsub (nd k d) l r) = maxkey r.
Proof.
  intros.
  generalize dependent l.
  induction r. intuition.
  intros.
  destruct n as [rk rd].
  destruct l.
    destruct r1;
      destruct r2;
        auto.
  (* STUCK *)
Admitted.

Lemma bst_minkey_l {X : Type} : forall k d l r,
  @bst X (btsub (nd k d) l r) ->
  l <> btnil ->
  minkey (btsub (nd k d) l r) = minkey l.
Proof.
Admitted.

Lemma btrotr_bst {X : Type} : forall t t',
  @bst X t ->
  btrotr t t' ->
  bst t'.
Proof.
  intros g p' Hs Hr.
  destruct p';
    inversion Hr; subst; clear Hr.
  rename p'1 into l, n into pn.
  destruct pn as [pk pd].
  destruct gn as [gk gd].
  set (btsub (nd pk pd) l r) as p in *.
  set (btsub (nd gk gd) r u) as g' in *.
  set (btsub (nd pk pd) l g') as p' in *.
  assert (bst p /\ bst u) as [Hsp Hsu]
    by (split; inversion Hs; try constructor; assumption).
  assert (maxkey p < gk) as Hkp by (inversion Hs; assumption).
  assert (u <> btnil -> gk < minkey u) as Hku
    by (intro; destruct u; inversion Hs; intuition).
  assert (bst l) as Hsl by (inversion Hsp; try constructor; assumption).

  destruct r as [| [rk rd] rl rr].
  Case "r = btnil".
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]. apply bstleaf.
      eapply bsthir; subst g'; auto. apply Hku. intro H. inversion H.
    assert (pk < minkey g')
      by (subst p g'; rewrite bst_maxkey_nd in Hkp; try rewrite bst_minkey_nd;
        assumption).
    destruct l as [| ln ll lr].
    SCase "l = btnil".
      eapply bsthir; subst g'; auto.
    SCase "l = btsub".
      set (btsub ln ll lr) as l.
      assert (maxkey l < pk) by (inversion Hsp; assumption).
      destruct ln as [lk ld].
      eapply bstbal; subst g'; auto.
  Case "r = btsub".
  set (btsub (nd rk rd) rl rr) as r.
    assert (bst r) as Hsr by (inversion Hsp; assumption).
    assert (maxkey r < gk) as Hkr
      by (subst p; rewrite bst_maxkey_r in Hkp; auto; intro H'; inversion H').
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]. eapply bsthil; auto.
      eapply bstbal; subst g'; auto. apply Hku. intro H'. inversion H'.
    assert (pk < minkey g').
      assert (pk < minkey r) as Hkr' by (inversion Hsp; assumption).
      subst g'. rewrite bst_minkey_l; auto.
      intro H'. inversion H'.
    destruct l as [| [lk ld] ll lr].
    SCase "l = btnil".
      eapply bsthir; subst g'; auto.
    SCase "l = btsub".
    set (btsub (nd lk ld) ll lr) as l.
      assert (maxkey l < pk) by (inversion Hsp; intuition).
      eapply bstbal; subst g'; auto.
Qed.

Inductive avlins {X : Type} : @bt X -> @node X -> @bt X -> Prop :=
| avlinsnil : forall k' d',
  avlins btnil (nd k' d') (btsub (nd k' d') btnil btnil)
| avlinsleft : forall k' d' k d l r l' t,
  k' < k ->
  avlins l (nd k' d') l' ->
  btrebal (btsub (nd k d) l' r) t ->
  avlins (btsub (nd k d) l r) (nd k' d') t
| avlinsright : forall k' d' k d l r r' t,
  k < k' ->
  avlins r (nd k' d') r' ->
  btrebal (btsub (nd k d) l r') t ->
  avlins (btsub (nd k d) l r) (nd k' d') t
.

(* AVL tree - a Binary Search Tree s.t. height diff of every subtree <= 1 *)
Inductive avlt {X : Type} : @bt X -> Prop :=
| avltnil : avlt btnil
| avltsub : forall k d l r,
  ndbal (btsub (nd k d) l r) ->
  avlt l ->
  avlt r ->
  bst (btsub (nd k d) l r) ->
  avlt (btsub (nd k d) l r)
.

(* Q: Would proofs be easier if we separate bal and bst as requirements
   and define AVL tree as a combination of both (see below)? *)

Inductive btbal {X : Type} : @bt X -> Prop :=
| balnil : btbal btnil
| balsub : forall k d l r,
  ndbal (btsub (nd k d) l r) ->
  btbal l ->
  btbal r ->
  btbal (btsub (nd k d) l r)
.

Definition avlt2 {X : Type} (t : @bt X) := bst t /\ btbal t.


Theorem btrebal_bst {X : Type} : forall t t',
  @bst X t ->
  btrebal t t' ->
  bst t'.
Proof.
  intros t t' Hs Hb.
  admit. (* TODO:  *)
Qed.

(* Lemma: A BST remains BST if we insert a smaller key to its left subtree. *)
Lemma avlins_bst_l {X : Type} : forall k d l r k' d' l',
  @bst X (btsub (nd k d) l r) ->
  k' < k ->
  avlins l (nd k' d') l' ->
  @bst X (btsub (nd k d) l' r).
Proof. admit.
Qed.

Lemma avlins_bst_r {X : Type} : forall k d l r k' d' r',
  @bst X (btsub (nd k d) l r) ->
  k < k' ->
  avlins r (nd k' d') r' ->
  @bst X (btsub (nd k d) l r').
Proof.
Admitted.

(* Lemma: Inserting and rebalancing an AVL tree preserves its BST property. *)
Theorem avlins_bst {X : Type} : forall t n t',
  @bst X t -> avlins t n t' -> bst t'.
Proof.
  intros t n t' Hs Hi.
  induction t;
    inversion Hi; subst.
  Case "insert leaf".
    constructor.
  Case "insert left".
    try assert (bst (btsub (nd k d) l' t2)) as Hn
      by (eapply avlins_bst_l; eassumption).
    eapply btrebal_bst;
      eassumption.
  Case "insert right".
    try assert (bst (btsub (nd k d) t1 r')) as Hn
      by (eapply avlins_bst_r; eassumption).
    eapply btrebal_bst;
      eassumption.
Qed.

(* Lemma: After inserting to an AVL, the height increases by at most one. *)
(* (note that it can also decrease because insertion involves rebalancing,
   so that's we didn't put also: bthsucc t <= bthsucc t'' *)
Lemma avlins_bthsucc {X : Type} : forall t n t'',
  @avlins X t n t'' ->
  bthsucc t'' <= S (bthsucc t).
Proof.
  intros t n t'' Ha.
  generalize dependent t''.
  generalize dependent n.
  induction t; intros;
    inversion Ha; subst;
      simpl.
  omega.

  destruct (le_either (bthsucc t1) (bthsucc t2)).
  rewrite max_r; try assumption.
  apply IHt1 in H5.
  (* TODO: need more lemmas *)
Admitted.

(* Fixpoint btleft {X : Type} (t : @bt X) : *)
(*   match t with | *)
(*     btnil  *)

Lemma btrotr_hsucc_l {X : Type} : forall n l r n' l' r',
  @btrotr X (btsub n l r) (btsub n' l' r') ->
  S (bthsucc l') <= bthsucc l.
Proof with eauto.
  intros n0 l0 r0 n0' l0' r0' Hr.
  inversion Hr. subst n0 l0 r0 n0' l0' r0'.
  simpl. apply le_n_S.
  destruct (le_either (bthsucc l) (bthsucc r)).
  rewrite max_r; assumption.
  rewrite max_l; omega.
Qed.

Lemma btrotr_hsucc_r {X : Type} : forall n l r n' l' r',
  @btrotr X (btsub n l r) (btsub n' l' r') ->
  S (bthsucc r) <= bthsucc r'.
Proof with eauto.
  intros n0 l0 r0 n0' l0' r0' Hr.
  inversion Hr. subst n0 l0 r0 n0' l0' r0'.
  simpl. apply le_n_S.
  destruct (le_either (bthsucc r) (bthsucc u)).
  rewrite max_r; omega.
  rewrite max_l; assumption.
Qed.

Hint Resolve max_r.
Hint Resolve max_l.
Hint Resolve le_either.

Lemma btrotr_bal {X : Type} : forall n l r t',
  btleanl 2 (btsub n l r) ->
  btleanl 1 l \/ btleanl 0 l ->
  @btrotr X (btsub n l r) t' ->
  ndbal t'.
Proof with auto.
  assert (forall n, S n = max (S n) n) as Ha.
    intros. destruct (le_either (S n) n). omega. rewrite max_l...

  intros g p u t' Hgl Hp Hr.
  inversion Hr; subst; clear Hr.
  destruct Hp as [Hp | Hp];
    inversion Hp; subst; clear Hp;
      inversion Hgl; subst; clear Hgl;
        simpl in H0, H1.
  Case "btleanl 1 l".
    apply ndbalbal. simpl.
    rewrite <- H0 in *.
    remember (bthsucc u) as hu. clear Heqhu.
    remember (bthsucc r) as hr. clear Heqhr.
    erewrite <- Ha in H1.
    destruct (max_dec hr hu); omega.
  Case "btleanl 0 l".
    apply ndbalhir. constructor. simpl.
    rewrite <- H0 in *. clear H0.
    rewrite max_idempotent in H1.
    rewrite succ_max_distr. rewrite <- H1.
    apply Ha.
Qed.

Theorem avlins_avlt {X : Type} : forall t n t'',
  @avlt X t ->
  @avlins X t n t'' ->
  @avlt X t''.
Proof.
  assert (forall X t, @avlt X t -> bst t) as Has.
    intros. inversion H; auto. constructor.

  (* intros t n t'' H Hi. *)
  (* generalize dependent Hi. *)
  (* generalize dependent n. *)
  (* generalize dependent t''. *)
  (* induction H; *)
  (*   intros. *)

  (* inversion Hi. constructor. *)
  (* apply ndbalbal. reflexivity. constructor. constructor. constructor. *)

  (* inversion Hi; subst; clear Hi. *)

  (* assert (bst t'') as Hs'' by *)
  (*   (eapply btrebal_bst; try eapply avlins_bst_l; eassumption). *)
  (* apply IHavlt1 in H10. *)


  (* destruct t''. constructor. *)
  (* destruct n. apply avltsub. *)
  (* admit. inversion H10; subst. *)

  intros t n t'' H Hi.
  generalize dependent Hi.
  generalize dependent n.
  generalize dependent t''.
  induction t;
    intros.
  admit.

  inversion Hi; subst; clear Hi.
  inversion H; subst.
  eapply IHt1 with (t'' := l') in H8;
    try eassumption.

  assert (bst t'') as Hs'' by
    (eapply btrebal_bst; try eapply avlins_bst_l; eassumption).

  inversion H7; subst; clear H7.
  constructor; assumption.
  inversion H13; subst.
  (*
     L1 =
 *)

  admit.
  inversion H0; subst.

admit. admit. admit.
  admit. admit.
  (* induction H; *)
  (*   intros. *)

(* end *)
Admitted.
