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
Hint Constructors bt.

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
| bstbal : forall k d lk ld ll lr rk rd rl rr,
  (maxkey (btsub (nd lk ld) ll lr)) < k ->
  bst (btsub (nd lk ld) ll lr) ->
  k < (minkey (btsub (nd rk rd) rl rr)) ->
  bst (btsub (nd rk rd) rl rr) ->
  bst (btsub (nd k d) (btsub (nd lk ld) ll lr) (btsub (nd rk rd) rl rr))
| bsthil : forall k d lk ld ll lr,
  (maxkey (btsub (nd lk ld) ll lr)) < k ->
  bst (btsub (nd lk ld) ll lr) ->
  bst (btsub (nd k d) (btsub (nd lk ld) ll lr) btnil)
| bsthir : forall k d rk rd rl rr,
  k < (minkey (btsub (nd rk rd) rl rr)) ->
  bst (btsub (nd rk rd) rl rr) ->
  bst (btsub (nd k d) btnil (btsub (nd rk rd) rl rr))
.
Hint Constructors bst.

Example test_bst_0 : bst (
  (btsub (nd 5 0)
    (btsub (nd 3 0)
      btnil
      (btsub (nd 4 0) btnil btnil))
    (btsub (nd 6 0) btnil btnil))).
Proof. repeat constructor.
Qed.

Inductive bsthaskey {X : Type} : @bt X -> nat -> Prop :=
| bsthaskeynd : forall k d l r,
  bsthaskey (btsub (nd k d) l r) k
| bsthaskeyl : forall k' k d l r,
  k' < k ->
  bsthaskey l k' ->
  bsthaskey (btsub (nd k d) l r) k'
| bsthaskeyr : forall k' k d l r,
  k < k' ->
  bsthaskey r k' ->
  bsthaskey (btsub (nd k d) l r) k'
.
Hint Constructors bsthaskey.

Inductive haskey {X : Type} : @bt X -> nat -> Prop :=
| haskeynd : forall k d l r,
  haskey (btsub (nd k d) l r) k
| haskeyl : forall k' k d l r,
  haskey l k' ->
  haskey (btsub (nd k d) l r) k'
| haskeyr : forall k' k d l r,
  haskey r k' ->
  haskey (btsub (nd k d) l r) k'
.
Hint Constructors haskey.

(* Next, we prove its correctness:
   [bsthaskey t k] holds if and only if tree contains the key, [haskey t k].

   For this we need several lemmas. *)

Lemma bsthaskey_haskey {X : Type} : forall t k,
  @bsthaskey X t k ->
  haskey t k.
Proof.
  intros t k Hh.
  induction Hh. apply haskeynd.
  apply haskeyl. assumption.
  apply haskeyr. assumption.
Qed.

Lemma maxkey_nd {X : Type} : forall k (d : X) l r,
  k <= maxkey (btsub (nd k d) l r).
Proof.
Admitted.

Lemma maxkey_l {X : Type} : forall (n : @node X) l r,
  maxkey l <= maxkey (btsub n l r).
Proof.
Admitted.

Lemma maxkey_r {X : Type} : forall (n : @node X) l r,
  maxkey r <= maxkey (btsub n l r).
Proof.
Admitted.

Lemma haskey_maxkey {X : Type} : forall t k,
  @haskey X t k ->
  k <= maxkey t.
Proof with eauto.
  intros.
  induction t;
    inversion H; subst.
  Case "haskeynd".
    apply maxkey_nd.
  Case "haskeyl".
    destruct t1. inversion H4.
    apply IHt1 in H4.
    eapply le_trans. eassumption. apply maxkey_l.
  Case "haskeyr".
    destruct t2. inversion H4.
    apply IHt2 in H4.
    eapply le_trans; eauto using maxkey_r.
Qed.

Lemma minkey_nd {X : Type} : forall k (d : X) l r,
  minkey (btsub (nd k d) l r) <= k.
Proof.
Admitted.

Lemma minkey_l {X : Type} : forall (n : @node X) l r,
  minkey (btsub n l r) <= minkey l.
Proof.
Admitted.

Lemma minkey_r {X : Type} : forall (n : @node X) l r,
  minkey (btsub n l r) <= minkey r.
Proof.
Admitted.

Lemma haskey_minkey {X : Type} : forall t k,
  @haskey X t k ->
  minkey t <= k.
Proof with eauto.
  intros.
  induction t;
    inversion H; subst.
  Case "haskeynd".
    apply minkey_nd.
  Case "haskeyl".
    destruct t1. inversion H4.
    apply IHt1 in H4.
    generalize @minkey_l; intros.
    eapply le_trans...
  Case "haskeyr".
    destruct t2. inversion H4.
    eauto using le_trans, minkey_r.
Qed.

Lemma bst_lr {X : Type} : forall n l r,
  @bst X (btsub n l r) ->
  bst l /\ bst r.
Proof.
  intros n l r Hs.
  split; inversion Hs; try constructor; assumption.
Qed.
Hint Resolve bst_lr.

Lemma haskey_bsthaskey {X : Type} : forall t k,
  @bst X t ->
  haskey t k ->
  bsthaskey t k.
Proof with eauto.
  intros t k' Hs Hh.
  induction t as [| [k d]]. inversion Hh. (* contradiction when t is nil *)
  inversion Hh; subst; clear Hh; auto;    (* auto takes care of trivial case *)
    assert (bst t1 /\ bst t2) as Hs2 by (apply bst_lr in Hs; assumption);
      destruct Hs2 as [Hsl Hsr]; intuition.
  (* bsthaskey t1/t2 follows by I.H. *)
  Case "haskeyl".
    destruct t1 as [| [lk ln] ll lr]. inversion H4.
    apply haskey_maxkey in H4.
    assert (maxkey (btsub (nd lk ln) ll lr) < k) by (inversion Hs; assumption).
    apply bsthaskeyl. omega.
    assumption.
  Case "haskeyr".
    destruct t2 as [| [rk rn] rl rr]. inversion H4.
    apply haskey_minkey in H4.
    assert (k < minkey (btsub (nd rk rn) rl rr)) by (inversion Hs; assumption).
    apply bsthaskeyr. omega.
    assumption.
Qed.

Theorem bsthaskey_correct {X : Type} : forall t k,
  @bst X t ->
  (bsthaskey t k <-> haskey t k).
Proof.
  intros. split.
  apply bsthaskey_haskey.
  apply haskey_bsthaskey; assumption.
Qed.


Inductive bstins {X : Type} : @bt X -> @node X -> @bt X -> Prop :=
| bstinsnil : forall k' d',
  bstins btnil (nd k' d') (btsub (nd k' d') btnil btnil)
| bstinsleft : forall k' d' k d l r l',
  k' < k ->
  bstins l (nd k' d') l' ->
  bstins (btsub (nd k d) l r) (nd k' d') (btsub (nd k d) l' r)
| bstinsright : forall k' d' k d l r r',
  k < k' ->
  bstins r (nd k' d') r' ->
  bstins (btsub (nd k d) l r) (nd k' d') (btsub (nd k d) l r')
.

Example test_bstins_left : bstins
(btsub (nd 5 0) btnil btnil)
(nd 3 0)
(btsub (nd 5 0) (btsub (nd 3 0) btnil btnil) btnil).
Proof.
  intros. apply bstinsleft. omega.
  apply bstinsnil.
Qed.

Example test_bstins_right : bstins
(btsub (nd 1 0) btnil btnil)
(nd 4 0)
(btsub (nd 1 0) btnil (btsub (nd 4 0) btnil btnil)).
Proof.
  intros. apply bstinsright. omega.
  apply bstinsnil.
Qed.

Lemma bstins_sub {X : Type} : forall t n t',
  @bstins X t n t' ->
  t' <> btnil.
Proof.
  intros.
  inversion H; subst;
    intro;
      try solve by inversion.
Qed.

Lemma bstins_maxkey {X : Type} : forall t k' d' t',
  t <> @btnil X ->
  @bstins X t (nd k' d') t' ->
  maxkey t' = max (maxkey t) k'.
Proof.
  intros. rename H0 into Hi.
  generalize dependent t'.
  generalize dependent k'.
  generalize dependent d'.
  induction t; intros. intuition.
  inversion Hi; subst.
  destruct t1 as [| ln ll lr];
    destruct t2 as [| rn rl rr].
  admit. admit. admit.
  set (btsub ln ll lr) as l in *.
  set (btsub rn rl rr) as r in *.
  rename H7 into Hli.
  destruct l'. inversion Hli.
  apply IHt1 in Hli.
  set (btsub n l'1 l'2) as l' in *.
  replace (maxkey (btsub (nd k d) l' r)) with
    (S (max (maxkey l') (maxkey r))).
  replace (maxkey (btsub (nd k d) l r)) with
    (S (max (maxkey l) (maxkey r))).
  remember (le_either (maxkey l) k') as m. destruct m.
  rewrite max_r in Hli; try assumption.
  clear Heqm.
  rewrite <- Hli.
  destruct l0 as [| k'pred]. rewrite Hli. admit.
  rewrite Hli.
  rewrite <- succ_max_distr.
  symmetry. rewrite max_comm. rewrite max_assoc.
  apply max_l in l0. rewrite l0.

                     (* STUCK *)
Admitted.

(* Lemma bstins_maxkey' {X : Type} : forall t k d l r k' d' t', *)
(*   t = btsub (nd k d) l r -> *)
(*   @bstins X t (nd k' d') t' -> *)
(*   k' < k -> *)
(*   maxkey t' = maxkey t. *)
(* Proof. *)
(*   intros. *)
(*   generalize dependent k.  *)
(*   generalize dependent d.  *)
(*   generalize dependent l. *)
(*   generalize dependent r. *)
(*   induction H0; *)
(*     intros. *)
(*   inversion H. *)
(*   inversion H1; subst; clear H1. *)


(*   inversion H0; subst. reflexivity.  *)
(*   simpl. *)
(*   (* intros. *) *)
(*   (* remember (btsub (nd k d) l r) as t. *) *)
(*   (* generalize dependent k'. *) *)
(*   (* generalize dependent d'. *) *)
(*   (* generalize dependent l'. *) *)
(*   (* generalize dependent H. *) *)
(*   (* generalize dependent l. *) *)
(*   (* generalize dependent l. *) *)
(*   intros t. *)
(*   induction t; intros. inversion H. *)
(*   inversion H; subst. *)
(*   inversion H0; subst. auto. *)
(*   eapply IHt1 in H7. *)
(*   eapply IHt1; eauto.  *)
(*   eapply IHt1 in H0. eassumption. e *)
(*   eapply IHt'1 in H0. *)
(* admit. *)
(*   destruct l' as [| ln ll lr]. inversion H8. *)
(*   apply IHt1 with (l := t1) in H8. *)

(*   (* STUCK *) *)
(* Admitted. *)

Lemma bstins_minkey {X : Type} : forall t k' d' t',
  t <> @btnil X ->
  @bstins X t (nd k' d') t' ->
  minkey t' = min (minkey t) k'.
Proof.
Admitted.

Theorem bstins_bst {X : Type} : forall t n t',
  @bst X t ->
  bstins t n t' ->
  bst t'.
Proof with auto.
  intros t n t' Hs Hi.
  generalize dependent Hs.
  induction Hi; intros;
    try apply bstleaf;
      assert (bst l /\ bst r) as [Hsl Hsr]
        by (split; inversion Hs; try constructor; assumption).

  assert (bst l') as Hsl' by auto.
  destruct l' as [| [l'k l'd] l'l l'r]. inversion Hi.
  set (btsub (nd l'k l'd) l'l l'r) as l' in *.
  assert (maxkey l' < k) as Hkl'.
    destruct l as [| [lk ld] ll lr].
    inversion Hi; subst l'; subst. assumption.
    set (btsub (nd lk ld) ll lr) as l in *.
    assert (maxkey l < k) by (inversion Hs; assumption).
    apply bstins_maxkey in Hi; try (intro Hcontra; inversion Hcontra).
    rewrite Hi. destruct (le_either (maxkey l) k').
    rewrite max_r; assumption.
    rewrite max_l; assumption.
  destruct r as [| [rk rd] rl rr].
    eapply bsthil; subst l'; auto.
    set (btsub (nd rk rd) rl rr) as r.
    assert (k < minkey r) by (inversion Hs; assumption).
    eapply bstbal; subst l' r; auto.

  assert (bst r') by auto.
  destruct r' as [| r'n r'l r'r]. inversion Hi.
  assert (k < minkey (btsub r'n r'l r'r)).
    destruct r. inversion Hi...
    assert (k < minkey (btsub n r1 r2)) by (inversion Hs; assumption).
    apply bstins_minkey in Hi; try (intro Hcontra; inversion Hcontra).
    rewrite Hi.
    destruct (le_either (minkey (btsub n r1 r2)) k').
      rewrite min_l...
      rewrite min_r...
  destruct r'n.
  destruct l.
    eapply bsthir...
    inversion Hs; eapply bstbal; eauto.
Qed.

Theorem bstins_bsthaskey {X : Type} : forall t k d t',
  @bstins X t (nd k d) t' ->
  bsthaskey t' k.
Proof with auto.
  intros t k d t' Hi.
  remember (nd k d) as n.
  induction Hi;
    inversion Heqn; subst;
      auto.
Qed.

Lemma bstins_haskey {X : Type} : forall t k (d : X) t',
  bstins t (nd k d) t' ->
  haskey t' k.
Proof with eauto.
  intros.
  generalize dependent t.
  induction t';
    intros;
      inversion H; subst.
  apply haskeynd.
  apply haskeyl. eapply IHt'1...
  apply haskeyr. eapply IHt'2...
Qed.

Theorem bstins_correct {X : Type} : forall t k (d : X) t' k',
  bst t ->
  bstins t (nd k d) t' ->
  (haskey t k' \/ k = k' <-> haskey t' k') /\ bst t'.
Proof with auto.
  intros t k d t' k' Hs Hi. split;
    try (eapply bstins_bst; eauto).
  unfold iff. split;
    intro H.
  destruct H.
  Case "->".
    apply haskey_bsthaskey in H; try assumption.
    generalize dependent t'.
    induction H;
      intros;
        apply bst_lr in Hs; destruct Hs as [Hsl Hsr].
    SCase "haskeynd".
      admit.
    SCase "haskeyl".
      destruct t' as [| [t'k t'd]]. inversion Hi. (* t' cannot be nil *)
      apply haskeyl.
      intuition.                  (* clean up I.H. *)
      inversion Hi; subst.
      SSCase "bstinsleft". assert (bst t'1) by eauto using bstins_bst...
      SSCase "bstinsright". eapply bsthaskey_haskey...
    SCase "haskeyr".
       (* symmetric to haskeyl, so I use more automation *)
       inversion Hi; subst;
         eauto using bsthaskey_haskey, bstins_bst.
    SCase "k = k".
      subst. apply bstins_haskey in Hi...
  Case "<-".
    assert (bst t') as Hs' by (eapply bstins_bst; eauto).
    admit.
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
| btrebalbal : forall t,        (*   case balanced:    p (-1|0|1) *)
  ndbal t ->                    (*                    / \         *)
  btrebal t t                   (*                   l   r        *)
| btreballl : forall n l r t', (*    case LL:          g (2)         p (-1|0) *)
  btleanl 2 (btsub n l r) -> (*                       /             / \       *)
  btleanl 1 l \/ btleanl 0 l -> (*                   p (1|0)  -->  l   g      *)
  btrotr (btsub n l r) t' -> (*                     /                         *)
  btrebal (btsub n l r) t' (*                       l                         *)
| btrebalrr : forall n l r t', (*    case RR:          g (-2)        p (1|0)  *)
  btleanr 2 (btsub n l r) -> (*                         \           / \       *)
  btleanr 1 r \/ btleanr 0 r -> (*                (-1|0) p    -->  g   r      *)
  btrotl (btsub n l r) t' -> (*                           \                   *)
  btrebal (btsub n l r) t' (*                              r                  *)
| btreballr : forall n l r l' t', (* case LR: *)
  btleanl 2 (btsub n l r) -> (*        g (2)           g (2)         r (-1|0) *)
  btleanr 1 l -> (*                   /               /             / \       *)
  btrotl l l' -> (*                  p (-1)   -->    r (1|0)  -->  p   g      *)
  btrotr (btsub n l' r) t' -> (*      \             /                         *)
  btrebal (btsub n l r) t' (*          r           p                          *)
| btrebalrl : forall n l r r' t', (* case RL: *)
  btleanl 2 (btsub n l r) -> (*        g (-2)          g (-2)        l (1|0)  *)
  btleanl 1 r -> (*                     \               \           / \       *)
  btrotr r r' -> (*                  (1) p    --> (-1|0) l    -->  g   p      *)
  btrotl (btsub n l r') t' -> (*        /                 \                   *)
  btrebal (btsub n l r) t' (*          l                   p                  *)
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
  inversion H; subst.
  (* clear H3 lk0 ld0 ll lr. *)
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
Proof with auto.
  intros g p' Hs Hr.
  destruct p';
    inversion Hr; subst; clear Hr.
  rename p'1 into l, n into pn.
  destruct pn as [pk pd].
  destruct gn as [gk gd].
  set (btsub (nd pk pd) l r) as p in *.
  set (btsub (nd gk gd) r u) as g' in *.
  set (btsub (nd pk pd) l g') as p' in *.
  assert (bst p /\ bst u) as [Hsp Hsu] by (apply bst_lr in Hs; assumption).
  assert (maxkey p < gk) as Hkp by (inversion Hs; assumption).
  assert (u <> btnil -> gk < minkey u) as Hku
    by (intro; destruct u; inversion Hs; intuition).
  assert (bst l) as Hsl by (inversion Hsp; try constructor; assumption).

  destruct r as [| [rk rd] rl rr].
  Case "r = btnil".
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]. apply bstleaf.
      apply bsthir; auto. apply Hku. intro H. inversion H.
    assert (pk < minkey g')
      by (subst p g'; rewrite bst_maxkey_nd in Hkp; try rewrite bst_minkey_nd;
        assumption).
    destruct l as [| [lk ld] ll lr].
    SCase "l = btnil".
      eapply bsthir...
    SCase "l = btsub".
      set (btsub (nd lk ld) ll lr) as l.
      assert (maxkey l < pk) by (inversion Hsp; assumption).
      eapply bstbal...
  Case "r = btsub".
  set (btsub (nd rk rd) rl rr) as r.
    assert (bst r) as Hsr by (inversion Hsp; assumption).
    assert (maxkey r < gk) as Hkr
      by (subst p; rewrite bst_maxkey_r in Hkp; auto; intro H'; inversion H').
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]. apply bsthil...
      apply bstbal; auto. apply Hku. intro H'. inversion H'.
    assert (pk < minkey g').
      assert (pk < minkey r) as Hkr' by (inversion Hsp; assumption).
      subst g'. rewrite bst_minkey_l...
      intro H'; inversion H'.
    destruct l as [| [lk ld] ll lr].
    SCase "l = btnil".
      eapply bsthir...
    SCase "l = btsub".
      set (btsub (nd lk ld) ll lr) as l.
      assert (maxkey l < pk) by (inversion Hsp; intuition).
      eapply bstbal...
Qed.

Lemma btrotl_bst {X : Type} : forall t t',
  @bst X t ->
  btrotl t t' ->
  bst t'.
Proof with auto.
  (* Analogous to [btrotl_bst], but with more automation. *)
  intros g p' Hs Hr.
  destruct p';
    inversion Hr; subst; clear Hr.
  rename p'2 into r, n into pn.
  destruct pn as [pk pd].
  destruct gn as [gk gd].
  set (btsub (nd pk pd) l r) as p in *.
  set (btsub (nd gk gd) u l) as g' in *.
  set (btsub (nd pk pd) g' r) as p' in *.
  assert (bst u /\ bst p) as [Hsu Hsp] by eauto using bst_lr.
  assert (gk < minkey p) as Hkp by (inversion Hs; assumption).
  assert (u <> btnil -> maxkey u < gk) as Hku
    by (intro; destruct u; inversion Hs; intuition).

  destruct l as [| [lk ld] ll lr].
  Case "l = btnil".
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]; constructor...
      apply Hku; intro H'; inversion H'.
    assert (maxkey g' < pk)
      by (subst p g'; rewrite bst_minkey_nd in Hkp; try rewrite bst_maxkey_nd;
        assumption).
    destruct r as [| [rk rd] rl rr]. apply bsthil...
    inversion Hsp; apply bstbal...
  Case "l = btsub".
    set (btsub (nd lk ld) ll lr) as l.
    assert (bst l) as Hsl by (inversion Hsp; assumption).
    assert (gk < minkey l) as Hkl
      by (subst p; rewrite bst_minkey_l in Hkp; auto; intro H'; inversion H').
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]; constructor...
      apply Hku; intro H'; inversion H'.
    assert (maxkey g' < pk).
      inversion Hsp;
        subst g'; rewrite bst_maxkey_r;
          try (intro H'; inversion H')...
    destruct r as [| [rk rd] rl rr]. apply bsthil...
    inversion Hsp; apply bstbal...
Qed.

Lemma btrotl_bstmax {X : Type} : forall t t',
  @btrotl X t t' ->
  maxkey t = maxkey t'.
Proof.
Admitted.

Lemma btrotr_bstmin {X : Type} : forall t t',
  @btrotr X t t' ->
  minkey t = minkey t'.
Proof.
Admitted.

Theorem btrebal_bst {X : Type} : forall (t t' : @bt X),
  bst t ->
  btrebal t t' ->
  bst t'.
Proof.
  intros t t' Hs Hb.
  inversion Hb; subst; clear Hb;
    try assumption;             (* trivial case - no rotation *)
    (* cases with single rotation follow directly from the lemma *)
      try (apply btrotr_bst in H1; assumption);
        try (apply btrotl_bst in H1; assumption);
         (* for the remaining cases, we need the lemma that children are bst *)
          assert (bst l /\ bst r) as [Hsl Hsr]
            by (apply bst_lr in Hs; assumption);
            destruct n as [k d].
  Case "LR".
    destruct l' as [| [l'k l'd] l'l l'r]. inversion H1.
    set (btsub (nd l'k l'd) l'l l'r) as l' in *.
    assert (maxkey l' < k).
      destruct l. inversion H1.
      apply btrotl_bstmax in H1. rewrite <- H1.
      inversion Hs; assumption.
    apply btrotr_bst in H2. assumption.
    apply btrotl_bst in H1; try assumption.
    destruct r as [| [rk rd] rl rr].
      apply bsthil; assumption.
      inversion Hs;
        apply bstbal; assumption.
  Case "RL".
    destruct r' as [| [r'k r'd] r'l r'r]. inversion H1.
    assert (k < minkey (btsub (nd r'k r'd) r'l r'r)).
      destruct r. inversion H1.
      apply btrotr_bstmin in H1. rewrite <- H1.
      inversion Hs; assumption.
    apply btrotl_bst in H2. assumption.
    apply btrotr_bst in H1; try assumption.
    destruct l as [| [lk ld] ll lr].
      apply bsthir; assumption.
      inversion Hs;
        apply bstbal; assumption.
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
    intros. inversion H; auto.

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
(*   inversion H0; subst. *)

(* admit. admit. admit. *)
(*   admit. admit. *)
  (* induction H; *)
  (*   intros. *)

(* end *)
Admitted.
