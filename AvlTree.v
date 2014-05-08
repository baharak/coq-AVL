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
        | btnil, btsub _ _ _ => min (minkey r) k
        | btsub _ _ _, btnil => min (minkey l) k
        | _, _ => min (min (minkey l) (minkey r)) k
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

(* Since we are going to work with min/max a lot, we better add some common
   lemmas about the min/max from the Coq Standard library - GenericMinMax:
   Lemma le_max_l : forall n m, n <= max n m.
   Lemma le_max_r : forall n m, m <= max n m. *)
(* Hint Resolve le_min_l. *)
(* Hint Resolve le_min_r. *)
(* Hint Resolve le_max_l. *)
(* Hint Resolve le_max_r. *)

Inductive haskey {X : Type} : @bt X -> nat -> Prop :=
| haskeynd : forall k d l r,
  haskey (btsub (nd k d) l r) k
| haskeyl : forall k n l r,
  haskey l k ->
  haskey (btsub n l r) k
| haskeyr : forall k n l r,
  haskey r k ->
  haskey (btsub n l r) k
.
Hint Constructors haskey.

Fixpoint haskeyb {X: Type} (t : @bt X) (k' : nat) : bool :=
  match t with
    | btnil => false
    | btsub (nd k d) l r => orb (beq_nat k k') (orb
      (haskeyb l k')
      (haskeyb r k'))
  end.

(* We prove the correctness of [haskey_correct] by showing it's equivalent
   to [Fixpoint] [haskeyb] *)

Theorem haskey_correct {X : Type} : forall (t : @bt X) k,
  haskey t k <-> haskeyb t k = true.
Proof.
  intros. split; intro.
  Case "->".
    induction t as [| [k' d']]. inversion H.
    inversion H; subst.
    simpl. rewrite <- beq_nat_refl. apply orb_true_iff. left. reflexivity.
    apply orb_true_iff. right. apply orb_true_iff. left. apply IHt1. assumption.
    apply orb_true_iff. right. apply orb_true_iff. right. auto.
  Case "<-".
    induction t as [| [k' d']];
      simpl in H.
    inversion H.
    apply orb_true_iff in H. destruct H.
    apply beq_nat_true_iff in H. subst. constructor.
    apply orb_true_iff in H. destruct H; auto.
Qed.


(* In-order traversal of the tree, i.e.:
   1) visit left subtree
   2) visit current node
   3) visit right subtree *)

Fixpoint btinorder {X : Type} (t : @bt X) : list nat :=
  match t with
    | btnil => []
    | btsub (nd k d) l r => btinorder l ++ k :: btinorder r
  end.

(* Some lemmas we need from Logic.v, proved using more automation. *)

Hint Constructors appears_in.

Lemma appears_in_app : forall (xs ys : list nat) (x : nat),
  appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros.
  induction xs; simpl; intros.
  right. assumption.
  inversion H; subst. auto.
  remember (IHxs H1). destruct o; auto.
Qed.

Lemma app_appears_in : forall (xs ys : list nat) (x : nat),
  appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  generalize dependent ys.
  induction xs; intros;
    simpl.
  inversion H. inversion H0. assumption.
  inversion H. inversion H0; subst; auto.
  constructor. auto.
Qed.

Lemma appears_in_app' : forall (xs ys : list nat) (x h : nat),
  appears_in x (xs ++ h :: ys) ->
  x = h \/ (appears_in x xs \/ appears_in x ys).
Proof.
  intros.
  induction xs; simpl in H.
  inversion H; subst;
    try (left; reflexivity);
      right.
  right. assumption.
  inversion H; subst.
  right. left. apply ai_here.
  remember (IHxs H1).
  destruct o. left. assumption.
  destruct o; right.
Admitted.

Theorem btinorder_correct {X : Type} : forall t k,
  appears_in k (btinorder t) <-> @haskey X t k.
Proof with auto.
  intros. split; intro.
  Case "->".
    induction t;
      simpl in H.
    SCase "btnil". inversion H.
    SCase "btsub".
      destruct n as [k' d'].
      (* apply appears_in_app' in H. *)
      (* intuition. subst... *)
      apply appears_in_app in H. destruct H...
      inversion H...
  Case "<-".
    induction t; intros.
    SCase "btnil". inversion H.
    SCase "btsub".
      destruct n as [k' d']; simpl.
      apply app_appears_in.
      inversion H...
Qed.


(* Binary Search Tree Search - we define it on any binary tree *)
(* (later on, we also define an inductive proposition [bst] which
   represents the Binary Search Tree property) *)

Inductive bstsearch {X : Type} : @bt X -> nat -> Prop :=
| bstsearchnd : forall k d l r,
  bstsearch (btsub (nd k d) l r) k
| bstsearchl : forall k' k d l r,
  k' < k ->
  bstsearch l k' ->
  bstsearch (btsub (nd k d) l r) k'
| bstsearchr : forall k' k d l r,
  k < k' ->
  bstsearch r k' ->
  bstsearch (btsub (nd k d) l r) k'
.
Hint Constructors bstsearch.

(* Next, we are going to prove its correctness:
   [bstsearch t k] holds if and only if tree contains the key, [haskey t k].

   For this we need several lemmas. *)

Lemma bstsearch_haskey {X : Type} : forall t k,
  @bstsearch X t k ->
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
  intros.
  destruct l;
    destruct r;
      try (simpl; reflexivity);
        destruct n;
          try (destruct r1; destruct r2);
            try (destruct l1; destruct l2);
              simpl; apply le_max_l.
Qed.

Lemma maxkey_l {X : Type} : forall (n : @node X) ln ll lr r,
  maxkey (btsub ln ll lr) <= maxkey (btsub n (btsub ln ll lr) r).
Proof with auto.
  intros. destruct n. destruct ln as [lk ld].
  destruct r as [| [rk rd]]. apply le_max_r.
  assert (forall n m o, m <= max n (max m o))
    by (intros; rewrite max_comm; rewrite <- max_assoc; apply le_max_l).
  destruct ll as [| [llk lld]];
    destruct lr as [| [lrk lrd]];
      simpl...
Qed.

Lemma maxkey_r {X : Type} : forall (n : @node X) l rn rl rr,
  maxkey (btsub rn rl rr) <= maxkey (btsub n l (btsub rn rl rr)).
Proof with auto.
  intros. destruct n. destruct rn as [rk rd].
  destruct l as [| [lk ld]]. apply le_max_r.
  assert (forall n m o, o <= max n (max m o))
    by (intros; rewrite max_assoc; apply le_max_r).
  destruct rl as [| [rlk rld]];
    destruct rr as [| [rrk rrd]];
      simpl...
Qed.

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
    destruct t2. solve by inversion.
    intuition.                  (* apply I.H. forward *)
    eapply le_trans; eauto using maxkey_r.
Qed.

Lemma minkey_nd {X : Type} : forall k (d : X) l r,
  minkey (btsub (nd k d) l r) <= k.
Proof.
  intros.
  destruct l;
    destruct r;
      try (simpl; reflexivity);
        destruct n;
          try (destruct r1; destruct r2);
            try (destruct l1; destruct l2);
              simpl; apply le_min_r.
Qed.

Lemma minkey_l {X : Type} : forall (n : @node X) ln ll lr r,
  minkey (btsub n (btsub ln ll lr) r) <= minkey (btsub ln ll lr).
Proof with auto.
  intros. destruct n. destruct ln as [lk ld].
  destruct r as [| [rk rd]]. apply le_min_l.
  assert (forall n m o, min (min n m) o <= n)
    by (intros; rewrite <- min_assoc; apply le_min_l).
  assert (forall n m o p, min (min (min n m) o) p <= min n m)
    by (intros; rewrite <- min_assoc; apply le_min_l).
  destruct ll as [| [llk lld]];
    destruct lr as [| [lrk lrd]];
      simpl...
Qed.

Lemma minkey_r {X : Type} : forall (n : @node X) l rn rl rr,
  minkey (btsub n l (btsub rn rl rr)) <= minkey (btsub rn rl rr).
Proof with auto.
  intros. destruct n. destruct rn as [rk rd].
  destruct l as [| [lk ld]]. apply le_min_l.
  assert (forall n m o, min (min n m) o <= m)
    by (intros; rewrite min_comm; rewrite min_assoc; apply le_min_r).
  destruct rl as [| [rlk rld]];
    destruct rr as [| [rrk rrd]];
      simpl...
Qed.

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

(* Binary Search Tree - we permit only unique keys *)

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

Lemma bst_lr {X : Type} : forall n l r,
  @bst X (btsub n l r) ->
  bst l /\ bst r.
Proof.
  intros n l r Hs.
  split; inversion Hs; try constructor; assumption.
Qed.
Hint Resolve bst_lr.

Lemma haskey_bstsearch {X : Type} : forall t k,
  @bst X t ->
  haskey t k ->
  bstsearch t k.
Proof with eauto.
  intros t k' Hs Hh.
  induction t as [| [k d]]. inversion Hh. (* contradiction when t is nil *)
  inversion Hh; subst; clear Hh; auto;    (* auto takes care of trivial case *)
    assert (bst t1 /\ bst t2) as Hs2 by (apply bst_lr in Hs; assumption);
      destruct Hs2 as [Hsl Hsr]; intuition.
  (* bstsearch t1/t2 follows by I.H. *)
  Case "haskeyl".
    destruct t1 as [| [lk ln] ll lr]. inversion H0.
    apply haskey_maxkey in H3.
    assert (maxkey (btsub (nd lk ln) ll lr) < k) by (inversion Hs; assumption).
    apply bstsearchl. omega.
    assumption.
  Case "haskeyr".
    destruct t2 as [| [rk rn] rl rr]. solve by inversion.
    apply haskey_minkey in H3.
    assert (k < minkey (btsub (nd rk rn) rl rr)) by (inversion Hs; assumption).
    apply bstsearchr. omega.
    assumption.
Qed.

(* Finally, we can prove the correctness of [bstsearch] using lemmas:
   - [bstsearch_haskey] - for forward direction
   - [haskey_bstsearch] - for backward direction
   given the precondition that the BST property holds on the tree. *)

Theorem bstsearch_correct {X : Type} : forall t k,
  @bst X t ->
  (bstsearch t k <-> haskey t k).
Proof.
  intros. split.
  apply bstsearch_haskey.
  apply haskey_bstsearch; assumption.
Qed.


(* Another interesting theorem:
   If a tree is a BST, then its inorder key list is sorted. *)

(* Fixpoint listmin (l : list nat) := *)
(* | match l with := *)

Inductive unsorted : list nat -> Prop :=
| unsortedcons : forall x h t,
  appears_in x t ->
  x <= h ->
  unsorted (h :: t)
.
Definition sorted (l : list nat) := ~ unsorted l.

Hint Unfold sorted.
Hint Constructors unsorted.

Theorem bst_inorder_sorted {X : Type} : forall t,
  @bst X t -> sorted (btinorder t).
Proof with eauto.
  intros t Hs. intro H.
  induction t as [| [k d]];
    simpl in H.
  inversion H.
  admit.
Qed.

Example test_sorted_145 : sorted [1,4,5].
Proof.
  intro. inversion H. inversion H2. omega. inversion H5. omega. inversion H8.
Qed.
(* Example test_sorted_153 : ~ sorted [1,5,3]. *)

Inductive bstins {X : Type} : @bt X -> @node X -> @bt X -> Prop :=
| bstinsnil : forall k' d',
  bstins btnil (nd k' d') (btsub (nd k' d') btnil btnil)
| bstinsnd : forall k d l r,
  bstins (btsub (nd k d) l r) (nd k d) (btsub (nd k d) l r)
| bstinsl : forall k' d' k d l r l',
  k' < k ->
  bstins l (nd k' d') l' ->
  bstins (btsub (nd k d) l r) (nd k' d') (btsub (nd k d) l' r)
| bstinsr : forall k' d' k d l r r',
  k < k' ->
  bstins r (nd k' d') r' ->
  bstins (btsub (nd k d) l r) (nd k' d') (btsub (nd k d) l r')
.

Example test_bstins_left : bstins
(btsub (nd 5 0) btnil btnil)
(nd 3 0)
(btsub (nd 5 0) (btsub (nd 3 0) btnil btnil) btnil).
Proof.
  intros. apply bstinsl. omega.
  apply bstinsnil.
Qed.

Example test_bstins_right : bstins
(btsub (nd 1 0) btnil btnil)
(nd 4 0)
(btsub (nd 1 0) btnil (btsub (nd 4 0) btnil btnil)).
Proof.
  intros. apply bstinsr. omega.
  apply bstinsnil.
Qed.

Theorem bstins_deterministic {X : Type} : forall t (n : @node X) t' t'',
  bstins t n t' ->
  bstins t n t'' ->
  t' = t''.
Proof with auto.
  intros t n t' t'' Hi' Hi''.
  generalize dependent t''.
  induction Hi'; intros;
    inversion Hi''; subst;
      try omega. (* cases of insertion in different subtrees are contras *)
  Case "bstinsnil". reflexivity.
  Case "bstinsnd". reflexivity.
  Case "bstinsl". apply IHHi' in H8. subst. reflexivity.
  Case "bstinsr". erewrite IHHi'... (* using more automation :) *)
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
  inversion Hi; subst. admit.
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
  assumption.

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

Theorem bstins_bstsearch {X : Type} : forall t k d t',
  @bstins X t (nd k d) t' ->
  bstsearch t' k.
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
  apply haskeynd.
  apply haskeyl. eapply IHt'1...
  apply haskeyr. eapply IHt'2...
Qed.

Theorem bstins_correct {X : Type} : forall t k (d : X) t' k',
  bst t ->
  bstins t (nd k d) t' ->
  (bstsearch t k' \/ k = k' <-> bstsearch t' k') /\ bst t'.
Proof with auto.
  intros t k d t' k' Hs Hi. split;
    try (eapply bstins_bst; eauto).
  unfold iff. split;
    intro H.
  Case "->".
    destruct H.
    generalize dependent t'.
    induction H;
      intros;
        apply bst_lr in Hs; destruct Hs as [Hsl Hsr].
    SCase "haskeynd".
      inversion Hi; subst;
        apply bstsearchnd... (* after insertion, the node remains untouched *)
    SCase "haskeyl".
      destruct t' as [| [t'k t'd]]. inversion Hi. (* t' cannot be nil *)
      intuition.                  (* clean up I.H. *)
      inversion Hi; subst.
      apply bstsearchl; assumption.
      SSCase "bstinsl".
        assert (bst t'1) by (apply bstins_bst in H13; assumption).
        apply H1 in H13. apply bstsearchl; assumption.
      SSCase "bstinsr". apply bstsearchl; assumption.
    SCase "haskeyr".
       (* symmetric to haskeyl, so I use more automation *)
       inversion Hi...
       subst...
    SCase "k = k".
      assert (bst t') by eauto using bstins_bst.
      subst. apply bstins_bstsearch in Hi. assumption.
  Case "<-".
    clear Hs.
    generalize dependent t.
    induction H;
      intros.
    SCase "haskeynd".
      inversion Hi; subst;
        try (right; reflexivity); (* insertion into empty tree implies k = k0 *)
          left; apply bstsearchnd... (* otherwise, the node remains untouched *)
    SCase "haskeyl".
      inversion Hi; subst.
      SSCase "bstinsnil". inversion H0.
      SSCase "bstinsnd". auto.
      SSCase "bstinsl".
        apply IHbstsearch in H9. destruct H9.
        left. apply bstsearchl; assumption.
        right. assumption.
      SSCase "bstinsr".
        left. apply bstsearchl; assumption.
    SCase "haskeyr".
      (* symmetric to haskeyl, so I use more automation *)
      inversion Hi; subst;
        try apply IHbstsearch in H9;
          intuition.
Qed.

(* For BST deletion, we need to find an in-order predecessor/successor [p]/[s]
   that is a descendent of the left/right subtree of [n], i.e.:
       n              n
      / \            / \
     l                  r
    / \      and       /
       .              .
        .            .
         \          /
          p        s

   These are equivalent to the rightmost/leftmost node in left/right subtree,
   so we first define partial functions [btlmost] and [btrmost]. *)

Inductive btlmostnd {X : Type} : @bt X -> @node X -> Prop :=
  | btlmostndleaf : forall n r,
    btlmostnd (btsub n btnil r) n
  | btlmostndsub : forall n l r n',
    btlmostnd l n' ->
    btlmostnd (btsub n l r) n'
.
Hint Constructors btlmostnd.

Inductive btrmostnd {X : Type} : @bt X -> @node X -> Prop :=
  | btrmostndleaf : forall n l,
    btrmostnd (btsub n l btnil) n
  | btrmostndsub : forall n l r n',
    btrmostnd r n' ->
    btrmostnd (btsub n l r) n'
.
Hint Constructors btrmostnd.

(* We can now define a BST deletion operation.

   Note that it is not even a (partial) function because we have the
   choice of choosing whether to replace the deleted node with
   in-order predecessor or sucessor of a node with 2 children.
   Actually, good implementations choose between the two choices to
   keep the tree as balanced as possible.  To permit this choice, we
   *must* use [Inductive] (even if bt(l/r)mostnd were [Fixpoint]). *)

Inductive bstdel {X : Type} : @bt X -> nat -> @bt X -> Prop :=
| bstdelnone : forall k,
(* Case n is leaf - nothing to delete:                  -->          *)
  bstdel btnil k btnil
| bstdelleaf : forall k d,
(* Case key n = k' and n is leaf:                 n     -->          *)
  bstdel (btsub (nd k d) btnil btnil) k btnil
| bstdelndl : forall k d ln ll lr l' r pk pd, (*  n             p    *)
(* Case key n = k' and n has left child:         / \           / \   *)
(*                                              l       -->   l'     *)
(*                                               \             \     *)
(*                                                .             .    *)
(*                                                 .             .   *)
  btrmostnd (btsub ln ll lr) (nd pk pd) -> (*       \                *)
  bstdel (btsub ln ll lr) pk l' -> (*                p               *)
  bstdel (btsub (nd k d) (btsub ln ll lr) r) k (btsub (nd pk pd) l' r)
| bstdelndr : forall k d l rn rl rr r' sk sd, (*  n             s    *)
(* Case key n = k' and n has right child:        / \           / \   *)
(*                                                  r   -->       r' *)
(*                                                 /             /   *)
(*                                                .             .    *)
(*                                               .             .     *)
  btlmostnd (btsub rn rl rr) (nd sk sd) -> (*   /                    *)
  bstdel (btsub rn rl rr) sk r' -> (*          s                     *)
  bstdel (btsub (nd k d) l (btsub rn rl rr)) k (btsub (nd sk sd) l r')
| bstdell : forall k' k d ln ll lr r l', (*       n             n    *)
(* Case key n > k':                              / \    -->    / \   *)
  k' < k -> (*                                  l             l'     *)
  bstdel (btsub ln ll lr) k' l' ->
  bstdel (btsub (nd k d) (btsub ln ll lr) r) k (btsub (nd k d) l' r)
| bstdelr : forall k' k d rn rl rr l r', (*       n             n    *)
(* Case key n < k':                              / \    -->    / \   *)
  k < k' -> (*                                      r             r' *)
  bstdel (btsub rn rl rr) k' r' ->
  bstdel (btsub (nd k d) l (btsub rn rl rr)) k (btsub (nd k d) l r')
.
Hint Constructors bstdel.

Theorem bstdel_nondeterministic {X : Type} : forall x : X,
  exists (t : @bt X) k t' t'',
    bstdel t k t' /\
    bstdel t k t'' /\
    t <> t''.
Proof.
  intro.                  (* contents of node data doesn't matter *)
  set (btsub (nd 2 x)     (*          2   *)
    (btsub (nd 1 x) btnil btnil) (*  / \  *)
    (btsub (nd 3 x) btnil btnil) (* 1   3 *)
  ) as t.
  set 2 as k.               (* now if we delete 2, we can get both: *)
  set (btsub (nd 1 x)       (*        1   *)
    btnil                   (*         \  *)
    (btsub (nd 3 x) btnil btnil) (*     3 *)
  ) as t'.                       (* and *)
  set (btsub (nd 3 x)            (*   3   *)
    (btsub (nd 1 x) btnil btnil) (*  /    *)
    btnil                        (* 1     *)
  ) as t''.
  assert (bstdel t k t') as Ht' by (subst t k t'; auto).
  assert (bstdel t k t'') as Ht'' by (subst t k t''; auto).
  exists t. exists k. exists t'. exists t''.
  split. assumption.
  split. assumption.
  intro Hcontra. inversion Hcontra.
Qed.

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
  intros.
  generalize @minkey_nd; intros.
 inversion H; subst. auto.
 set (btsub (nd rk rd) rl rr) as r in *.
 set (btsub (nd k d) btnil r) as t in *.
 assert (minkey r <= rk) by eauto.
 assert (minkey t <= k) by eauto.
 assert (k < rk) by omega.
 assert (minkey t < minkey r) by omega.
 (* STUCK *)
Admitted.

Lemma bst_maxkey_r {X : Type} : forall n l rn rl rr,
  @bst X (btsub n l (btsub rn rl rr)) ->
  maxkey (btsub n l (btsub rn rl rr)) = maxkey (btsub rn rl rr).
Proof.
  (* STUCK *)
Admitted.

Lemma bst_minkey_l {X : Type} : forall k d ln ll lr r,
  @bst X (btsub (nd k d) (btsub ln ll lr) r) ->
  minkey (btsub (nd k d) (btsub ln ll lr) r) = minkey (btsub ln ll lr).
Proof.
Admitted.

Lemma bst_btrmostnd_maxkey {X : Type} : forall n l r k d,
  @bst X (btsub n l r) ->
  btrmostnd (btsub n l r) (nd k d) ->
  k = maxkey (btsub n l r).
Proof.
  intros n l r k d Hs Hm.
  induction (btsub n l r) as [| [k' d']]. inversion Hm.
  inversion Hm; subst.
  Case "btrmostndleaf".
    rewrite bst_maxkey_nd. reflexivity. assumption.
  Case "btrmostndsub".
    assert (bst b2) by (inversion Hs; auto).
    intuition.                  (* use I.H. *)
    destruct b2. inversion H3.
    rewrite bst_maxkey_r; assumption.
Qed.

Lemma bst_btlmostnd_minkey {X : Type} : forall n l r k d,
  @bst X (btsub n l r) ->
  btlmostnd (btsub n l r) (nd k d) ->
  k = minkey (btsub n l r).
Proof.
  intros n l r k d Hs Hm.
  induction (btsub n l r) as [| [k' d']]. inversion Hm.
  inversion Hm; subst.
  Case "btlmostndleaf".
    rewrite bst_minkey_nd. reflexivity. assumption.
  Case "btlmostndsub".
    assert (bst b1) by (inversion Hs; auto).
    intuition.                  (* use I.H. *)
    destruct b1. inversion H3.
    rewrite bst_minkey_l; assumption.
Qed.

Lemma btsub_not_nil {X : Type} : forall n l r,
  @btsub X n l r <> btnil.
Proof.
  intros. intro H. inversion H.
Qed.
Hint Resolve btsub_not_nil.

Lemma maxkey_le_l_le {X : Type} : forall k d l r k' (d' : X) l',
  k <= k' ->
  l = btnil \/ maxkey l <= maxkey l' ->
  maxkey (btsub (nd k d) l r) <= maxkey (btsub (nd k' d') l' r).
Proof with eauto.
Admitted.

Lemma maxkey_le_nd_le {X : Type} : forall k (d : X) l r k' (d' : X) l' r',
  k <= k' ->
  l = btnil \/ maxkey l <= maxkey l' ->
  r = btnil \/ maxkey r <= maxkey r' ->
  maxkey (btsub (nd k d) l r) <= maxkey (btsub (nd k' d') l' r').
Proof with eauto.
Admitted.

Lemma minkey_le_nd_le {X : Type} : forall k (d : X) l r k' (d' : X) l' r',
  k' <= k ->
  l = btnil \/ minkey l' <= minkey l ->
  r = btnil \/ minkey r' <= minkey r ->
  minkey (btsub (nd k' d') l' r') <= minkey (btsub (nd k d) l r).
Proof with eauto.
Admitted.

(* Lemma maxkey_le_l *)

Lemma bst_maxkey_lt {X : Type} : forall k d ln ll lr r,
  @bst X (btsub (nd k d) (btsub ln ll lr) r) ->
  maxkey (btsub ln ll lr) < k.
Proof.
  intros.
  inversion H; subst.
  (* apply maxkey_l *)
admit. admit.
Qed.
Hint Resolve bst_maxkey_lt.

Lemma bst_l {X : Type} : forall n l r,
  @bst X (btsub n l r) ->
  bst l.
Proof. apply bst_lr.
Qed.
Lemma bst_r {X : Type} : forall n l r,
  @bst X (btsub n l r) ->
  bst r.
Proof. apply bst_lr.
Qed.

Lemma minkey_maxkey {X : Type} : forall (n : @node X) l r,
  minkey (btsub n l r) <= maxkey (btsub n l r).
Proof.
  intros [k d] l r.
  assert (forall n m, min n m <= max n m).
    intros. destruct (min_dec n m); rewrite e. apply le_max_l. apply le_max_r.
  destruct l;
    destruct r;
      simpl.
  reflexivity.
  (* STUCK *)
Admitted.

Lemma maxkey_r_eq {X : Type} : forall k (d : X) l r,
  l = btnil \/ maxkey l <= k ->
  k <= maxkey r ->
  maxkey (btsub (nd k d) l r) = maxkey r.
Proof.
Admitted.

Lemma minkey_l_eq {X : Type} : forall k (d : X) l r,
  k <= minkey l ->
  r = btnil \/ k <= minkey r ->
  minkey (btsub (nd k d) l r) = minkey l.
Proof.
Admitted.

Lemma minkey_nd_eq {X : Type} : forall k (d : X) r,
  r = btnil \/ k <= minkey r ->
  minkey (btsub (nd k d) btnil r) = k.
Proof with eauto.
Admitted.

Lemma minkey_l_min {X : Type} : forall k (d : X) ln ll lr r,
  r = btnil \/ k <= minkey r ->
  minkey (btsub (nd k d) (btsub ln ll lr) r) = min k (minkey (btsub ln ll lr)).
Proof.
Admitted.

Lemma maxkey_nd_eq {X : Type} : forall k (d : X) l,
  l = btnil \/ maxkey l <= k ->
  maxkey (btsub (nd k d) l btnil) = k.
Proof with eauto.
Admitted.

Lemma maxkey_r_max {X : Type} : forall k (d : X) l rn rl rr,
  l = btnil \/ maxkey l <= k ->
  maxkey (btsub (nd k d) l (btsub rn rl rr)) = max k (maxkey (btsub rn rl rr)).
Proof.
Admitted.


Lemma bst_bstdel_le_invariant {X : Type} : forall t k t',
  t' <> btnil ->
  @bst X t ->
  bstdel t k t' ->
  (maxkey t' <= maxkey t /\ minkey t <= minkey t').
Proof with auto.
  intros t k' t' Ht' Hs Hd.
  generalize dependent t'.
  generalize dependent k'.
  induction t as [| [k d]]; intros;
    inversion Hd; subst.
  intuition.                    (* base case is contradiction *)
  Case "bstdelleaf". intuition.
  Case "bstdelndl".
    set (btsub ln ll lr) as l.
    assert (maxkey l < k') by (subst l; inversion Hs; assumption).
    (* assert (bst l) as Hsl by (subst l; inversion Hs; auto). *)
    assert (bst l) as Hsl by (apply bst_l in Hs; assumption).
    subst l. apply bst_btrmostnd_maxkey in H5; try assumption.
    split;
      destruct l'.
    SCase "maxkey".
      SSCase "l' = btnil". apply maxkey_le_nd_le... omega.
      SSCase "l' = btsub".
        apply IHt1 in H6... destruct H6.
        subst. apply maxkey_le_nd_le... omega.
    SCase "minkey".
      SSCase "l' = btnil".
        rewrite minkey_l. rewrite minkey_nd_eq. subst.
        apply minkey_maxkey.
        destruct t2. left. reflexivity.
        assert (k' < minkey (btsub n t2_1 t2_2)) by (inversion Hs; assumption).
        right. omega.
      SSCase "l' = btsub".
        apply IHt1 in H6... destruct H6.
        rewrite minkey_l. rewrite H1.
        rewrite minkey_l_min. subst.
        set (btsub ln ll lr) as l in *.
        set (btsub n l'1 l'2) as l' in *.
        destruct (min_dec (maxkey l) (minkey l')); rewrite e.
          eapply le_trans. apply minkey_maxkey. subst l l'; assumption.
          reflexivity.
        destruct t2. left. reflexivity.
        assert (pk < k') as Hkp by (subst pk; inversion Hs; assumption).
        assert (k' < minkey (btsub n0 t2_1 t2_2))
          by (inversion Hs; assumption).
        right. omega.
  Case "bstdelndr".
    set (btsub rn rl rr) as r.
    assert (k' < minkey r) by (subst r; inversion Hs; assumption).
    assert (bst r) as Hsr by (apply bst_r in Hs; assumption).
    subst r. apply bst_btlmostnd_minkey in H5; try assumption.
    assert (k' < sk) by (subst sk; inversion Hs; assumption).
    split;
      destruct r'.
    SCase "maxkey".
      SSCase "r' = btnil".
        rewrite <- maxkey_r. rewrite maxkey_nd_eq. subst.
        apply minkey_maxkey.
        destruct t1. left. reflexivity.
        assert (maxkey (btsub n t1_1 t1_2) < k') by (inversion Hs; assumption).
        right. omega.
      SSCase "l' = btsub".
        apply IHt2 in H6... destruct H6.
        assert (maxkey (btsub rn rl rr) <=
          maxkey (btsub (nd k' d) t1 (btsub rn rl rr))) by apply maxkey_r.
        eapply le_trans; try eassumption. rewrite <- H1.
        rewrite maxkey_r_max. subst.
        destruct (max_dec (minkey (btsub rn rl rr)) (maxkey (btsub n r'1 r'2)));
          rewrite e.
          eapply le_trans. apply H2. apply minkey_maxkey.
          reflexivity.
        destruct t1. left. reflexivity.
        assert (k' < sk) as Hks by (subst sk; inversion Hs; assumption).
        assert (maxkey (btsub n0 t1_1 t1_2) < k')
          by (inversion Hs; assumption).
        right. omega.
    SCase "minkey".
      SSCase "l' = btnil". apply minkey_le_nd_le... omega.
      SSCase "l' = btsub".
        apply IHt2 in H6... destruct H6.
        subst. apply minkey_le_nd_le... omega.
  Case "bstdell".
    assert (bst (btsub ln ll lr)) by (inversion Hs; assumption).
    split.
    SCase "maxkey".
      apply maxkey_le_nd_le...
      destruct l'. left. reflexivity.
      right. apply IHt1 in H6... destruct H6. assumption.
    SCase "minkey".
      apply minkey_le_nd_le...
      destruct l'. left. reflexivity.
      right. apply IHt1 in H6... destruct H6. assumption.
  Case "bstdelr".
    assert (bst (btsub rn rl rr)) by (inversion Hs; assumption).
    split;
      try (apply maxkey_le_nd_le; auto);
        try (apply minkey_le_nd_le; auto);
          destruct r'; auto;
            apply IHt2 in H6; auto; destruct H6...
Qed.

(* This lemma should be simpler to prove than the above:

   Probably we need the*)
Lemma bst_bstdel_max_ne {X : Type} : forall t k (d : X) t',
  t' <> btnil ->
  @bst X t ->
  btrmostnd t (nd k d) ->
  bstdel t k t' ->
  maxkey t' <> k.
Proof.
(* probably we need to use bst_bstdel_le_invariant at some point *)
Admitted.

Lemma bst_bstdel_min_ne {X : Type} : forall t k (d : X) t',
  t' <> btnil ->
  @bst X t ->
  btlmostnd t (nd k d) ->
  bstdel t k t' ->
  minkey t' <> k.
Proof.
(* probably we need to use bst_bstdel_le_invariant at some point *)
Admitted.


(* Now we prove an important theorem:
   Deletion doesn't violate the BST property *)

Theorem bstdel_bst {X : Type} : forall t k t',
  @bst X t ->
  bstdel t k t' ->
  bst t'.
Proof with auto.
  intros t k t' Hs Hd.
  induction Hd; intros.
  Case "bstdelnone". apply bstnil.
  Case "bstdelleaf". apply bstnil.
  Case "bstdelndl".
    assert (bst (btsub ln ll lr)) by (inversion Hs; assumption).
    destruct l' as [| [l'k l'd]]. inversion Hd; subst.
    SCase "l' = btnil".
      assert (pk < k) by (inversion Hs; auto).
      destruct r. constructor. destruct n.
      apply bsthir; inversion Hs; subst; auto. omega.
    SCase "l' = btsub".
      assert (maxkey (btsub ln ll lr) < k) by (inversion Hs; assumption).
      assert (maxkey (btsub (nd l'k l'd) l'1 l'2) <> pk)
        by (eapply bst_bstdel_max_ne; eauto).
      apply bst_btrmostnd_maxkey in H...
      apply bst_bstdel_le_invariant in Hd... destruct Hd as [Hmin Hmax].
      destruct r. constructor... subst. omega.
      destruct n as [rk rd].
      assert (k < minkey (btsub (nd rk rd) r1 r2))
        by (inversion Hs; assumption).
      assert (bst (btsub (nd rk rd) r1 r2)) by (inversion Hs; assumption).
      constructor; auto; try omega.
  Case "bstdelndr".
    assert (bst (btsub rn rl rr)) by (inversion Hs; assumption).
    destruct r' as [| [r'k r'd]]. inversion Hd; subst.
    SCase "r' = btnil".
      assert (k < sk) by (inversion Hs; auto).
      destruct l. constructor. destruct n.
      apply bsthil; inversion Hs; subst; auto. omega.
    SCase "r' = btsub".
      assert (k < minkey (btsub rn rl rr)) by (inversion Hs; assumption).
      assert (minkey (btsub (nd r'k r'd) r'1 r'2) <> sk)
        by (eapply bst_bstdel_min_ne; eauto).
      apply bst_btlmostnd_minkey in H...
      apply bst_bstdel_le_invariant in Hd... destruct Hd as [Hmin Hmax].
      destruct l. constructor... subst. omega.
      destruct n as [lk ld].
      assert (maxkey (btsub (nd lk ld) l1 l2) < k)
        by (inversion Hs; assumption).
      assert (bst (btsub (nd lk ld) l1 l2)) by (inversion Hs; assumption).
      constructor; auto; try omega.
  Case "bstdell".
    destruct l'. destruct r; try constructor; inversion Hs; auto.
    assert (bst (btsub ln ll lr)) by (inversion Hs; auto).
    apply bst_bstdel_le_invariant in Hd... destruct Hd as [Hmin Hmax].
    assert (maxkey (btsub n l'1 l'2) < k)
      by (inversion Hs; subst; auto; omega).
    destruct n. destruct r; inversion Hs; auto.
  Case "bstdelr".
    destruct r'. destruct l; try constructor; inversion Hs; auto.
    assert (bst (btsub rn rl rr)) by (inversion Hs; auto).
    apply bst_bstdel_le_invariant in Hd... destruct Hd as [Hmin Hmax].
    assert (k < minkey (btsub n r'1 r'2))
      by (inversion Hs; subst; auto; omega).
    destruct n. destruct l; inversion Hs; auto.
Qed.

Theorem bstdel_correct {X : Type} : forall (t : @bt X) k' t' k,
  bst t ->
  bstdel t k' t' ->
  (bstsearch t k <-> bstsearch t' k \/ k = k') /\ bst t'.
Proof.
(* we need bstdel_bst *)
  intros t k' t' k Hs Hd. split.
  Case "->".
    admit.
  Case "<-".
    admit.
Admitted.

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
      by (subst p; rewrite bst_maxkey_r in Hkp; assumption).
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]. apply bsthil...
      apply bstbal; auto. apply Hku. intro H'. inversion H'.
    assert (pk < minkey g').
      assert (pk < minkey r) as Hkr' by (inversion Hsp; assumption).
      subst g'. rewrite bst_minkey_l; assumption.
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
  (* Analogous to right rotation, but with more automation. *)
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
      by (subst p; rewrite bst_minkey_l in Hkp; assumption).
    assert (bst g') as Hsg'.
      destruct u as [| [uk ud] ul ur]; constructor...
      apply Hku; intro H'; inversion H'.
    assert (maxkey g' < pk).
      inversion Hsp;
        subst g'; rewrite bst_maxkey_r; assumption.
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
(* at some point we will use avlins_bst *)
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
