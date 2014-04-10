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


Inductive height {X : Type} : @bt X -> nat -> Prop :=
| heightnil : height btnil 0
| heightsub : forall k d l lh r rh h,
  height l lh ->
  height r rh ->
  h = S (max lh rh) ->
  height (btsub (nd k d) l r) h
.

Example height_0 : @height nat btnil 0.
Proof. constructor. Qed.
Example height_1 : @height nat (btsub (nd 3 0) btnil btnil) 1.
Proof. econstructor; constructor. Qed.

(* For search trees, [id] can serve as a key (used for ordering) *)
Definition key {X : Type} (n : @node X) : nat :=
  match n with
    | nd k d => k
  end
.

Fixpoint minkey {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub (nd k _) l r => (min k
      (min (minkey l) (minkey r)))
  end
.

Fixpoint maxkey {X : Type} (t : @bt X) : nat :=
  match t with
    | btnil => 0
    | btsub (nd k _) l r => (max k
      (max (maxkey l) (maxkey r)))
  end
.

Inductive bst {X : Type} : @bt X -> Prop :=
| bstnil : bst btnil
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
  (maxkey r) < k ->
  bst r ->
  bst (btsub (nd k d) btnil r)
.


Inductive hbal : nat -> nat -> Prop :=
| hbaleq : forall h, hbal h h
| hballh : forall h, hbal (S h) h
| hbalrh : forall h, hbal h (S h)
.

(* AVL tree - a Binary Search Tree s.t. height diff of every subtree <= 1 *)
Inductive avlt {X : Type} : @bt X -> Prop :=
| avltnil : avlt btnil
| avltsub : forall k d l lh r rh,
  height l lh ->
  height r rh ->
  hbal lh rh ->
  avlt l ->
  avlt r ->
  bst (btsub (nd k d) l r) ->
  avlt (btsub (nd k d) l r)
.

(* Q: Would proofs be easier if we separate bal and bst as requirements
   and define AVL tree as a combination of both (see below)? *)

Inductive bal {X : Type} : @bt X -> Prop :=
| balnil : bal btnil
| balsub : forall k d l lh r rh,
  height l lh ->
  height r rh ->
  hbal lh rh ->
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
