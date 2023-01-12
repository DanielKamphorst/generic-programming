From HoTT Require Import HoTT.

Record Poly := makePoly
  { positions : Type
  ; directions : positions -> Type
  }.

Definition coproductOfFunctors {I C : Type} (F : I -> C -> Type) : C -> Type :=
  fun c => {i : I & F i c}.

#[export] Instance coproductOfFunctorsIs0Functor {I C : Type} `{IsGraph C}
  (F : I -> C -> Type) `{forall i : I, Is0Functor (F i)}
  : Is0Functor (coproductOfFunctors F).
Proof.
  constructor.
  exact (fun c d f => functor_sigma idmap (fun i => fmap (F i) f)).
Defined.

Definition Ext (p : Poly) : Type -> Type :=
  coproductOfFunctors (opyon o directions p).

Class IsPolynomialFunctor (F : Type -> Type) `{!Is0Functor F} :=
  makeIsPolynomialFunctor
    { polynomial : Poly
    ; equivalenceToExtension : NatEquiv F (Ext polynomial)
    }.

Arguments makeIsPolynomialFunctor F {_}.
Arguments polynomial              F {_ _}.
Arguments equivalenceToExtension  F {_ _}.

Definition unzip' (p : Poly) {A B : Type}
  : Ext p (A * B)
  <~> Pullback
    (pr1 (P := fun i => directions p i -> A))
    (pr1 (P := fun i => directions p i -> B)).
Proof.
  refine (
    _
    oE equiv_functor_sigma_pb
      (Q := fun '(i; i'; w) => (directions p i -> A) * (directions p i' -> B))
      (equiv_pr1 (fun i => {i' : positions p & i = i'}))^-1
    oE equiv_functor_sigma_id (fun i => (equiv_prod_coind _ _)^-1)
  ).
  make_equiv.
Defined.

Definition unzip (F : Type -> Type) `{IsPolynomialFunctor F} {A B : Type}
    : F (A * B)
    <~> Pullback
      (pr1 o equivalenceToExtension F A)
      (pr1 o equivalenceToExtension F B) :=
  (equiv_sigma_prod _)^-1
  oE (equiv_functor_sigma_pb
    (equivalenceToExtension F A *E equivalenceToExtension F B))^-1
  oE equiv_sigma_prod (fun '(a', b') => pr1 a' = pr1 b')
  oE unzip' (polynomial F)
  oE equivalenceToExtension F (A * B).

Notation zip F := (unzip F)^-1.

Inductive Tree (A : Type) : Type :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Arguments leaf {A}.
Arguments node {A}.

Notation indTree := Tree_rect.

Definition recTree (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Tree A -> X :=
  indTree A (fun _ => X) x1 (fun _ x a _ => x2 x a).

Fixpoint TreeMap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
  match t with
  | leaf         => leaf
  | node t1 a t2 => node (TreeMap f t1) (f a) (TreeMap f t2)
  end.

#[export] Instance TreeIs0Functor : Is0Functor Tree.
Proof.
  constructor; exact @TreeMap.
Defined.

Fixpoint TreeDirections (t : Tree Unit) : Type :=
  match t with
  | leaf         => Empty
  | node t1 _ t2 => TreeDirections t1 + Unit + TreeDirections t2
  end.

Definition Tree' : Poly := makePoly (Tree Unit) TreeDirections.

Definition leaf' {A : Type} : Ext Tree' A := (leaf; Empty_rec).

Definition node' {A : Type} : Ext Tree' A -> A -> Ext Tree' A -> Ext Tree' A :=
  fun '(t1; a1) a '(t2; a2) =>
    (node t1 tt t2; sum_ind _ (sum_ind _ a1 (fun _ => a)) a2).

Definition recTree' (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Ext Tree' A -> X :=
  sig_ind _ (
    fix f (t : Tree Unit) : (TreeDirections t -> A) -> X :=
      match t with
      | leaf         => fun _ => x1
      | node t1 _ t2 => fun a =>
          x2 (f t1 (a o inl o inl)) (a (inl (inr tt))) (f t2 (a o inr))
      end
  ).

Definition indTree' `{Funext} (A : Type)
    (X : Ext Tree' A -> Type)
    (x1 : X leaf')
    (x2
      : forall t1' : Ext Tree' A
      , X t1'
      -> forall (a : A) (t2' : Ext Tree' A), X t2' -> X (node' t1' a t2'))
    : forall t' : Ext Tree' A, X t' :=
  sig_ind X (
    fix f (t : Tree Unit) : forall a : TreeDirections t -> A, X (t; a) :=
      match t with
      | leaf          => fun a => transport (X o exist _ leaf) (contr a) x1
      | node t1 tt t2 => fun a => transport (X o exist _ (node t1 tt t2))
          (ap (fun a' => sum_ind _ (sum_ind _ (a o inl o inl) a') (a o inr))
              (eisretr (fun x => unit_name x) (a o inl o inr))
            @ ap (fun a' => sum_ind _ a' (a o inr))
              (eisretr (sum_ind_uncurried _) (a o inl))
            @ eisretr (sum_ind_uncurried _) a)
          (x2 _ (f t1 (a o inl o inl)) (a (inl (inr tt))) _ (f t2 (a o inr)))
      end
  ).

#[export] Instance TreeIsPolynomialFunctor `{Funext} : IsPolynomialFunctor Tree.
Proof.
  apply (makeIsPolynomialFunctor Tree Tree'), natequiv_inverse.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recTree' A (Tree A) leaf node).
    + exact (recTree A (Ext Tree' A) leaf' node').
    + rapply indTree.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node t1' a t2') w1 w2
        ).
    + rapply indTree'.
      * reflexivity.
      * exact (fun t1' w1 a t2' w2 =>
          ap011 (fun t1'' t2'' => node' t1'' a t2'') w1 w2
        ).
  - intros A B f; rapply indTree'.
    + reflexivity.
    + exact (fun t1' w1 a t2' w2 =>
        ap011 (fun t1 t2 => node t1 (f a) t2) w1 w2
      ).
Defined.

Context `{Funext}.
Open Scope nat_scope.

Eval compute in
  zip Tree
    ( node leaf false (node (node leaf true leaf) false leaf)
    ; node leaf 0     (node (node leaf 2    leaf) 4     leaf)
    ; idpath
    ).

Eval compute in
  pullback_pr1 (unzip Tree (
    node (node leaf (false, 0) (node leaf (true, 1) leaf)) (false, 2) leaf
  )).
Eval compute in
  pullback_pr2 (unzip Tree (
    node (node leaf (false, 0) (node leaf (true, 1) leaf)) (false, 2) leaf
  )).
