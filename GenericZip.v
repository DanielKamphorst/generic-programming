Require Import HoTT.HoTT GenericZipAndTraverse.PolynomialFunctors.

Definition zipExtension (p : Polynomial) {A B : Type}
  : Pullback
      (pr1 (P := fun i => Direction p i -> A))
      (pr1 (P := fun i => Direction p i -> B))
    <~> Extension p (A * B).
Proof.
  refine (
    equiv_functor_sigma_id (fun i => equiv_prod_coind _ _)
    oE (equiv_functor_sigma_pb
      (Q := fun '(i; i'; w) => (Direction p i -> A) * (Direction p i' -> B))
      (equiv_pr1 (fun i => {i' : Position p & i = i'}))^-1)^-1
    oE _
  ).
  make_equiv.
Defined.

Definition zip (F : Type -> Type) `{IsPolynomialFunctor F} {A B : Type}
  : Pullback
      (pr1 o equivalenceToExtension F A)
      (pr1 o equivalenceToExtension F B)
    <~> F (A * B) :=
  (equivalenceToExtension F (A * B))^-1
  oE zipExtension (polynomial F)
  oE (equiv_sigma_prod (fun '(x', y') => pr1 x' = pr1 y'))^-1
  oE equiv_functor_sigma_pb
    (equivalenceToExtension F A *E equivalenceToExtension F B)
  oE equiv_sigma_prod _.

Notation unzip F := (zip F)^-1.

Context `{Funext}.
Open Scope nat_scope.

Eval compute in
  zip Tree
    ( node leaf 2 (node leaf 4 leaf)
    ; node leaf true (node leaf false leaf)
    ; idpath
    ).

Eval compute in unzip Tree (node leaf (0, false) (node leaf (1, true) leaf)).
