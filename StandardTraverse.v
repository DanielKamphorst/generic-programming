Require Import
  HoTT.HoTT
  GenericZipAndTraverse.PolynomialFunctors
  GenericZipAndTraverse.LaxMonoidalFunctors.

Fixpoint τ (F : LaxMonoidalFunctor) (A : Type) (l : List (F A)) : F (List A) :=
  match l with
  | nil        => fmap F (unit_name nil) (η F tt)
  | cons a' l' => fmap F (uncurry cons) (μ F (A, List A) (a', τ F A l'))
  end.

Open Scope list_scope.
Open Scope nat_scope.

Eval compute in τ MaybeLaxMonoidalFunctor nat (some 1 :: none :: some 3 :: nil).
Eval compute in
  τ MaybeLaxMonoidalFunctor nat (some 1 :: some 2 :: some 3 :: nil).
