From HoTT Require Import HoTT.

#[export] Existing Instance isgraph_forall | 0.

#[export] Instance ProductIs0Functor : Is0Functor (uncurry prod).
Proof.
  constructor; exact (fun A B => uncurry functor_prod).
Defined.

Record LaxMonoidalFunctor := makeLaxMonoidalFunctor
  { UnderlyingFunctor :> Fun11 Type Type
  ; η : Unit -> UnderlyingFunctor Unit
  ; μ
    : NatTrans
      (uncurry prod o functor_prod UnderlyingFunctor UnderlyingFunctor)
      (UnderlyingFunctor o uncurry prod)
  }.

Record MonoidalNaturalTransformation (F G : LaxMonoidalFunctor) :=
  makeMonoidalNaturalTransformation
    { naturalTransformation :> NatTrans F G
    ; compatibilityWithUnit : η G == naturalTransformation Unit o η F
    ; compatibilityWithProduct A B
      : μ G (A, B)
          o fmap11 prod (naturalTransformation A) (naturalTransformation B)
        == naturalTransformation (A * B) o μ F (A, B)
    }.

Arguments compatibilityWithUnit    {F G}.
Arguments compatibilityWithProduct {F G}.

#[export] Instance LaxMonoidalFunctorIsGraph : IsGraph LaxMonoidalFunctor.
Proof.
  constructor; exact MonoidalNaturalTransformation.
Defined.

#[export] Instance UnderlyingFunctorIs0Functor : Is0Functor UnderlyingFunctor.
Proof.
  constructor; exact naturalTransformation.
Defined.

Definition IdentityLaxMonoidalFunctor : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor fun11_id idmap (nattrans_id (uncurry prod)).

Definition CompositeOfTwoLaxMonoidalFunctors (G F : LaxMonoidalFunctor)
    : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor (fun11_compose G F)
    (fmap G (η F) o η G)
    (nattrans_comp
      (nattrans_postwhisker G (μ F))
      (nattrans_prewhisker (μ G) (functor_prod F F))).

#[export] Instance fun11_funIs0Functor
  (C D : Type) `{Is1Cat C} `{Is1Cat D}
  : Is0Functor (fun11_fun C D).
Proof.
  constructor; exact (fun F G => trans_nattrans F G).
Defined.

Definition eval {A B : Type} (a : A) : (A -> B) -> B := fun f => f a.

#[export] Instance evalIs0Functor {I : Type} (C : Type) `{IsGraph C} (i : I)
  : Is0Functor (eval (B := C) i).
Proof.
  constructor; exact (fun c d f => f i).
Defined.

Definition ApplyLaxMonoidalFunctorTo (A : Type) : LaxMonoidalFunctor -> Type :=
  eval A o fun11_fun Type Type o UnderlyingFunctor.

Notation Maybe := option.
Notation some := Some.
Notation none := None.

#[export] Instance MaybeIs0Functor : Is0Functor Maybe.
Proof.
  constructor.
  exact (fun A B f a' =>
    match a' with
    | some a => some (f a)
    | none   => none
    end
  ).
Defined.

#[export] Instance MaybeIs1Functor : Is1Functor Maybe.
Proof.
  constructor; try (intros; intros []; reflexivity).
  intros A B f g w; rapply option_rect; try reflexivity.
  exact (fun a => ap some (w a)).
Defined.

Definition MaybeLaxMonoidalFunctor : LaxMonoidalFunctor.
Proof.
  refine (makeLaxMonoidalFunctor (Build_Fun11 _ _ Maybe) some _).
  snrapply Build_NatTrans.
  - exact (fun A a' =>
      match a' with
      | (some a1, some a2) => some (a1, a2)
      | _                  => none
      end
    ).
  - intros A B f [[] []]; reflexivity.
Defined.
