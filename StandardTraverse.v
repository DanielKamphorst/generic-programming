From HoTT Require Import HoTT.

Definition horizontalCompositeOfTwoSquares {A A' A'' B B' B'' : Type}
    {h : A -> A'} {h' : A' -> A''}
    {f : A -> B} {f' : A' -> B'} {f'' : A'' -> B''}
    {k : B -> B'} {k' : B' -> B''}
    (w1 : f' o h = k o f) (w2 : f'' o h' = k' o f')
    : f'' o h' o h = k' o k o f :=
  ap (fun x => x o h) w2 @ ap (fun x => k' o x) w1.

Record Functor := makeFunctor
  { onObjects :> Type -> Type
  ; onMorphisms {A B} : (A -> B) -> (onObjects A -> onObjects B)
  ; preservationOfIdentities {A} : onMorphisms (fun a : A => a) = idmap
  ; preservationOfComposition {A B C} (g : B -> C) (f : A -> B)
    : onMorphisms (g o f) = onMorphisms g o onMorphisms f
  }.

Definition functorPreservesSquare (F : Functor) {A A' B B' : Type}
    {h : A -> A'}
    {f : A -> B} {f' : A' -> B'}
    {k : B -> B'}
    (w : f' o h = k o f)
    : onMorphisms F f' o onMorphisms F h = onMorphisms F k o onMorphisms F f :=
  (preservationOfComposition F f' h)^
  @ ap (onMorphisms F) w
  @ preservationOfComposition F k f.

Definition identityFunctor : Functor :=
  makeFunctor idmap (fun _ _ => idmap)
    (fun _ => idpath)
    (fun _ _ _ _ _ => idpath).

Definition compositeOfTwoFunctors (G F : Functor) : Functor :=
  makeFunctor (G o F) (fun _ _ => onMorphisms G o onMorphisms F)
    (fun _ =>
      ap (onMorphisms G) (preservationOfIdentities F)
      @ preservationOfIdentities G)
    (fun _ _ _ g f =>
      ap (onMorphisms G) (preservationOfComposition F g f)
      @ preservationOfComposition G (onMorphisms F g) (onMorphisms F f)).

Record LaxMonoidalFunctor := makeLaxMonoidalFunctor
  { underlyingFunctor :> Functor
  ; μ {A B}
    : underlyingFunctor A * underlyingFunctor B -> underlyingFunctor (A * B)
  ; μNaturality {A A' B B'} (f : A -> A') (g : B -> B')
    : onMorphisms underlyingFunctor (functor_prod f g) o μ
    = μ
      o functor_prod
        (onMorphisms underlyingFunctor f)
        (onMorphisms underlyingFunctor g)
  ; η : Unit -> underlyingFunctor Unit
  }.

Definition identityLaxMonoidalFunctor : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor identityFunctor
    (fun _ _ => idmap) (fun _ _ _ _ _ _ => idpath)
    idmap.

Definition compositeOfTwoLaxMonoidalFunctors (G F : LaxMonoidalFunctor) :=
  makeLaxMonoidalFunctor (compositeOfTwoFunctors G F)
    (fun _ _ => onMorphisms G (μ F) o μ G)
    (fun _ _ _ _ f g => horizontalCompositeOfTwoSquares
      (μNaturality G (onMorphisms F f) (onMorphisms F g))
      (functorPreservesSquare G (μNaturality F f g)))
    (onMorphisms G (η F) o η G).

Record NaturalTransformation (F G : Functor) := makeNaturalTransformation
  { component A :> F A -> G A
  ; naturality {A B} (f : A -> B)
    : onMorphisms G f o component A = component B o onMorphisms F f
  }.

Arguments naturality {F G} α {A B} : rename.

Record MonoidalNaturalTransformation (F G : LaxMonoidalFunctor) :=
  makeMonoidalNaturalTransformation
    { underlyingNaturalTransformation :> NaturalTransformation F G
    ; compatibilityWithProduct A B
      : μ G
        o functor_prod
          (underlyingNaturalTransformation A)
          (underlyingNaturalTransformation B)
      = underlyingNaturalTransformation (A * B) o μ F
    ; compatibilityWithUnit : η G = underlyingNaturalTransformation Unit o η F
    }.

Arguments compatibilityWithUnit {F G} α : rename.
Arguments compatibilityWithProduct {F G} α : rename.

Notation List := list.

Fixpoint ListMap {A B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

Definition nil' {A : Type} : Unit -> List A := unit_name nil.
Definition cons' {A : Type} : A * List A -> List A := prod_ind _ (@cons A).

Fixpoint τ (F : LaxMonoidalFunctor) (A : Type) (l : List (F A)) : F (List A) :=
  match l with
  | nil       => onMorphisms F nil' (η F tt)
  | cons a l' => onMorphisms F cons' (μ F (a, τ F A l'))
  end.

Fixpoint τNaturality1 {F G} (α : MonoidalNaturalTransformation F G) {A}
    (l : List (F A))
    : α (List A) (τ F A l) = τ G A (ListMap (α A) l) :=
  match l with
  | nil       =>
      happly (naturality α nil')^ (η F tt)
      @ ap (onMorphisms G nil') (happly (compatibilityWithUnit α)^ tt)
  | cons a l' =>
      happly (naturality α cons')^ (μ F (a, τ F A l'))
      @ ap
        (onMorphisms G cons')
        (happly (compatibilityWithProduct α A (List A))^ (a, τ F A l'))
      @ ap (onMorphisms G cons' o μ G o pair (α A a)) (τNaturality1 α l')
  end.

Fixpoint τNaturality2 (F : LaxMonoidalFunctor) {A B} (f : A -> B)
    (l : List (F A))
    : onMorphisms F (ListMap f) (τ F A l)
    = τ F B (ListMap (onMorphisms F f) l) :=
  match l with
  | nil       =>
      happly (preservationOfComposition F (ListMap f) nil')^ (η F tt)
  | cons a l' =>
      happly
        (preservationOfComposition F (ListMap f) cons')^
        (μ F (a, τ F A l'))
      @ happly
        (preservationOfComposition F cons' (functor_prod f (ListMap f)))
        (μ F (a, τ F A l'))
      @ ap
        (onMorphisms F cons')
        (happly (μNaturality F f (ListMap f)) (a, τ F A l'))
      @ ap
        (onMorphisms F cons' o μ F o pair (onMorphisms F f a))
        (τNaturality2 F f l')
  end.

Fixpoint τUnitarity {A} (l : List A) : τ identityLaxMonoidalFunctor A l = l :=
  match l with
  | nil       => idpath
  | cons a l' => ap (cons a) (τUnitarity l')
  end.

Fixpoint τLinearity `{Funext} {G F : LaxMonoidalFunctor} {A}
    (l : List (G (F A)))
    : onMorphisms G (τ F A) (τ G (F A) l)
    = τ (compositeOfTwoLaxMonoidalFunctors G F) A l :=
  match l with
  | nil       =>
      happly (preservationOfComposition G (τ F A) nil')^ (η G tt)
      @ happly
        (ap
          (onMorphisms G)
          (eisretr (fun x => unit_name x) (onMorphisms F nil' o η F)))
        (η G tt)
      @ happly (preservationOfComposition G (onMorphisms F nil') (η F)) (η G tt)
  | cons a l' =>
      happly
        (preservationOfComposition G (τ F A) cons')^
        (μ G (a, τ G (F A) l'))
      @ happly
        (preservationOfComposition G
          (onMorphisms F cons' o μ F)
          (functor_prod idmap (τ F A)))
        (μ G (a, τ G (F A) l'))
      @ ap
        (onMorphisms G (onMorphisms F cons' o μ F))
        (happly (μNaturality G idmap (τ F A)) (a, τ G (F A) l'))
      @ ap
        (onMorphisms G (onMorphisms F cons' o μ F) o μ G)
        (happly
          (ap
            (fun x => functor_prod x (onMorphisms G (τ F A)))
            (preservationOfIdentities G))
          (a, τ G (F A) l'))
      @ ap
        (onMorphisms G (onMorphisms F cons' o μ F) o μ G o pair a)
        (τLinearity l')
      @ happly
        (preservationOfComposition G (onMorphisms F cons') (μ F))
        (μ G (a, τ (compositeOfTwoLaxMonoidalFunctors G F) A l'))
  end.

Definition optionMap {A B} (f : A -> B) (a' : option A) : option B :=
  match a' with
  | Some a => Some (f a)
  | None   => None
  end.

Definition optionFunctor `{Funext} : Functor.
Proof.
  apply (makeFunctor option (@optionMap))
  ; intros
  ; apply path_forall
  ; rapply option_rect
  ; reflexivity.
Defined.

Definition optionμ {A B} (x : option A * option B) : option (A * B) :=
  match x with
  | (Some a, Some b) => Some (a, b)
  | _                => None
  end.

Definition optionLaxMonoidalFunctor `{Funext} : LaxMonoidalFunctor.
Proof.
  refine (makeLaxMonoidalFunctor optionFunctor (@optionμ) _ Some).
  intros.
  apply path_forall.
  exact (fun x =>
    match x with
    | (Some _, Some _) => idpath
    | _                => idpath
    end).
Defined.

Context `{Funext}.
Open Scope list_scope.
Open Scope nat_scope.
Eval compute in
  τ optionLaxMonoidalFunctor nat (Some 0 :: Some 2 :: Some 4 :: Some 6 :: nil).
Eval compute in
  τ optionLaxMonoidalFunctor nat (Some 0 :: Some 2 :: None :: Some 6 :: nil).
