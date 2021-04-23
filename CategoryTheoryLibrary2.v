Require Export Program.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Export CategoryTheory.
  Open Scope type_scope.

  Class Functor F := {
    fmap : forall A B, (A -> B) -> (F A -> F B)
  }.

  Class Bifunctor F := {
    bimap : forall A A' B B', (A -> A') -> (B -> B') -> (F A B -> F A' B')
  }.

  Definition pair' A B C (f : C -> A) (g : C -> B) : C -> A * B :=
    fun c => (f c, g c).
  Infix "&&&" := pair' (at level 50).

  Instance productBifunctor : Bifunctor prod := {
    bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.

  Definition copair A B C (f : A -> C) (g : B -> C) : A + B -> C := fun cp =>
    match cp with
    | inl a => f a
    | inr b => g b
    end.
  Infix "|||" := copair (at level 60).

  Instance coproductBifunctor : Bifunctor sum := {
    bimap _ _ _ _ f g := inl ∘ f ||| inr ∘ g
  }.

  Ltac crush :=
    let x := fresh "x"
    in intros
      ; match goal with [|- _ /\ _] => split | _ => idtac end
      ; extensionality x
      ; repeat match goal with [x' : _ |- _] => try destruct x' end
      ; auto.

  Theorem coproductUniversalProperty
      : forall A B C (f : A -> C) (g : B -> C) (h : A + B -> C)
      , h = f ||| g <-> h ∘ inl = f /\ h ∘ inr = g.
    split; [intros -> | intros [<- <-]]; crush.
  Qed.

  Corollary coproductCancellationLaw1
      : forall A B C (f : A -> C) (g : B -> C), (f ||| g) ∘ inl = f.
    intros; eapply coproductUniversalProperty; reflexivity.
  Qed.

  Corollary coproductCancellationLaw2
      : forall A B C (f : A -> C) (g : B -> C), (f ||| g) ∘ inr = g.
    intros; eapply coproductUniversalProperty; reflexivity.
  Qed.
  
  Notation curry   := prod_uncurry.
  Notation uncurry := prod_curry.

  Reserved Notation "A × B" (at level 40).

  Inductive partialProd A B : Type :=
    | inlp : A      -> A × B
    | midp : A -> B -> A × B
    | inrp :      B -> A × B
  where "A × B" := (partialProd A B).

  Definition partialProduct A B : (A * B) + (A + B) -> A × B :=
    uncurry midp ||| (inlp ||| inrp).

  Definition partialProductInverse A B : A × B -> (A * B) + (A + B) :=
    partialProd_rect _ (inr ∘ inl) (curry inl) (inr ∘ inr).

  Instance partialProductBifunctor : Bifunctor partialProd := {
    bimap _ _ _ _ f g :=
      partialProduct
      ∘ bimap (bimap f g) (bimap f g)
      ∘ partialProductInverse
  }.

  Inductive polynomialFunctorExpression : Type :=
    | identityFunctor : polynomialFunctorExpression
    | product
        : polynomialFunctorExpression
        -> polynomialFunctorExpression
        -> polynomialFunctorExpression
    | coproduct
        : polynomialFunctorExpression
        -> polynomialFunctorExpression
        -> polynomialFunctorExpression
    | composite
        : polynomialFunctorExpression
        -> polynomialFunctorExpression
        -> polynomialFunctorExpression.

  Infix "|*|" := product (at level 40).
  Infix "|+|" := coproduct (at level 50).
  Infix "|∘|" := composite (at level 40).

  Reserved Notation "⟦ F ⟧".

  Fixpoint denotation F : Type -> Type :=
    match F with
    | identityFunctor => id
    | F' |*| G        => fun A => ⟦F'⟧ A * ⟦G⟧ A
    | F' |+| G        => fun A => ⟦F'⟧ A + ⟦G⟧ A
    | G  |∘| F'       => ⟦G⟧ ∘ ⟦F'⟧
    end
  where "⟦ F ⟧" := (denotation F).

  Fixpoint polynomialFunctorMap F A B : (A -> B) -> (⟦F⟧ A -> ⟦F⟧ B) :=
    match F with
    | identityFunctor => id
    | G |∘| F'        => polynomialFunctorMap _ ∘ polynomialFunctorMap _
    | _               => fun f =>
        bimap (polynomialFunctorMap _ f) (polynomialFunctorMap _ f)
    end.

  Instance polynomialFunctor F : Functor ⟦F⟧ := {
    fmap := @polynomialFunctorMap F
  }.

  Reserved Notation "⟬ F ⟭".

  Fixpoint generalisedDenotation F : Type -> Type :=
    match F with
    | identityFunctor => id
    | F' |*| G        => fun A => ⟬F'⟭ A × ⟬G⟭ A
    | F' |+| G        => fun A => ⟬F'⟭ A × ⟬G⟭ A
    | G  |∘| F'       => ⟬G⟭ ∘ ⟬F'⟭
    end
  where "⟬ F ⟭" := (generalisedDenotation F).

  Instance generalisedPolynomialFunctor F : Functor ⟬F⟭ := {
    fmap := (fix fmap'' F' A B : (A -> B) -> (⟬F'⟭ A -> ⟬F'⟭ B) :=
      match F' with
      | identityFunctor => id
      | G |∘| F''       => fmap'' _ _ _ ∘ fmap'' _ _ _
      | _               => fun f => bimap (fmap'' _ _ _ f) (fmap'' _ _ _ f)
      end) F
  }.

  Fixpoint α F A : ⟦F⟧ A -> ⟬F⟭ A :=
    match F with
    | identityFunctor => id
    | F' |*| G        => partialProduct ∘ inl ∘ bimap (α _ _) (α _ _)
    | F' |+| G        => partialProduct ∘ inr ∘ bimap (α _ _) (α _ _)
    | G  |∘| F'       => α _ _ ∘ fmap (α _ _)
    end.

  Notation "!" := (fun _ => None).

  Theorem optionPreservesIdentities : forall A, option_map id = @id (option A).
    crush.
  Qed.

  Theorem optionPreservesComposition
      : forall A B C (f : A -> B) (g : B -> C)
      , option_map (g ∘ f) = option_map g ∘ option_map f.
    crush.
  Qed.

  Notation η := Some.

  Definition μ A (ooa : option (option A)) : option A :=
    match ooa with
    | Some oa => oa
    | None    => None
    end.

  Definition bind A B (oa : option A) (f : A -> option B) : option B :=
    μ (option_map f oa).
  Infix ">>=" := bind (at level 80).

  Definition pairOption A B : option A * option B -> option (A * B) :=
    fun '(oa, ob) =>
      oa >>= fun a =>
      ob >>= fun b =>
      η (a, b).

  Fixpoint sequence F A : ⟦F⟧ (option A) -> option (⟦F⟧ A) :=
    match F with
    | identityFunctor => id
    | F' |*| G        => pairOption ∘ bimap (sequence F' _) (sequence G _)
    | F' |+| G        =>
        option_map inl ∘ sequence F' _
        ||| option_map inr ∘ sequence G _
    | G  |∘| F'       => sequence G _ ∘ fmap (sequence F' _)
    end.

  Theorem optionCoherenceLaw11 : forall A, μ ∘ @η (option A) = μ ∘ option_map η.
    crush.
  Qed.

  Theorem optionCoherenceLaw12 : forall A, μ ∘ option_map η = @id (option A).
    crush.
  Qed.

  Theorem optionCoherenceLaw2 : forall A, μ ∘ @μ (option A) = μ ∘ option_map μ.
    crush.
  Qed.

  Theorem unitNaturality : forall A B (f : A -> B), option_map f ∘ η = η ∘ f.
    reflexivity.
  Qed.

  (* μNaturality and ηNaturality maybe more fitting names *)
  Theorem multiplicationNaturality
      : forall A B (f : A -> B)
      , μ ∘ option_map (option_map f) = option_map f ∘ μ.
    crush.
  Qed.

  (* Morphisms of the following form are called Kleisli morphisms. *)
  Notation "A ⇸ B" :=
    (A -> option B) (at level 99, right associativity, B at level 200).

  (* Kleisli composition. *)
  Definition compose' A B C (g : B ⇸ C) (f : A ⇸ B) : A ⇸ C :=
    μ ∘ option_map g ∘ f.
  Infix "∘'" := compose' (at level 40).

  Theorem compositionAssociativity'
      : forall A B C D (f : A ⇸ B) (g : B ⇸ C) (h : C ⇸ D)
      , (h ∘' g) ∘' f = h ∘' (g ∘' f).
    intros.
    unfold "_ ∘' _".
    repeat rewrite optionPreservesComposition.
    change (?p ∘ (?k ∘ ?h ∘ ?g) ∘ ?f) with ((p ∘ k) ∘ h ∘ g ∘ f).
    rewrite <- optionCoherenceLaw2.
    change (?p ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (p ∘ (k ∘ h) ∘ g ∘ f).
    rewrite multiplicationNaturality.
    reflexivity.
  Qed.

  Theorem compositionLeftUnitLaw' : forall A B (f : A ⇸ B), η ∘' f = f.
    intros.
    unfold "_ ∘' _".
    rewrite optionCoherenceLaw12.
    apply compose_id_left.
  Qed.

  Theorem compositionRightUnitLaw' : forall A B (f : A ⇸ B), f ∘' η = f.
    reflexivity.
  Qed.

  Class Functor' F := {
    fmap' : forall A B, (A ⇸ B) -> (F A ⇸ F B)
  }.

  Class Bifunctor' F := {
    bimap' : forall A A' B B', (A ⇸ A') -> (B ⇸ B') -> (F A B ⇸ F A' B')
  }.

  Definition fst'' A B : A × B ⇸ A := fun pp =>
    match pp with
    | inlp a   => η a
    | midp a _ => η a
    | _        => None
    end.

  Definition snd'' A B : A × B ⇸ B := fun pp =>
    match pp with
    | inrp   b => η b
    | midp _ b => η b
    | _        => None
    end.

  Definition pair'' A B C (f : C ⇸ A) (g : C ⇸ B) : C ⇸ A × B := fun c =>
    match f c, g c with
    | Some a, None   => η (inlp a)
    | Some a, Some b => η (midp a b)
    | None  , Some b => η (inrp b)
    | None  , None   => None
    end.
  Infix "&&&'" := pair'' (at level 50).

  Instance partialProductBifunctor' : Bifunctor' partialProd := {
    bimap' _ _ _ _ f g := f ∘' fst'' &&&' g ∘' snd''
  }.

  Fixpoint αLeftInverse F A : ⟬F⟭ A ⇸ ⟦F⟧ A :=
    match F return ⟬F⟭ A ⇸ ⟦F⟧ A with
    | identityFunctor => η
    | F' |*| G        =>
        (η ||| !)
        ∘' (η ∘ partialProductInverse)
        ∘' bimap' (αLeftInverse _ _) (αLeftInverse _ _)
    | F' |+| G        =>
        (! ||| η)
        ∘' (η ∘ partialProductInverse)
        ∘' bimap' (αLeftInverse _ _) (αLeftInverse _ _)
    | G  |∘| F'       =>
        sequence G _
        ∘' αLeftInverse _ _
        ∘ fmap (αLeftInverse _ _)
    end.

  Theorem αLeftInverseIsARetractionOfα
      : forall F A, αLeftInverse F A ∘ α _ _ = η.
  Admitted.

  Theorem partialProductUniversalProperty
      : forall A B C (f : C ⇸ A) (g : C ⇸ B) (h : C ⇸ A × B)
      , h = f &&&' g <-> fst'' ∘' h = f /\ snd'' ∘' h = g.
    unfold "_ &&&' _", "_ ∘' _", "_ ∘ _".
    split
      ; [intros ->; split | intros [<- <-]]
      ; extensionality c
      ; tryif case (h c) then try destruct p else (case (f c); case (g c))
      ; reflexivity.
  Qed.

  Corollary partialProductCancellationLaw1
      : forall A B C (f : C ⇸ A) (g : C ⇸ B), fst'' ∘' (f &&&' g) = f.
    intros; eapply partialProductUniversalProperty; reflexivity.
  Qed.

  Corollary partialProductCancellationLaw2
      : forall A B C (f : C ⇸ A) (g : C ⇸ B), snd'' ∘' (f &&&' g) = g.
    intros; eapply partialProductUniversalProperty; reflexivity.
  Qed.

  Corollary partialProductReflectionLaw
      : forall A B, @η (A × B) = fst'' &&&' snd''.
    intros; apply partialProductUniversalProperty; auto.
  Qed.

  Corollary partialProductFusionLaw
      : forall A B C C' (h : C' ⇸ C) (f : C ⇸ A) (g : C ⇸ B)
      , (f &&&' g) ∘' h = f ∘' h &&&' g ∘' h.
    intros.
    apply partialProductUniversalProperty.
    split; rewrite <- compositionAssociativity';
      [ rewrite partialProductCancellationLaw1
      | rewrite partialProductCancellationLaw2
      ]; reflexivity.
  Qed.

  Theorem partialProductAbsorptionLaw
      : forall A A' B B' C (h : C ⇸ A) (f : A ⇸ A') (k : C ⇸ B) (g : B ⇸ B')
      , bimap' f g ∘' (h &&&' k) = f ∘' h &&&' g ∘' k.
    intros.
    unfold bimap', partialProductBifunctor'.
    rewrite partialProductFusionLaw.
    rewrite compositionAssociativity'; rewrite partialProductCancellationLaw1.
    rewrite compositionAssociativity'; rewrite partialProductCancellationLaw2.
    reflexivity.
  Qed.

  Theorem partialProductPreservesIdentities
      : forall A B
      , bimap' η η = @η (A × B).
    intros.
    cbn [bimap' partialProductBifunctor'].
    repeat rewrite compositionLeftUnitLaw'.
    symmetry; apply partialProductReflectionLaw.
  Qed.

  Corollary partialProductPreservesComposition
      : forall A A' A'' B B' B''
        (f : A ⇸ A') (f' : A' ⇸ A'')
        (g : B ⇸ B') (g' : B' ⇸ B'')
      , bimap' (f' ∘' f) (g' ∘' g) = bimap' f' g' ∘' bimap' f g.
    intros.
    unfold bimap' at 1, partialProductBifunctor' at 1.
    repeat rewrite compositionAssociativity'.
    symmetry; apply partialProductAbsorptionLaw.
  Qed.

  Instance generalisedPolynomialFunctor' F : Functor' ⟬F⟭ := {
    fmap' := (fix fmap'' F' A B : (A ⇸ B) -> (⟬F'⟭ A ⇸ ⟬F'⟭ B) :=
      match F' return (A ⇸ B) -> (⟬F'⟭ A ⇸ ⟬F'⟭ B) with
      | identityFunctor => id
      | G |∘| F''       => fmap'' _ _ _ ∘ fmap'' _ _ _
      | _               => fun f => bimap' (fmap'' _ _ _ f) (fmap'' _ _ _ f)
      end) F
  }.

  Ltac unfoldSingleFmap' :=
    match goal with
    | |- context G [fmap' (F := ⟬?F⟭) ?f] =>
        let g :=
          match F with
          | identityFunctor => f
          | _ |∘| _         => constr:(fmap' (fmap' f))
          | _               => constr:(bimap' (fmap' f) (fmap' f))
          end
        in let t := context G [g] in change t
    end.

  Theorem generalisedPolynomialFunctorsPreserveIdentities'
      : forall F A
      , fmap' (F := ⟬F⟭) η = @η (⟬F⟭ A).
    induction F
    ; intros
    ; repeat unfoldSingleFmap'
    ; try rewrite IHF2; try rewrite IHF1
    ; (reflexivity || apply partialProductPreservesIdentities).
  Qed.

  Theorem generalisedPolynomialFunctorsPreserveComposition'
      : forall F A B C (f : A ⇸ B) (g : B ⇸ C)
      , fmap' (F := ⟬F⟭) (g ∘' f) = fmap' g ∘' fmap' f.
    induction F
    ; intros
    ; repeat unfoldSingleFmap'
    ; try rewrite IHF2; try rewrite IHF1
    ; (reflexivity || apply partialProductPreservesComposition).
  Qed.
End CategoryTheory.
