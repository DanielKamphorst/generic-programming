Require Import Program.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module Export CategoryTheory.
  Class Functor F := {
    fmap : forall A B, (A -> B) -> (F A -> F B)
  }.

  Instance optionFunctor : Functor option := { fmap := option_map }.

  Ltac crush :=
    let x := fresh "x" in intros; extensionality x; destruct x; reflexivity.

  Theorem optionPreservesIdentities : forall A, option_map id = @id (option A).
    crush.
  Qed.

  Theorem optionPreservesComposition
      : forall A B C (f : A -> B) (g : B -> C)
      , option_map (g ∘ f) = option_map g ∘ option_map f.
    crush.
  Qed.

  (* The unit η of option. *)
  Notation pure := Some.

  (* The multiplication μ. *)
  Definition join A (ooa : option (option A)) : option A :=
    match ooa with
    | Some oa => oa
    | None    => None
    end.

  Theorem pureNaturality 
      : forall A B (f : A -> B), pure ∘ f = option_map f ∘ pure.
    reflexivity.
  Qed.

  Theorem joinNaturality
      : forall A B (f : A -> B)
      , join ∘ option_map (option_map f) = option_map f ∘ join.
    crush.
  Qed.

  Theorem monadCoherenceLaw11
      : forall A, join ∘ @pure (option A) = join ∘ option_map pure.
    crush.
  Qed.

  Theorem monadCoherenceLaw12
      : forall A, join ∘ option_map pure = @id (option A).
    crush.
  Qed.

  Theorem monadCoherenceLaw2
      : forall A, join ∘ @join (option A) = join ∘ option_map join.
    crush.
  Qed.

  (* Morphisms of the following form are called Kleisli morphisms. *)
  Notation "A ⇸ B" :=
    (A -> option B)
    (at level 99, right associativity, B at level 200).

  (* Kleisli composition. *)
  Definition compose' A B C (g : B ⇸ C) (f : A ⇸ B) : A ⇸ C :=
    join ∘ option_map g ∘ f.
  Infix "∘'" := compose' (at level 40).

  Theorem compositionAssociativity'
      : forall A B C D (f : A ⇸ B) (g : B ⇸ C) (h : C ⇸ D)
      , (h ∘' g) ∘' f = h ∘' (g ∘' f).
    intros.
    unfold "_ ∘' _".
    repeat rewrite optionPreservesComposition.
    change (?p ∘ (?k ∘ ?h ∘ ?g) ∘ ?f) with ((p ∘ k) ∘ h ∘ g ∘ f).
    rewrite <- monadCoherenceLaw2.
    change (?p ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (p ∘ (k ∘ h) ∘ g ∘ f).
    rewrite joinNaturality.
    reflexivity.
  Qed.

  Theorem compositionLeftUnitLaw' : forall A B (f : A ⇸ B), pure ∘' f = f.
    intros.
    unfold "_ ∘' _".
    rewrite monadCoherenceLaw12.
    apply compose_id_left.
  Qed.

  Theorem compositionRightUnitLaw' : forall A B (f : A ⇸ B), f ∘' pure = f.
    reflexivity.
  Qed.

  Class Functor' F := {
    fmap' : forall A B, (A ⇸ B) -> (F A ⇸ F B)
  }.

  Class Bifunctor' F := {
    bimap' : forall A A' B B', (A ⇸ A') -> (B ⇸ B') -> (F A B ⇸ F A' B')
  }.

  Reserved Notation "A × B" (at level 40).

  Inductive prod' A B : Type :=
    | inlp : A      -> A × B
    | midp : A -> B -> A × B
    | inrp :      B -> A × B
  where "A × B" := (prod' A B).

  Definition fst' A B : A × B ⇸ A := fun p =>
    match p with
    | inlp a   => Some a
    | midp a _ => Some a
    | _        => None
    end.

  Definition snd' A B : A × B ⇸ B := fun p =>
    match p with
    | inrp   b => Some b
    | midp _ b => Some b
    | _        => None
    end.

  Definition pair' A B C (f : C ⇸ A) (g : C ⇸ B) : C ⇸ A × B := fun c =>
    match f c, g c with
    | Some a, None   => Some (inlp a)
    | Some a, Some b => Some (midp a b)
    | None  , Some b => Some (inrp b)
    | None  , None   => None
    end.
  Infix "&&&" := pair' (at level 50).

  Definition inl' A B : A ⇸ A + B := pure ∘ inl.
  Definition inr' A B : B ⇸ A + B := pure ∘ inr.

  Definition copair A B C (f : A ⇸ C) (g : B ⇸ C) : A + B ⇸ C := fun cp =>
    match cp with
    | inl a => f a
    | inr b => g b
    end.
  Infix "|||" := copair (at level 60).

  Instance productBifunctor' : Bifunctor' prod' := {
    bimap' _ _ _ _ f g := f ∘' fst' &&& g ∘' snd'
  }.

  Instance coproductBifunctor' : Bifunctor' sum := {
    bimap' _ _ _ _ f g := inl' ∘' f ||| inr' ∘' g
  }.

  Theorem productUniversalProperty
      : forall A B C (f : C ⇸ A) (g : C ⇸ B) (h : C ⇸ A × B)
      , h = f &&& g <-> fst' ∘' h = f /\ snd' ∘' h = g.
    split
      ; [intros ->; split | intros [<- <-]]
      ; extensionality c
      ; unfold "_ &&& _", "_ ∘' _", "_ ∘ _"
      ; (case (f c); case (g c)) || (case (h c); try destruct p)
      ; reflexivity.
  Qed.

  Theorem coproductUniversalProperty
      : forall A B C (f : A ⇸ C) (g : B ⇸ C) (h : A + B ⇸ C)
      , h = f ||| g <-> h ∘' inl' = f /\ h ∘' inr' = g.
    split; [intros -> | intros [<- <-]; extensionality cp; destruct cp]; auto.
  Qed.

  Corollary productCancellationLaw1
      : forall A B C (f : C ⇸ A) (g : C ⇸ B), fst' ∘' (f &&& g) = f.
    intros; eapply productUniversalProperty; reflexivity.
  Qed.

  Corollary productCancellationLaw2
      : forall A B C (f : C ⇸ A) (g : C ⇸ B), snd' ∘' (f &&& g) = g.
    intros; eapply productUniversalProperty; reflexivity.
  Qed.

  Corollary coproductCancellationLaw1
      : forall A B C (f : A ⇸ C) (g : B ⇸ C), (f ||| g) ∘' inl' = f.
    intros; eapply coproductUniversalProperty; reflexivity.
  Qed.

  Corollary coproductCancellationLaw2
      : forall A B C (f : A ⇸ C) (g : B ⇸ C), (f ||| g) ∘' inr' = g.
    intros; eapply coproductUniversalProperty; reflexivity.
  Qed.

  Corollary productReflectionLaw : forall A B, @pure (A × B) = fst' &&& snd'.
    intros; apply productUniversalProperty; auto.
  Qed.

  Corollary coproductReflectionLaw : forall A B, @pure (A + B) = inl' ||| inr'.
    intros; apply coproductUniversalProperty; auto.
  Qed.

  Corollary productFusionLaw
      : forall A B C C' (h : C' ⇸ C) (f : C ⇸ A) (g : C ⇸ B)
      , (f &&& g) ∘' h = f ∘' h &&& g ∘' h.
    intros.
    apply productUniversalProperty.
    split; rewrite <- compositionAssociativity'; 
      [ rewrite productCancellationLaw1
      | rewrite productCancellationLaw2
      ]; reflexivity.
  Qed.

  Corollary coproductFusionLaw
      : forall A B C C' (f : A ⇸ C) (g : B ⇸ C) (h : C ⇸ C')
      , h ∘' (f ||| g) = h ∘' f ||| h ∘' g.
    intros.
    apply coproductUniversalProperty.
    split; rewrite compositionAssociativity'; 
      [ rewrite coproductCancellationLaw1
      | rewrite coproductCancellationLaw2
      ]; reflexivity.
  Qed.

  Theorem productAbsorptionLaw
      : forall A A' B B' C (h : C ⇸ A) (f : A ⇸ A') (k : C ⇸ B) (g : B ⇸ B')
      , bimap' f g ∘' (h &&& k) = f ∘' h &&& g ∘' k.
    intros.
    unfold bimap', productBifunctor'.
    rewrite productFusionLaw.
    rewrite compositionAssociativity'; rewrite productCancellationLaw1.
    rewrite compositionAssociativity'; rewrite productCancellationLaw2.
    reflexivity.
  Qed.

  Theorem coproductAbsorptionLaw
      : forall A A' B B' C (f : A' ⇸ A) (h : A ⇸ C) (g : B' ⇸ B) (k : B ⇸ C)
      , (h ||| k) ∘' bimap' f g = h ∘' f ||| k ∘' g.
    intros.
    unfold bimap', coproductBifunctor'.
    rewrite coproductFusionLaw.
    rewrite <- compositionAssociativity'; rewrite coproductCancellationLaw1.
    rewrite <- compositionAssociativity'; rewrite coproductCancellationLaw2.
    reflexivity.
  Qed.

  Theorem productPreservesIdentities
      : forall A B, bimap' pure pure = @pure (A × B).
    intros.
    unfold bimap', productBifunctor'.
    repeat rewrite compositionLeftUnitLaw'.
    symmetry; apply productReflectionLaw.
  Qed.

  Theorem coproductPreservesIdentities
      : forall A B, bimap' pure pure = @pure (A + B).
    intros.
    unfold bimap', coproductBifunctor'.
    repeat rewrite compositionRightUnitLaw'.
    symmetry; apply coproductReflectionLaw.
  Qed.

  Corollary productPreservesComposition
      : forall A A' A'' B B' B''
        (f : A ⇸ A') (f' : A' ⇸ A'')
        (g : B ⇸ B') (g' : B' ⇸ B'')
      , bimap' (F := prod') (f' ∘' f) (g' ∘' g) = bimap' f' g' ∘' bimap' f g.
    intros.
    unfold bimap' at 1, productBifunctor' at 1.
    repeat rewrite compositionAssociativity'.
    symmetry; apply productAbsorptionLaw.
  Qed.

  Corollary coproductPreservesComposition
      : forall A A' A'' B B' B''
        (f' : A'' ⇸ A') (f : A' ⇸ A)
        (g' : B'' ⇸ B') (g : B' ⇸ B)
      , bimap' (F := sum) (f ∘' f') (g ∘' g') = bimap' f g ∘' bimap' f' g'.
    intros.
    unfold bimap' at 1, coproductBifunctor' at 1.
    repeat rewrite <- compositionAssociativity'.
    symmetry; apply coproductAbsorptionLaw.
  Qed.

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

  Infix "|×|" := product (at level 40).
  Infix "|+|" := coproduct (at level 50).
  Infix "|∘|" := composite (at level 40).

  Reserved Notation "⟦ F ⟧".

  Fixpoint denotation F : Type -> Type :=
    match F with
    | identityFunctor => id
    | F' |×| G        => fun A => ⟦F'⟧ A × ⟦G⟧ A
    | F' |+| G        => fun A => (⟦F'⟧ A + ⟦G⟧ A) % type
    | G  |∘| F'       => ⟦G⟧ ∘ ⟦F'⟧
    end
  where "⟦ F ⟧" := (denotation F).

  Instance polynomialFunctor' F : Functor' ⟦F⟧ := {
    fmap' := (fix fmap'' F' A B : (A ⇸ B) -> (⟦F'⟧ A ⇸ ⟦F'⟧ B) :=
      match F' with
      | identityFunctor => id
      | G |∘| F''       => fmap'' _ _ _ ∘ fmap'' _ _ _
      | _               => fun f => bimap' (fmap'' _ _ _ f) (fmap'' _ _ _ f)
      end) F
  }.

  Ltac unfoldSingleFmap' :=
    match goal with
    | |- context G [fmap' (F := ⟦?F⟧) ?f] =>
        let g :=
          match F with
          | identityFunctor => f
          | _ |×| _         => constr:(bimap' (F := prod') (fmap' f) (fmap' f))
          | _ |+| _         => constr:(bimap' (F := sum)   (fmap' f) (fmap' f))
          | _ |∘| _         => constr:(fmap' (fmap' f))
          end
        in let t := context G [g] in change t
    end.

  Lemma polynomialFunctorsPreserveIdentities1
      : forall F G
      , (forall A, fmap' (F := ⟦F⟧) pure = @pure (⟦F⟧ A))
      -> (forall A, fmap' (F := ⟦G⟧) pure = @pure (⟦G⟧ A))
      -> forall A, fmap' (F := ⟦F |×| G⟧) pure = @pure (⟦F |×| G⟧ A).
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; rewrite H2.
    apply productPreservesIdentities.
  Qed.
    
  Lemma polynomialFunctorsPreserveIdentities2
      : forall F G
      , (forall A, fmap' (F := ⟦F⟧) pure = @pure (⟦F⟧ A))
      -> (forall A, fmap' (F := ⟦G⟧) pure = @pure (⟦G⟧ A))
      -> forall A, fmap' (F := ⟦F |+| G⟧) pure = @pure (⟦F |+| G⟧ A).
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; rewrite H2.
    apply coproductPreservesIdentities.
  Qed.
    
  Lemma polynomialFunctorsPreserveIdentities3
      : forall F G
      , (forall A, fmap' (F := ⟦F⟧) pure = @pure (⟦F⟧ A))
      -> (forall A, fmap' (F := ⟦G⟧) pure = @pure (⟦G⟧ A))
      -> forall A, fmap' (F := ⟦G |∘| F⟧) pure = @pure (⟦G |∘| F⟧ A).
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; apply H2.
  Qed.
    
  Theorem polynomialFunctorsPreserveIdentities 
      : forall F A, fmap' (F := ⟦F⟧) pure = @pure (⟦F⟧ A).
    induction F.
    reflexivity.
    apply polynomialFunctorsPreserveIdentities1; assumption.
    apply polynomialFunctorsPreserveIdentities2; assumption.
    apply polynomialFunctorsPreserveIdentities3; assumption.
  Qed.
   
  Lemma polynomialFunctorsPreserveComposition1
      : forall F G
      , (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦F⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦G⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦F |×| G⟧) (g ∘' f) = fmap' g ∘' fmap' f.
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; rewrite H2.
    apply productPreservesComposition.
  Qed.

  Lemma polynomialFunctorsPreserveComposition2
      : forall F G
      , (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦F⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦G⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦F |+| G⟧) (g ∘' f) = fmap' g ∘' fmap' f.
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; rewrite H2.
    apply coproductPreservesComposition.
  Qed.

  Lemma polynomialFunctorsPreserveComposition3
      : forall F G
      , (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦F⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> (forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦G⟧) (g ∘' f) = fmap' g ∘' fmap' f)
      -> forall A B C (f : A ⇸ B) (g : B ⇸ C)
        , fmap' (F := ⟦G |∘| F⟧) (g ∘' f) = fmap' g ∘' fmap' f.
    intros * H1 H2 *.
    unfoldSingleFmap'.
    rewrite H1; apply H2.
  Qed.

  Theorem polynomialFunctorsPreserveComposition
      : forall F A B C (f : A ⇸ B) (g : B ⇸ C)
      , fmap' (F := ⟦F⟧) (g ∘' f) = fmap' g ∘' fmap' f.
    induction F.
    reflexivity.
    apply polynomialFunctorsPreserveComposition1; assumption.
    apply polynomialFunctorsPreserveComposition2; assumption.
    apply polynomialFunctorsPreserveComposition3; assumption.
  Qed.
End CategoryTheory.
