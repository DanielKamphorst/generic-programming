Require Import FunctionalExtensionality Program.

Set Implicit Arguments.

Module Export CategoryTheory.
  Class Functor (F : Type -> Type) := {
    fmap : forall A B, (A -> B) -> (F A -> F B)
  }.

  Class Bifunctor (F : Type -> Type -> Type) := {
    bimap : forall A A' B B', (A -> A') -> (B -> B') -> (F A B -> F A' B')
  }.

  Open Scope type_scope.

  Definition pairing A B C (f : C -> A) (g : C -> B) : C -> A * B :=
    fun c => (f c, g c).
  Infix "&&&" := pairing (at level 50).

  Definition copairing A B C (f : A -> C) (g : B -> C) : A + B -> C :=
    fun cp =>
      match cp with
      | inl a => f a
      | inr b => g b
      end.
  Infix "|||" := copairing (at level 60).

  Notation curry := prod_uncurry.
  Notation uncurry := prod_curry.

  Instance productBifunctor : Bifunctor prod := {
    bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.

  Instance coproductBifunctor : Bifunctor sum := {
    bimap _ _ _ _ f g := inl ∘ f ||| inr ∘ g
  }.

  Theorem universalPropertyOfProduct
      : forall A B C (f : C -> A) (g : C -> B) (h : C -> A * B)
      , h = f &&& g <-> fst ∘ h = f /\ snd ∘ h = g.
    split
      ; [ intros ->
        | intros [<- <-]; extensionality c; apply injective_projections
        ]
      ; auto.
  Qed.

  Theorem universalPropertyOfCoproduct
      : forall A B C (f : A -> C) (g : B -> C) (h : A + B -> C)
      , h = f ||| g <-> h ∘ inl = f /\ h ∘ inr = g.
    split
      ; [ intros ->
        | intros [<- <-]; extensionality cp; destruct cp
        ]
      ; auto.
  Qed.

  Corollary cancellationLawForProducts1
      : forall A B C (f : C -> A) (g : C -> B)
      , fst ∘ (f &&& g) = f.
    intros; eapply universalPropertyOfProduct; auto.
  Qed.

  Corollary cancellationLawForProducts2
      : forall A B C (f : C -> A) (g : C -> B)
      , snd ∘ (f &&& g) = g.
    intros; eapply universalPropertyOfProduct; auto.
  Qed.

  Corollary cancellationLawForCoproducts1
      : forall A B C (f : A -> C) (g : B -> C)
      , (f ||| g) ∘ inl = f.
    intros; eapply universalPropertyOfCoproduct; auto.
  Qed.

  Corollary cancellationLawForCoproducts2
      : forall A B C (f : A -> C) (g : B -> C)
      , (f ||| g) ∘ inr = g.
    intros; eapply universalPropertyOfCoproduct; auto.
  Qed.

  Corollary reflectionLawForProducts : forall A B, @id (A * B) = fst &&& snd.
    intros; apply universalPropertyOfProduct; auto.
  Qed.

  Corollary reflectionLawForCoproducts : forall A B, @id (A + B) = inl ||| inr.
    intros; apply universalPropertyOfCoproduct; auto.
  Qed.

  Corollary fusionLawForProducts
      : forall A B C C' (f : C -> A) (g : C -> B) (h : C' -> C)
      , (f &&& g) ∘ h = f ∘ h &&& g ∘ h.
    intros.
    apply universalPropertyOfProduct.
    repeat rewrite <- compose_assoc.
    rewrite cancellationLawForProducts1; rewrite cancellationLawForProducts2.
    split; reflexivity.
  Qed.

  Corollary fusionLawForCoproducts
      : forall A B C C' (f : A -> C) (g : B -> C) (h : C -> C')
      , h ∘ (f ||| g) = h ∘ f ||| h ∘ g.
    intros.
    apply universalPropertyOfCoproduct.
    repeat rewrite compose_assoc.
    rewrite cancellationLawForCoproducts1.
    rewrite cancellationLawForCoproducts2.
    split; reflexivity.
  Qed.

  Theorem absorptionLawForProducts 
      : forall A A' B B' C (f : A -> A') (g : B -> B') (p : C -> A) (q : C -> B)
      , bimap f g ∘ (p &&& q) = f ∘ p &&& g ∘ q.
    intros.
    unfold bimap, productBifunctor.
    rewrite fusionLawForProducts.
    repeat rewrite compose_assoc.
    rewrite cancellationLawForProducts1; rewrite cancellationLawForProducts2.
    reflexivity.
  Qed.

  Theorem absorptionLawForCoproducts 
      : forall A A' B B' C (f : A' -> A) (g : B' -> B) (p : A -> C) (q : B -> C)
      , (p ||| q) ∘ bimap f g = p ∘ f ||| q ∘ g.
    intros.
    unfold bimap, coproductBifunctor.
    rewrite fusionLawForCoproducts.
    repeat rewrite <- compose_assoc.
    rewrite cancellationLawForCoproducts1.
    rewrite cancellationLawForCoproducts2.
    reflexivity.
  Qed.

  Theorem productPreservesIdentities 
      : forall A B
      , bimap (F := prod) (@id A) (@id B) = id.
    intros.
    unfold bimap, productBifunctor.
    repeat rewrite compose_id_left.
    symmetry.
    apply reflectionLawForProducts.
  Qed.

  Corollary productPreservesComposition 
      : forall A A' A'' B B' B'' 
        (f : A -> A') 
        (f' : A' -> A'') 
        (g : B -> B') 
        (g' : B' -> B'')
      , bimap (F := prod) (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
    intros; apply absorptionLawForProducts.
  Qed.

  Theorem coproductPreservesIdentities 
      : forall A B
      , bimap (F := sum) (@id A) (@id B) = id.
    intros.
    unfold bimap, coproductBifunctor.
    repeat rewrite compose_id_right.
    symmetry.
    apply reflectionLawForCoproducts.
  Qed.

  Corollary coproductPreservesComposition 
      : forall A A' A'' B B' B'' 
        (f : A' -> A) 
        (f' : A'' -> A') 
        (g : B' -> B) 
        (g' : B'' -> B')
      , bimap (F := sum) (f ∘ f') (g ∘ g') = bimap f g ∘ bimap f' g'.
    symmetry; apply absorptionLawForCoproducts.
  Qed.
End CategoryTheory.
