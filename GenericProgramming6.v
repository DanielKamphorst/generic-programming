Require Import FunctionalExtensionality Program.

Set Asymmetric Patterns.
Set Implicit Arguments.

(* A subset of the endofunctors from Set to Set. *)
Inductive functor : Set := 
  | idSet : functor
  | product : functor -> functor -> functor
  | composition : functor -> functor -> functor.

Infix "|*|" := product (at level 40).
Infix "|∘|" := composition (at level 40).
Reserved Notation "⟦ F ⟧".

Open Scope type_scope.

Fixpoint evaluate (F : functor) : Set -> Set := 
  match F with
  | idSet     => id
  | F' |*| G  => fun A => ⟦F'⟧ A * ⟦G⟧ A
  | G  |∘| F' => ⟦G⟧ ∘ ⟦F'⟧
  end
where "⟦ F ⟧" := (evaluate F).

(* The universal property of product. *)
Definition pair' (A B C : Set) (f : C -> A) (g : C -> B) : C -> A * B := 
  fun c => (f c, g c).
Infix "&&&" := pair' (at level 60).

Notation curry := prod_uncurry.
Notation uncurry := prod_curry.

Class Functor (F : Set -> Set) := 
  fmap : forall A B : Set, (A -> B) -> (F A -> F B).

Class Bifunctor (F : Set -> Set -> Set) := 
  bimap 
    : forall A A' B B' : Set
    , (A -> A') -> (B -> B') -> (F A B -> F A' B').

Instance productBifunctor : Bifunctor prod := 
  { bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.

Instance evaluatedFunctor (F : functor) : Functor ⟦F⟧ := 
  { fmap := 
      let fix fmap' (F' : functor) (A B : Set) 
          : (A -> B) -> (⟦F'⟧ A -> ⟦F'⟧ B) :=
        match F' with
        | idSet       => id
        | F'' |*| G   => fun f => bimap (fmap' _ _ _ f) (fmap' _ _ _ f)
        | G   |∘| F'' => fmap' _ _ _ ∘ fmap' _ _ _
        end
      in fmap' F
  }.

Theorem cancellationProperty1 
    : forall (A B C : Set) (f : C -> A) (g : C -> B)
    , fst ∘ (f &&& g) = f.
  reflexivity.
Qed.

Theorem cancellationProperty2 
    : forall (A B C : Set) (f : C -> A) (g : C -> B)
    , snd ∘ (f &&& g) = g.
  reflexivity.
Qed.

Theorem reflectionLaw : forall A B : Set, fst &&& snd = @id (A * B).
  intros.
  extensionality p; destruct p.
  reflexivity.
Qed.

Theorem fusionLaw 
    : forall (A B C C' : Set) (h : C' -> C) (f : C -> A) (g : C -> B)
    , (f &&& g) ∘ h = f ∘ h &&& g ∘ h.
  reflexivity.
Qed.

Theorem absorptionLaw 
    : forall 
      (A A' B B' C : Set) 
      (p : C -> A) 
      (q : C -> B) 
      (f : A -> A') 
      (g : B -> B')
    , bimap f g ∘ (p &&& q) = f ∘ p &&& g ∘ q.
  intros.
  unfold bimap, productBifunctor.
  rewrite fusionLaw.
  rewrite compose_assoc; rewrite cancellationProperty1.
  rewrite compose_assoc; rewrite cancellationProperty2.
  reflexivity.
Qed.

Theorem uniquenessOfPairings
    : forall (A B C : Set) (f f' : C -> A) (g g' : C -> B)
    , f' &&& g' = f &&& g <-> f' = f /\ g' = g.
  split.
  intro H.
  rewrite <- cancellationProperty1 with (f := f') (g := g').
  rewrite H.
  rewrite cancellationProperty1.
  rewrite <- cancellationProperty2 with (f := f') (g := g').
  rewrite H.
  rewrite cancellationProperty2.
  auto.
  intros [-> ->]; reflexivity.
Qed.

Theorem productPreservesIdentities 
    : forall A B : Set, bimap (@id A) (@id B) = id.
  intros.
  unfold bimap, productBifunctor.
  repeat rewrite compose_id_left.
  extensionality p; destruct p.
  reflexivity.
Qed.

Corollary productPreservesComposition 
    : forall 
      (A A' A'' B B' B'' : Set) 
      (f : A -> A') 
      (f' : A' -> A'') 
      (g : B -> B') 
      (g' : B' -> B'')
    , bimap (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
  intros.
  apply absorptionLaw.
Qed.

Ltac unfoldSingleFmap :=
  match goal with
  | |- context G [fmap (F := ⟦?F⟧) ?f] => 
      let g :=
        match F with
        | idSet       => f
        | ?F' |*| ?G' => constr:(bimap (fmap f) (fmap f))
        | ?G' |∘| ?F' => constr:(fmap (fmap f))
        end
      in let t := context G [g] in change t
  end.

Lemma evaluatedFunctorsPreserveIdentities1
    : forall F G : functor
    , (forall A : Set, fmap (F := ⟦F⟧) (@id A) = id)
    -> (forall A : Set, fmap (F := ⟦G⟧) (@id A) = id)
    -> forall A : Set, fmap (F := ⟦F |*| G⟧) (@id A) = id.
  intros * H1 H2 *.
  unfoldSingleFmap.
  rewrite H1.
  rewrite H2.
  apply productPreservesIdentities.
Qed.

Lemma evaluatedFunctorsPreserveIdentities2
    : forall F G : functor
    , (forall A : Set, fmap (F := ⟦F⟧) (@id A) = id)
    -> (forall A : Set, fmap (F := ⟦G⟧) (@id A) = id)
    -> forall A : Set, fmap (F := ⟦G |∘| F⟧) (@id A) = id.
  intros * H1 H2 *.
  unfoldSingleFmap.
  rewrite H1.
  apply H2.
Qed.

Theorem evaluatedFunctorsPreserveIdentities 
    : forall (F : functor) (A : Set)
    , fmap (F := ⟦F⟧) (@id A) = id.
  induction F.
  reflexivity.
  apply evaluatedFunctorsPreserveIdentities1; assumption.
  apply evaluatedFunctorsPreserveIdentities2; assumption.
Qed.

Lemma evaluatedFunctorsPreserveComposition1 
    : forall F G : functor
    , (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F |*| G⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  repeat unfoldSingleFmap.
  rewrite H1.
  rewrite H2.
  apply productPreservesComposition.
Qed.

Lemma evaluatedFunctorsPreserveComposition2 
    : forall F G : functor
    , (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G |∘| F⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  repeat unfoldSingleFmap.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Theorem evaluatedFunctorsPreserveComposition 
    : forall (F : functor) (A B C : Set) (f : A -> B) (g : B -> C)
    , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f.
  induction F.
  reflexivity.
  apply evaluatedFunctorsPreserveComposition1; assumption.
  apply evaluatedFunctorsPreserveComposition2; assumption.
Qed.

Fixpoint zip (F : functor) (A B : Set) : ⟦F⟧ A * ⟦F⟧ B -> ⟦F⟧ (A * B) :=
  match F with
  | idSet     => id
  | F' |*| G  => zip F' A B ∘ bimap fst fst &&& zip G A B ∘ bimap snd snd
  | G  |∘| F' => fmap (zip F' A B) ∘ zip G (⟦F'⟧ A) (⟦F'⟧ B)
  end.

Definition zipWith (F : functor) (A B C : Set) (f : A * B -> C) 
    : ⟦F⟧ A * ⟦F⟧ B -> ⟦F⟧ C :=
  fmap f ∘ zip F A B.

Definition zipWith' (F : functor) (A B C : Set) (f : A -> B -> C) 
    : ⟦F⟧ A -> ⟦F⟧ B -> ⟦F⟧ C :=
  curry (zipWith F (uncurry f)).

Definition unzip (F : functor) (A B : Set) : ⟦F⟧ (A * B) -> ⟦F⟧ A * ⟦F⟧ B :=
  fmap fst &&& fmap snd.

Lemma unzipDecomposition 
    : forall (F G : functor) (A B : Set)
    , unzip (G |∘| F) A B = unzip G (⟦F⟧ A) (⟦F⟧ B) ∘ fmap (unzip F A B).
  intros.
  unfold unzip.
  repeat unfoldSingleFmap.
  rewrite fusionLaw.
  repeat rewrite <- evaluatedFunctorsPreserveComposition.
  rewrite cancellationProperty1.
  rewrite cancellationProperty2.
  reflexivity.
Qed.

Lemma zipIsTheInverseOfUnzip1 
    : forall A B : Set
    , zip idSet A B ∘ unzip _ _ _ = id.
  intros.
  simpl.
  rewrite compose_id_left.
  unfold unzip.
  repeat unfoldSingleFmap.
  apply reflectionLaw.
Qed.

Lemma zipIsTheInverseOfUnzip2 
    : forall F G : functor
    , (forall A B : Set, zip F A B ∘ unzip _ _ _ = id)
    -> (forall A B : Set, zip G A B ∘ unzip _ _ _ = id)
    -> forall A B : Set, zip (F |*| G) A B ∘ unzip _ _ _ = id.
  intros * H1 H2 *.
  simpl.
  rewrite fusionLaw.
  unfold unzip.
  repeat unfoldSingleFmap.
  repeat (rewrite compose_assoc; rewrite absorptionLaw).
  unfold bimap, productBifunctor.
  unfold "⟦ _ ⟧".
  repeat rewrite cancellationProperty1.
  repeat rewrite cancellationProperty2.
  repeat rewrite <- fusionLaw.
  repeat rewrite <- compose_assoc.
  rewrite H1.
  rewrite H2.
  repeat rewrite compose_id_left.
  apply reflectionLaw.
Qed.

Lemma zipIsTheInverseOfUnzip3 
    : forall F G : functor
    , (forall A B : Set, zip F A B ∘ unzip _ _ _ = id)
    -> (forall A B : Set, zip G A B ∘ unzip _ _ _ = id)
    -> forall A B : Set, zip (G |∘| F) A B ∘ unzip _ _ _ = id.
  intros * H1 H2 *.
  simpl.
  rewrite unzipDecomposition.
  change ((?k ∘ ?h) ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f).
  rewrite H2.
  rewrite compose_id_right.
  rewrite <- evaluatedFunctorsPreserveComposition.
  rewrite H1.
  apply evaluatedFunctorsPreserveIdentities.
Qed.

Theorem zipIsTheInverseOfUnzip 
    : forall (F : functor) (A B : Set)
    , zip F A B ∘ unzip _ _ _ = id.
  induction F.
  exact zipIsTheInverseOfUnzip1.
  apply zipIsTheInverseOfUnzip2; assumption.
  apply zipIsTheInverseOfUnzip3; assumption.
Qed.

Lemma unzipIsTheInverseOfZip1 
    : forall A B : Set, unzip idSet A B ∘ zip _ _ _ = id.
  intros.
  simpl.
  rewrite compose_id_right.
  unfold unzip.
  repeat unfoldSingleFmap.
  apply reflectionLaw.
Qed.

Lemma unzipIsTheInverseOfZip2 
    : forall F G : functor
    , (forall A B : Set, unzip F A B ∘ zip _ _ _ = id)
    -> (forall A B : Set, unzip G A B ∘ zip _ _ _ = id)
    -> forall A B : Set, unzip (F |*| G) A B ∘ zip _ _ _ = id.
  intros * H1 H2 *.
  specialize (H1 A B); specialize (H2 A B).
  unfold unzip in H1, H2 |- *.
  rewrite fusionLaw in H1, H2 |- *.
  rewrite <- reflectionLaw in H1, H2.
  rewrite uniquenessOfPairings in H1, H2.
  destruct H2 as [H3 H4]; destruct H1 as [H1 H2].

  repeat unfoldSingleFmap.
  simpl.
  repeat rewrite absorptionLaw.
  repeat rewrite <- compose_assoc.
  rewrite H1; rewrite H2; rewrite H3; rewrite H4.

  extensionality p; destruct p as [[fa ga] [fb gb]].
  reflexivity.
Qed.

Lemma unzipIsTheInverseOfZip3 
    : forall F G : functor
    , (forall A B : Set, unzip F A B ∘ zip _ _ _ = id)
    -> (forall A B : Set, unzip G A B ∘ zip _ _ _ = id)
    -> forall A B : Set, unzip (G |∘| F) A B ∘ zip _ _ _ = id.
  intros * H1 H2 *.
  rewrite unzipDecomposition.
  simpl.
  change ((?k ∘ ?h) ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f).
  rewrite <- evaluatedFunctorsPreserveComposition.
  rewrite H1.
  rewrite evaluatedFunctorsPreserveIdentities.
  rewrite compose_id_right.
  apply H2.
Qed.

Theorem unzipIsTheInverseOfZip 
    : forall (F : functor) (A B : Set)
    , unzip F A B ∘ zip _ _ _ = id.
  induction F.
  apply unzipIsTheInverseOfZip1.
  apply unzipIsTheInverseOfZip2; assumption.
  apply unzipIsTheInverseOfZip3; assumption.
Qed.

Theorem zipIsAnIsomorphism 
    : forall (F : functor) (A B : Set)
    , zip F A B ∘ unzip _ _ _ = id /\ unzip _ _ _ ∘ zip F A B = id.
  split; [apply zipIsTheInverseOfUnzip | apply unzipIsTheInverseOfZip].
Qed.
