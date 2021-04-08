Require Import CategoryTheoryLibrary.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Fixpoint zip F A B : ⟦F⟧ A × ⟦F⟧ B ⇸ ⟦F⟧ (A × B) :=
  match F with
  | identityFunctor => pure
  | F' |×| G =>
      zip F' _ _ ∘' bimap' fst' fst'
      &&& zip G _ _ ∘' bimap' snd' snd'
  | F' |+| G => fun p =>
      match p with
      | midp cp1 cp2 =>
          match cp1, cp2 with
          | inl fa, inl fb => option_map inl (zip F' _ _ (midp fa fb))
          | inr ga, inr gb => option_map inr (zip G  _ _ (midp ga gb))
          | _, _           => None
          end
      | _ => None
      end
  | G |∘| F' => fmap' (zip F' _ _) ∘' zip G _ _
  end.

Definition unzip F A B : ⟦F⟧ (A × B) ⇸ ⟦F⟧ A × ⟦F⟧ B :=
  fmap' fst' &&& fmap' snd'.

Lemma unzipDecompositionLaw
    : forall F G A B, unzip (G |∘| F) A B = unzip G _ _ ∘' fmap' (unzip F _ _).
  intros.
  unfold unzip; repeat unfoldSingleFmap'.
  rewrite productFusionLaw.
  repeat rewrite <- polynomialFunctorsPreserveComposition.
  rewrite productCancellationLaw1; rewrite productCancellationLaw2.
  reflexivity.
Qed.

Lemma unzipIsARetractionOfZip1
    : forall A B
    , unzip _ _ _ ∘' zip _ _ _
      = @pure (⟦identityFunctor⟧ A × ⟦identityFunctor⟧ B).
Admitted.

Lemma unzipIsARetractionOfZip2
    : forall F G
    , (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F⟧ A × ⟦F⟧ B))
    -> (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦G⟧ A × ⟦G⟧ B))
    -> forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F |×| G⟧ A × ⟦F |×| G⟧ B).
Admitted.

Lemma unzipIsARetractionOfZip3
    : forall F G
    , (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F⟧ A × ⟦F⟧ B))
    -> (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦G⟧ A × ⟦G⟧ B))
    -> forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F |+| G⟧ A × ⟦F |+| G⟧ B).
Admitted.

Lemma unzipIsARetractionOfZip4
    : forall F G
    , (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F⟧ A × ⟦F⟧ B))
    -> (forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦G⟧ A × ⟦G⟧ B))
    -> forall A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦G |∘| F⟧ A × ⟦G |∘| F⟧ B).
Admitted.

Theorem unzipIsARetractionOfZip
    : forall F A B, unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F⟧ A × ⟦F⟧ B).
Admitted.

Lemma unzipIsASectionOfZip1
    : forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦identityFunctor⟧ (A × B)).
Admitted.

Lemma unzipIsASectionOfZip2
    : forall F G
    , (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F⟧ (A × B)))
    -> (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦G⟧ (A × B)))
    -> forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F |×| G⟧ (A × B)).
Admitted.

Lemma unzipIsASectionOfZip3
    : forall F G
    , (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F⟧ (A × B)))
    -> (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦G⟧ (A × B)))
    -> forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F |+| G⟧ (A × B)).
Admitted.

Lemma unzipIsASectionOfZip4
    : forall F G
    , (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F⟧ (A × B)))
    -> (forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦G⟧ (A × B)))
    -> forall A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦G |∘| F⟧ (A × B)).
Admitted.

Theorem unzipIsASectionOfZip
    : forall F A B, zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F⟧ (A × B)).
Admitted.

Theorem unzipIsAnInverseOfZip
    : forall F A B
    , unzip _ _ _ ∘' zip _ _ _ = @pure (⟦F⟧ A × ⟦F⟧ B)
      /\ zip _ _ _ ∘' unzip _ _ _ = @pure (⟦F⟧ (A × B)).
Admitted.
