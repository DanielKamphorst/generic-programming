Require Import CategoryTheoryLibrary.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Fixpoint generalisedZip' F A B : ⟬F⟭ A × ⟬F⟭ B ⇸ ⟬F⟭ (A × B) :=
  match F with
  | identityFunctor => η
  | G |∘| F'        => fmap' (generalisedZip' F' _ _) ∘' generalisedZip' G _ _
  | _               =>
      generalisedZip' _ _ _ ∘' bimap' fst'' fst''
      &&&' generalisedZip' _ _ _ ∘' bimap' snd'' snd''
  end.

Definition unzip' F A B : ⟬F⟭ (A × B) ⇸ ⟬F⟭ A × ⟬F⟭ B :=
  fmap' fst'' &&&' fmap' snd''.

Lemma unzipDecompositionLaw'
    : forall F G A B
    , unzip' (G |∘| F) A B = unzip' G _ _ ∘' fmap' (unzip' F _ _).
  intros.
  unfold unzip'; repeat unfoldSingleFmap'.
  rewrite partialProductFusionLaw.
  repeat rewrite <- generalisedPolynomialFunctorsPreserveComposition'.
  rewrite partialProductCancellationLaw1
    ; rewrite partialProductCancellationLaw2.
  reflexivity.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip1'
    : forall A B
    , unzip' _ _ _ ∘' generalisedZip' _ _ _
      = @η (⟬identityFunctor⟭ A × ⟬identityFunctor⟭ B).
  intros.
  unfold unzip'; repeat unfoldSingleFmap'; cbn ["⟬ _ ⟭"]; unfold id.
  rewrite <- partialProductReflectionLaw.
  cbn [generalisedZip'].
  apply compositionLeftUnitLaw'.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip2'
    : forall F G
    , (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F |*| G⟭ A × ⟬F |*| G⟭ B).
  unfold unzip'.
  setoid_rewrite partialProductFusionLaw.
  setoid_rewrite partialProductReflectionLaw.
  setoid_rewrite partialProductUniversalProperty.
  setoid_rewrite partialProductCancellationLaw1
    ; setoid_rewrite partialProductCancellationLaw2.
  intros * H1 H2 *.
  repeat unfoldSingleFmap'.
  cbn ["⟬ _ ⟭" generalisedZip'].
  repeat rewrite partialProductAbsorptionLaw.
  repeat rewrite <- compositionAssociativity'.
  destruct H1 with A B as [-> ->]; destruct H2 with A B as [-> ->].
  cbn [bimap' partialProductBifunctor'].
  repeat rewrite partialProductCancellationLaw1
    ; repeat rewrite partialProductCancellationLaw2.
  repeat rewrite <- partialProductFusionLaw.
  repeat rewrite <- partialProductReflectionLaw.
  split; apply compositionLeftUnitLaw'.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip3'
    : forall F G
    , (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F |+| G⟭ A × ⟬F |+| G⟭ B).
  change (?f (?F |+| ?G) ?A ?B) with (f (F |*| G) A B).
  exact @unzipIsARetractionOfGeneralisedZip2'.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip4'
    : forall F G
    , (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G |∘| F⟭ A × ⟬G |∘| F⟭ B).
  intros * H1 H2 *.
  rewrite unzipDecompositionLaw'.
  cbn [generalisedZip'].
  match goal with
  | |- context [(?k ∘' ?h) ∘' (?g ∘' ?f)] => transitivity (k ∘' (h ∘' g) ∘' f)
  end.
  repeat rewrite compositionAssociativity'; reflexivity.
  rewrite <- generalisedPolynomialFunctorsPreserveComposition'.
  rewrite H1.
  rewrite generalisedPolynomialFunctorsPreserveIdentities'.
  rewrite compositionRightUnitLaw'.
  apply H2.
Qed.

Theorem unzipIsARetractionOfGeneralisedZip'
    : forall F A B, unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B).
  induction F; intros;
    [ apply unzipIsARetractionOfGeneralisedZip1'
    | apply unzipIsARetractionOfGeneralisedZip2'
    | apply unzipIsARetractionOfGeneralisedZip3'
    | apply unzipIsARetractionOfGeneralisedZip4'
    ]; assumption.
Qed.

Lemma unzipIsASectionOfGeneralisedZip1'
    : forall A B
    , generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬identityFunctor⟭ (A × B)).
  intros.
  cbn [generalisedZip'].
  rewrite compositionLeftUnitLaw'.
  unfold unzip'; repeat unfoldSingleFmap'.
  symmetry; apply partialProductReflectionLaw.
Qed.

Lemma unzipIsASectionOfGeneralisedZip2'
    : forall F G
    , (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F |*| G⟭ (A × B)).
  intros * H1 H2 *.
  cbn ["⟬ _ ⟭" generalisedZip'].
  rewrite partialProductFusionLaw.
  unfold unzip'; repeat unfoldSingleFmap'.
  repeat
    ( rewrite compositionAssociativity'
    ; rewrite partialProductAbsorptionLaw
    ).
  cbn [bimap' partialProductBifunctor'].
  repeat rewrite partialProductCancellationLaw1
    ; repeat rewrite partialProductCancellationLaw2.
  repeat rewrite <- partialProductFusionLaw.
  repeat rewrite <- compositionAssociativity'; rewrite H1; rewrite H2.
  repeat rewrite compositionLeftUnitLaw'.
  symmetry; apply partialProductReflectionLaw.
Qed.

Lemma unzipIsASectionOfGeneralisedZip3'
    : forall F G
    , (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F |+| G⟭ (A × B)).
  change (?f (?F |+| ?G) ?A ?B) with (f (F |*| G) A B).
  exact @unzipIsASectionOfGeneralisedZip2'.
Qed.

Lemma unzipIsASectionOfGeneralisedZip4'
    : forall F G
    , (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬G |∘| F⟭ (A × B)).
  intros * H1 H2 *; cbn ["⟬ _ ⟭"].
  cbn [generalisedZip'].
  rewrite unzipDecompositionLaw'.
  match goal with
  | |- context [(?k ∘' ?h) ∘' (?g ∘' ?f)] => transitivity (k ∘' (h ∘' g) ∘' f)
  end.
  repeat rewrite compositionAssociativity'; reflexivity.
  rewrite H2.
  rewrite compositionRightUnitLaw'.
  rewrite <- generalisedPolynomialFunctorsPreserveComposition'.
  rewrite H1.
  apply generalisedPolynomialFunctorsPreserveIdentities'.
Qed.

Theorem unzipIsASectionOfGeneralisedZip'
    : forall F A B, generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F⟭ (A × B)).
  induction F; intros;
    [ apply unzipIsASectionOfGeneralisedZip1'
    | apply unzipIsASectionOfGeneralisedZip2'
    | apply unzipIsASectionOfGeneralisedZip3'
    | apply unzipIsASectionOfGeneralisedZip4'
    ]; assumption.
Qed.

Theorem unzipIsAnInverseOfGeneralisedZip'
    : forall F A B
    , unzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B)
      /\ generalisedZip' _ _ _ ∘' unzip' _ _ _ = @η (⟬F⟭ (A × B)).
  split;
    [ apply unzipIsARetractionOfGeneralisedZip'
    | apply unzipIsASectionOfGeneralisedZip'
    ].
Qed.

Theorem someTheorem
    : forall F A B
    , pairOption ∘ bimap (F := prod) (αLeftInverse _ _) (αLeftInverse _ _)
        ∘' (η ||| !) ∘' (η ∘ partialProductInverse)
        ∘' unzip' _ _ _ ∘' generalisedZip' _ _ _
        ∘ partialProduct ∘ inl ∘ bimap (α _ _) (α _ _)
      = @η (⟦F⟧ A * ⟦F⟧ B).
Admitted.

(* 
proof that generalisedZip ∘ generalisedUnzip = pure
then we also have that
αLeftInverse ∘ genZip ∘ genUnzip ∘ α = pure

if you zip something that is actually 'zippable' and would get a pair in return.
then genZip would return midp _ _.
which we can transform into a pair.

if something actually zippable, sum return type.
then genZip would return either inlp (midp _ _) or inrp (midp _ _)
once again, we can turn this into inl (_, _) or inr (_, _)

(αLeftInverse ∘ genUnzip ∘ α) ∘ (αLeftInverse ∘ genZip ∘ α)
= pure
if and only if
input is 'zippable'.
*)
