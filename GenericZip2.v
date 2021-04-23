Require Import CategoryTheoryLibrary List.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* Induction on G |∘| F is what's really annoying. Maybe we can define a 'base case' for composite. Eventually F must be one of |+|, |*| or identityFunctor. (Inductively define composite/poly functors in general) *)

(* Idea 2 would be to make use of the fact that every poly functor G |∘| F 'theoretically' can be 'reduced' to a poly functor without any composites (by substitution). (Define some sort of reduction function) *)

Definition pair''' A B C (f : C ⇸ A) (g : C ⇸ B) : C ⇸ A * B := fun c =>
  match (f c, g c) with
  | (Some a, Some b) => η (a, b)
  | _                => None
  end.
Infix "&&&''" := pair''' (at level 50).

Instance productBifunctor' : Bifunctor' prod := {
  bimap' _ _ _ _ f g := f ∘ fst &&&'' g ∘ snd
}.

Instance coproductBifunctor' : Bifunctor' sum := {
  bimap' _ _ _ _ f g := option_map inl ∘ f ||| option_map inr ∘ g
}.

Instance polynomialFunctor' F : Functor' ⟦F⟧ := {
  fmap' := (fix fmap'' F' A B : (A ⇸ B) -> (⟦F'⟧ A ⇸ ⟦F'⟧ B) :=
    match F' with
    | identityFunctor => id
    | G |∘| F''       => fmap'' _ _ _ ∘ fmap'' _ _ _
    | _               => fun f => bimap' (fmap'' _ _ _ f) (fmap'' _ _ _ f)
    end) F
}.

Fixpoint zip F A B : ⟦F⟧ A * ⟦F⟧ B ⇸ ⟦F⟧ (A * B) :=
  match F with
  | identityFunctor => η
  | F1 |*| F2       => zip _ _ _ ∘ bimap fst fst &&&'' zip _ _ _ ∘ bimap snd snd
  | F1 |+| F2       => fun p =>
      match p with
      | (inl f1a, inl f1b) => option_map inl (zip _ _ _ (f1a, f1b))
      | (inr f2a, inr f2b) => option_map inr (zip _ _ _ (f2a, f2b))
      | _                  => None
      end
  | G  |∘| F'       => fmap' (zip F' _ _) ∘' zip G _ _
  end.

Definition unzip F A B : ⟦F⟧ (A * B) -> ⟦F⟧ A * ⟦F⟧ B := fmap fst &&& fmap snd.

Fixpoint members F A : ⟦F⟧ A -> list A :=
  match F return ⟦F⟧ A -> list A with
  | identityFunctor => flip cons nil
  | F1 |*| F2       => uncurry (@app _) ∘ bimap (members _) (members _)
  | F1 |+| F2       => members _ ||| members _
  | G  |∘| F'       => @concat _ ∘ members _ ∘ fmap (members _)
  end.

Theorem someTheorem :
    forall F A B (p : ⟦F⟧ A * ⟦F⟧ B) (fab : ⟦F⟧ (A * B))
    , zip _ _ _ p = η fab
    -> combine (members _ (fst p)) (members _ (snd p)) = members _ fab.
  induction F.
  admit.
  admit.
  admit.
  intros * H.
  cbn [members].
  cbn [zip] in H.
Abort.

Corollary productReflectionLaw : forall A B, fst &&& snd = @id (A * B).
Admitted.

Corollary productFusionLaw :
    forall A B C C' (f : C -> A) (g : C -> B) (h : C' -> C)
    , (f &&& g) ∘ h = f ∘ h &&& g ∘ h.
Admitted.

Corollary productCancellationLaw1 :
    forall A B C (f : C -> A) (g : C -> B), fst ∘ (f &&& g) = f.
Admitted.

Corollary productCancellationLaw2 :
    forall A B C (f : C -> A) (g : C -> B), snd ∘ (f &&& g) = g.
Admitted.

Theorem productAbsorptionLaw :
    forall A A' B B' C (h : C -> A) (f : A -> A') (k : C -> B) (g : B -> B')
    , bimap f g ∘ (h &&& k) = f ∘ h &&& g ∘ k.
Admitted.

Theorem t1 :
    forall A B C (f : C -> A) (g : C -> B)
    , option_map f &&&'' option_map g = option_map (f &&& g).
  crush.
Qed.

Theorem t2 :
    forall A B C C' (f : C ⇸ A) (g : C ⇸ B) (h : C' -> C)
    , (f &&&'' g) ∘ h = f ∘ h &&&'' g ∘ h.
  crush.
Qed.

Theorem t3 :
    forall A B C D
    , bimap (@fst A B) (@fst C D) = fun '((a, _), (c, _)) => (a, c).
  intros.
  extensionality p.
  destruct p as [p1 p2]; destruct p1; destruct p2; reflexivity.
Qed.

Theorem t4 :
    forall A B C D
    , bimap (@snd A B) (@snd C D) = fun '((_, b), (_, d)) => (b, d).
  intros.
  extensionality p.
  destruct p as [p1 p2]; destruct p1; destruct p2; reflexivity.
Qed.

Theorem polynomialFunctorsPreserveComposition :
    forall F A B C (f : A -> B) (g : B -> C)
    , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f.
Admitted.

Lemma unzipDecompositionLaw :
    forall F G A B
    , unzip (G |∘| F) A B = unzip G _ _ ∘ fmap (unzip F _ _).
  intros.
  unfold unzip.
  rewrite productFusionLaw.
  repeat rewrite <- polynomialFunctorsPreserveComposition.
  rewrite productCancellationLaw1; rewrite productCancellationLaw2.
  reflexivity.
Qed.

Theorem t5 :
    forall F A B C (f : A ⇸ B) (g : B -> C)
    , option_map (fmap (F := ⟦F⟧) g) ∘ fmap' f = fmap' (option_map g ∘ f).
  intros.
  change_no_check (option_map g ∘ f) with ((η ∘ g) ∘' f).
  change_no_check (fmap' ((η ∘ g) ∘' f)) with (fmap' (F := ⟦F⟧) (η ∘ g) ∘' fmap' f).
  change_no_check (option_map (fmap g) ∘ fmap' f) with ((η ∘ (fmap (F := ⟦F⟧) g)) ∘' fmap' f).
  change_no_check (η ∘ fmap g) with (fmap' (η ∘ g)).
  reflexivity.
Admitted.

Theorem unzipIsASectionOfZip :
    forall F A B (fab : ⟦F⟧ (A * B))
    , (zip _ _ _ ∘ unzip _ _ _) fab = η fab
      \/ (zip _ _ _ ∘ unzip _ _ _) fab = None.
  induction F.
  admit.
  admit.
  admit.
  intros.
  cbn [zip].
  rewrite unzipDecompositionLaw.
  unfold unzip in IHF1, IHF2.
Abort.

Theorem unzipIsARetractionOfZip :
    forall F A B (p : ⟦F⟧ A * ⟦F⟧ B)
    , (option_map (unzip _ _ _) ∘ zip _ _ _) p = η p
      \/ (option_map (unzip _ _ _) ∘ zip _ _ _) p = None.
  induction F.

  unfold zip, unzip.
  unfold fmap, polynomialFunctor.
  unfold id.
  unfold "⟦ _ ⟧".
  unfold id.
  setoid_rewrite productReflectionLaw.
  auto.

  cbn [zip]; unfold unzip.
  unfold fmap, polynomialFunctor; cbn [polynomialFunctorMap].
  unfold unzip in IHF1, IHF2.
  unfold fmap, polynomialFunctor in IHF1, IHF2.
  intros A B [[f1a f2a] [f1b f2b]].
  rewrite t3; rewrite t4.
  unfold "_ &&&'' _".
  unfold compose.
  specialize (IHF1 A B (f1a, f1b)).
  specialize (IHF2 A B (f2a, f2b)).
  unfold "_ &&& _" in IHF1.
  unfold compose in IHF1.
  unfold option_map in IHF1.
  unfold "_ &&& _" in IHF2.
  unfold compose in IHF2.
  unfold option_map in IHF2.
  unfold option_map, bimap, productBifunctor, "_ &&& _", compose.
  destruct (zip F1 A B (f1a, f1b)) as [f1ab |]; destruct (zip F2 A B (f2a, f2b)) as [f2ab |]; try auto.
  simpl.
  elim IHF1; elim IHF2; intros [= -> ->] [= -> ->]; auto.

  cbn [zip]; unfold unzip.
  unfold fmap, polynomialFunctor; cbn [polynomialFunctorMap].
  unfold unzip in IHF1, IHF2.
  unfold fmap, polynomialFunctor in IHF1, IHF2.
  unfold option_map, compose, "_ &&& _", bimap, coproductBifunctor, copair, compose in *.
  intros A B [[f1a | f2a] [f1b | f2b]]; try specialize (IHF1 A B (f1a, f1b)); try specialize (IHF2 A B (f2a, f2b)).
  all: try change (zip F1 A B (f1a, f1b)) with (zip F1 A B (f1a, f1b)).
  all: try change (zip F2 A B (f2a, f2b)) with (zip F2 A B (f2a, f2b)).
  4: destruct (zip F2 A B (f2a, f2b)).
  1: destruct (zip F1 A B (f1a, f1b)).
  1: elim IHF1; intros [= -> ->]; auto.
  4: elim IHF2; intros [= -> ->]; auto.
  all: try auto.

  intros.
  cbn [zip].
  rewrite unzipDecompositionLaw.
  rewrite optionPreservesComposition.
  rewrite compose_assoc.
  change_no_check (?h ∘ (?g ∘' ?f)) with ((h ∘ g) ∘' f).
change (option_map (fmap (unzip F2 A B)) ∘ fmap' (zip F2 A B)) with (option_map (fmap (F := ⟦F1⟧) (unzip F2 A B)) ∘ fmap' (zip F2 A B)).
  rewrite (@t5 F1 _ _ _ (zip F2 A B) (unzip F2 A B)).
Abort.

(*
Theorem t1 :
    forall A B C (f : C ⇸ A) (g : C ⇸ B) (c : C)
    , (f &&&'' g) c = None <-> f c = None \/ g c = None.
  unfold "_ &&&'' _".
  split
    ; [ destruct (f c); destruct (g c); intros [=] 
      | intros [-> | ->]; [| destruct (f c)]
      ]
    ; auto.
Qed.

Theorem t2 : forall A B (f : A -> B) oa, option_map f oa = None <-> oa = None.
  split; destruct oa; intros [=]; reflexivity.
Qed.

Theorem t3 :
    forall A B C D
    , bimap (@fst A B) (@fst C D) = fun '((a, _), (c, _)) => (a, c).
  intros.
  extensionality p.
  destruct p as [p1 p2]; destruct p1; destruct p2; reflexivity.
Qed.

Theorem t4 :
    forall A B C D
    , bimap (@snd A B) (@snd C D) = fun '((_, b), (_, d)) => (b, d).
  intros.
  extensionality p.
  destruct p as [p1 p2]; destruct p1; destruct p2; reflexivity.
Qed.

(* Clearly (by the definition of zip and theorems t1 to t4), a pair p is 'zippable' if and only if zip p = η. Or maybe more intuitively, zip p = None if and only if p is not 'zippable' *)
*)

Fixpoint FR_related F A B (R : A * B -> Prop) : ⟦F⟧ A * ⟦F⟧ B -> Prop :=
  match F with
  | identityFunctor => R
  | F' |*| G => fun '((fa', ga), (fb', gb)) =>
      FR_related F' R (fa', fb') /\ FR_related G R (ga, gb)
  | F' |+| G => fun '(cp1, cp2) =>
      match cp1, cp2 with
      | inl fa', inl fb' => FR_related F' R (fa', fb')
      | inr ga , inr gb  => FR_related G R (ga, gb)
      | _, _             => False
      end
  | G |∘| F' => FR_related G (FR_related F' R)
  end.

Definition equivalentlyShaped F A B : ⟦F⟧ A * ⟦F⟧ B -> Prop :=
  FR_related F (fun _ => True).

Fixpoint generalisedZip' F A B : ⟬F⟭ A × ⟬F⟭ B ⇸ ⟬F⟭ (A × B) :=
  match F with
  | identityFunctor => η
  | G |∘| F'        => fmap' (generalisedZip' F' _ _) ∘' generalisedZip' G _ _
  | _               =>
      generalisedZip' _ _ _ ∘' bimap' fst'' fst''
      &&&' generalisedZip' _ _ _ ∘' bimap' snd'' snd''
  end.

Definition generalisedUnzip' F A B : ⟬F⟭ (A × B) ⇸ ⟬F⟭ A × ⟬F⟭ B :=
  fmap' fst'' &&&' fmap' snd''.

Lemma unzipDecompositionLaw'
    : forall F G A B
    , generalisedUnzip' (G |∘| F) A B
      = generalisedUnzip' G _ _ ∘' fmap' (generalisedUnzip' F _ _).
  intros.
  unfold generalisedUnzip'; repeat unfoldSingleFmap'.
  rewrite partialProductFusionLaw.
  repeat rewrite <- generalisedPolynomialFunctorsPreserveComposition'.
  rewrite partialProductCancellationLaw1
    ; rewrite partialProductCancellationLaw2.
  reflexivity.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip1'
    : forall A B
    , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _
      = @η (⟬identityFunctor⟭ A × ⟬identityFunctor⟭ B).
  intros.
  unfold generalisedUnzip'; repeat unfoldSingleFmap'; cbn ["⟬ _ ⟭"]; unfold id.
  rewrite <- partialProductReflectionLaw.
  cbn [generalisedZip'].
  apply compositionLeftUnitLaw'.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip2'
    : forall F G
    , (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _
        = @η (⟬F |*| G⟭ A × ⟬F |*| G⟭ B).
  unfold generalisedUnzip'.
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
    , (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _
        = @η (⟬F |+| G⟭ A × ⟬F |+| G⟭ B).
  change (?f (?F |+| ?G) ?A ?B) with (f (F |*| G) A B).
  exact @unzipIsARetractionOfGeneralisedZip2'.
Qed.

Lemma unzipIsARetractionOfGeneralisedZip4'
    : forall F G
    , (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B))
    -> (forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬G⟭ A × ⟬G⟭ B))
    -> forall A B
      , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _
        = @η (⟬G |∘| F⟭ A × ⟬G |∘| F⟭ B).
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
    : forall F A B
    , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B).
  induction F; intros;
    [ apply unzipIsARetractionOfGeneralisedZip1'
    | apply unzipIsARetractionOfGeneralisedZip2'
    | apply unzipIsARetractionOfGeneralisedZip3'
    | apply unzipIsARetractionOfGeneralisedZip4'
    ]; assumption.
Qed.

Lemma unzipIsASectionOfGeneralisedZip1'
    : forall A B
    , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _
      = @η (⟬identityFunctor⟭ (A × B)).
  intros.
  cbn [generalisedZip'].
  rewrite compositionLeftUnitLaw'.
  unfold generalisedUnzip'; repeat unfoldSingleFmap'.
  symmetry; apply partialProductReflectionLaw.
Qed.

Lemma unzipIsASectionOfGeneralisedZip2'
    : forall F G
    , (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _
        = @η (⟬F |*| G⟭ (A × B)).
  intros * H1 H2 *.
  cbn ["⟬ _ ⟭" generalisedZip'].
  rewrite partialProductFusionLaw.
  unfold generalisedUnzip'; repeat unfoldSingleFmap'.
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
    , (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _
        = @η (⟬F |+| G⟭ (A × B)).
  change (?f (?F |+| ?G) ?A ?B) with (f (F |*| G) A B).
  exact @unzipIsASectionOfGeneralisedZip2'.
Qed.

Lemma unzipIsASectionOfGeneralisedZip4'
    : forall F G
    , (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬F⟭ (A × B)))
    -> (forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬G⟭ (A × B)))
    -> forall A B
      , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _
        = @η (⟬G |∘| F⟭ (A × B)).
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
    : forall F A B
    , generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬F⟭ (A × B)).
  induction F; intros;
    [ apply unzipIsASectionOfGeneralisedZip1'
    | apply unzipIsASectionOfGeneralisedZip2'
    | apply unzipIsASectionOfGeneralisedZip3'
    | apply unzipIsASectionOfGeneralisedZip4'
    ]; assumption.
Qed.

Theorem unzipIsAnInverseOfGeneralisedZip'
    : forall F A B
    , generalisedUnzip' _ _ _ ∘' generalisedZip' _ _ _ = @η (⟬F⟭ A × ⟬F⟭ B)
      /\ generalisedZip' _ _ _ ∘' generalisedUnzip' _ _ _ = @η (⟬F⟭ (A × B)).
  split;
    [ apply unzipIsARetractionOfGeneralisedZip'
    | apply unzipIsASectionOfGeneralisedZip'
    ].
Qed.

Corollary coproductFusionLaw
    : forall A B C C' (f : A -> C) (g : B -> C) (h : C -> C')
    , h ∘ (f ||| g) = h ∘ f ||| h ∘ g.
  intros.
  apply coproductUniversalProperty.
  split
    ; rewrite compose_assoc
    ; [rewrite coproductCancellationLaw1 | rewrite coproductCancellationLaw2]
    ; reflexivity.
Qed.

Theorem coproductAbsorptionLaw
    : forall A A' B B' C (f' : A' -> A) (f : A -> C) (g' : B' -> B) (g : B -> C)
    , (f ||| g) ∘ bimap f' g' = f ∘ f' ||| g ∘ g'.
  intros.
  cbn [bimap coproductBifunctor].
  rewrite coproductFusionLaw.
  rewrite <- compose_assoc; rewrite coproductCancellationLaw1
    ; rewrite <- compose_assoc; rewrite coproductCancellationLaw2.
  reflexivity.
Qed.

Theorem partialProductInverseIsAnInverseOfPartialProduct
    : forall A B
    , partialProductInverse ∘ partialProduct = @id ((A * B) + (A + B))
      /\ partialProduct ∘ partialProductInverse = @id (A × B).
  crush.
Qed.

Definition β A : option A -> A + () := option_rect _ inl (inr tt).
Definition βInverse A : A + () -> option A := η ||| !.

Theorem βInverseIsAnInverseOfβ
    : forall A
    , βInverse ∘ β = @id (option A) /\ β ∘ βInverse = @id (A + ()).
  crush.
Qed.

Definition ξ1 A B : (A * B) + (A + B) -> (A * B) + () :=
  bimap id (fun _ => tt).

Definition ξ2 A B : (A * B) + (A + B) -> () + (A + B) :=
  bimap (fun _ => tt) id.

Definition swap A B : A + B -> B + A := inr ||| inl.

Definition ξ1' A B : (A * B) + (A + B) ⇸ A * B := βInverse ∘ ξ1.
Definition ξ2' A B : (A * B) + (A + B) ⇸ A + B := βInverse ∘ swap ∘ ξ2.

Theorem t1 : forall A B, @ξ1' A B = η ||| !.
  intros.
  unfold ξ1', βInverse, ξ1.
  rewrite coproductAbsorptionLaw.
  trivial.
Qed.

Theorem t2 : forall A B, @ξ2' A B = ! ||| η.
  intros.
  unfold ξ2', βInverse, swap, ξ2.
  rewrite compose_assoc; rewrite coproductAbsorptionLaw.
  rewrite coproductFusionLaw.
  rewrite <- compose_assoc; rewrite coproductCancellationLaw2
    ; rewrite <- compose_assoc; rewrite coproductCancellationLaw1.
  trivial.
Qed.

Definition p2pp A B : A * B -> A × B := partialProduct ∘ inl.
Definition pp2p A B : A × B ⇸ A * B := (η ||| !) ∘ partialProductInverse.

Theorem pp2pIsARetractionOfp2pp : forall A B, pp2p ∘ p2pp = @η (A * B).
  intros.
  unfold pp2p, p2pp.
  change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; rewrite (proj1 partialProductInverseIsAnInverseOfPartialProduct)
    ; rewrite compose_id_right.
  apply coproductCancellationLaw1.
Qed.

Definition cp2pp A B : A + B -> A × B := partialProduct ∘ inr.
Definition pp2cp A B : A × B ⇸ A + B := (! ||| η) ∘ partialProductInverse.

Theorem pp2cpIsARetractionOfcp2pp : forall A B, pp2cp ∘ cp2pp = @η (A + B).
  intros.
  unfold pp2cp, cp2pp.
  change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; rewrite (proj1 partialProductInverseIsAnInverseOfPartialProduct)
    ; rewrite compose_id_right.
  apply coproductCancellationLaw2.
Qed.

Fixpoint pf2gpf F A : ⟦F⟧ A -> ⟬F⟭ A :=
  match F with
  | identityFunctor => id
  | F' |*| G        => bimap (pf2gpf _ _) (pf2gpf _ _) ∘ p2pp
  | F' |+| G        => bimap (pf2gpf _ _) (pf2gpf _ _) ∘ cp2pp
  | G  |∘| F'       => fmap (pf2gpf _ _) ∘ pf2gpf _ _
  end.

Fixpoint gpf2pf F A : ⟬F⟭ A ⇸ ⟦F⟧ A :=
  match F with
  | identityFunctor => η
  | F' |*| G        => pp2p ∘' bimap' (gpf2pf _ _) (gpf2pf _ _)
  | F' |+| G        => pp2cp ∘' bimap' (gpf2pf _ _) (gpf2pf _ _)
  | G  |∘| F'       => (gpf2pf _ _) ∘' fmap' (gpf2pf _ _)
  end.

Theorem t3 :
    forall A A' A'' B B' B''
      (f : A -> A') (f' : A' ⇸ A'')
      (g : B -> B') (g' : B' ⇸ B'')
    , bimap' (F := partialProd) f' g' ∘ bimap f g
      = bimap' (F := partialProd) (f' ∘ f) (g' ∘ g).
  crush.
Qed.

Ltac unfoldSingleFmap :=
  match goal with
  | |- context G [fmap (F := ⟬?F⟭) ?f] =>
      let g :=
        match F with
        | identityFunctor => f
        | _ |∘| _         => constr:(fmap (fmap f))
        | _               => constr:(bimap (fmap f) (fmap f))
        end
      in let t := context G [g] in change t
  end.

Theorem t4 :
    forall F A B C (f : A -> B) (g : B ⇸ C)
    , fmap' g ∘ fmap f = fmap' (F := ⟬F⟭) (g ∘ f).
  induction F; intros; repeat unfoldSingleFmap'; repeat unfoldSingleFmap.
  reflexivity.
  cbn ["⟬ _ ⟭"].
  repeat rewrite t3.
  rewrite IHF1; rewrite IHF2.
  reflexivity.
  cbn ["⟬ _ ⟭"].
  repeat rewrite t3.
  rewrite IHF1; rewrite IHF2.
  reflexivity.
  rewrite <- IHF2.
  rewrite <- IHF1.
  reflexivity.
Qed.

Theorem gpf2pfIsARetractionOfpf2gpf
    : forall F A, gpf2pf _ _ ∘ pf2gpf _ _ = @η (⟦F⟧ A).
  induction F.
  reflexivity.

  intro.
  cbn [pf2gpf gpf2pf].
  unfold "_ ∘' _".
  change (?p ∘ ?k ∘ ?h ∘ (?g ∘ ?f)) with (p ∘ k ∘ (h ∘ g) ∘ f).
  rewrite t3.
  rewrite IHF1; rewrite IHF2.
  rewrite partialProductPreservesIdentities.
  change (?k ∘ ?h ∘ ?g ∘ ?f) with (k ∘ (h ∘ g) ∘ f).
  rewrite unitNaturality.
  change (?k ∘ (?h ∘ ?g) ∘ ?f) with (k ∘ h ∘ (g ∘ f)).
  rewrite pp2pIsARetractionOfp2pp.
  reflexivity.

  intro.
  cbn [pf2gpf gpf2pf].
  unfold "_ ∘' _".
  change (?p ∘ ?k ∘ ?h ∘ (?g ∘ ?f)) with (p ∘ k ∘ (h ∘ g) ∘ f).
  rewrite t3.
  rewrite IHF1; rewrite IHF2.
  rewrite partialProductPreservesIdentities.
  change (?k ∘ ?h ∘ ?g ∘ ?f) with (k ∘ (h ∘ g) ∘ f).
  rewrite unitNaturality.
  change (?k ∘ (?h ∘ ?g) ∘ ?f) with (k ∘ h ∘ (g ∘ f)).
  rewrite pp2cpIsARetractionOfcp2pp.
  reflexivity.

  intro.
  cbn [pf2gpf gpf2pf].
  unfold "_ ∘' _".
  change (?p ∘ ?k ∘ ?h ∘ (?g ∘ ?f)) with (p ∘ k ∘ (h ∘ g) ∘ f).
  rewrite t4.
  rewrite IHF2.
  rewrite generalisedPolynomialFunctorsPreserveIdentities'.
  change (μ ∘ option_map ?g ∘ ?f) with (g ∘' f).
  rewrite compositionRightUnitLaw'.
  apply IHF1.
Qed.

Theorem retractionTheorem1 :
    forall F A B
    , bimap' (gpf2pf _ _) (gpf2pf _ _) ∘ bimap (pf2gpf _ _) (pf2gpf _ _)
      = @η (⟦F⟧ A × ⟦F⟧ B).
  intros.
  rewrite t3.
  repeat rewrite gpf2pfIsARetractionOfpf2gpf.
  apply partialProductPreservesIdentities.
Qed.

Theorem retractionTheorem2
    : forall F A B, fmap' pp2p ∘ fmap p2pp = @η (⟬F⟭ (A * B)).
  intros.
  rewrite t4.
  rewrite pp2pIsARetractionOfp2pp.
  apply generalisedPolynomialFunctorsPreserveIdentities'.
Qed.

Theorem retractionTheorem3 :
    forall F A B
    , (pp2p ∘' bimap' (gpf2pf _ _) (gpf2pf _ _))
        ∘ bimap (pf2gpf _ _) (pf2gpf _ _)
        ∘ p2pp
      = @η (⟦F⟧ A * ⟦F⟧ B).
  intros.
  unfold "_ ∘' _".
  change (?p ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (p ∘ k ∘ (h ∘ g) ∘ f).
  rewrite retractionTheorem1.
  change (μ ∘ option_map ?g ∘ ?f) with (g ∘' f).
  rewrite compositionRightUnitLaw'.
  apply pp2pIsARetractionOfp2pp.
Qed.

Theorem retractionTheorem4 :
    forall F A B
    , (gpf2pf _ _ ∘' fmap' pp2p) ∘ fmap p2pp ∘ pf2gpf _ _ = @η (⟦F⟧ (A * B)).
  intros.
  unfold "_ ∘' _".
  change (?p ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (p ∘ k ∘ (h ∘ g) ∘ f).
  rewrite retractionTheorem2.
  change (μ ∘ option_map ?g ∘ ?f) with (g ∘' f).
  rewrite compositionRightUnitLaw'.
  apply gpf2pfIsARetractionOfpf2gpf.
Qed.

Theorem retractionTheorem5 :
    forall F A B
    , (pp2p
          ∘' bimap' (gpf2pf _ _) (gpf2pf _ _)
          ∘' generalisedUnzip' _ _ _
          ∘' generalisedZip' _ _ _)
        ∘ bimap (pf2gpf _ _) (pf2gpf _ _) ∘ p2pp
      = @η (⟦F⟧ A * ⟦F⟧ B).
  intros.
  rewrite compositionAssociativity'.
  rewrite unzipIsARetractionOfGeneralisedZip'; rewrite compositionRightUnitLaw'.
  apply retractionTheorem3.
Qed.

Theorem retractionTheorem6 :
    forall F A B
    , (gpf2pf _ _
          ∘' fmap' pp2p
          ∘' generalisedZip' _ _ _
          ∘' generalisedUnzip' _ _ _)
        ∘ fmap p2pp ∘ pf2gpf _ _
      = @η (⟦F⟧ (A * B)).
  intros.
  rewrite compositionAssociativity'.
  rewrite unzipIsASectionOfGeneralisedZip'; rewrite compositionRightUnitLaw'.
  apply retractionTheorem4.
Qed.

Definition zip F A B : ⟦F⟧ A * ⟦F⟧ B ⇸ ⟦F⟧ (A * B) :=
  (gpf2pf _ _ ∘' fmap' pp2p ∘' generalisedZip' _ _ _)
  ∘ bimap (pf2gpf _ _) (pf2gpf _ _)
  ∘ p2pp.

Definition unzip' F A B : ⟦F⟧ (A * B) ⇸ ⟦F⟧ A * ⟦F⟧ B :=
  (pp2p ∘' bimap' (gpf2pf _ _) (gpf2pf _ _) ∘' generalisedUnzip' _ _ _)
  ∘ fmap p2pp
  ∘ pf2gpf _ _.

Theorem someTheorem1 :
    forall A B (pp : A × B)
    , (exists a b, pp = midp a b) -> (option_map p2pp ∘ pp2p) pp = η pp.
  destruct pp; intros [a' [b' [=]]]; reflexivity.
Qed.

Lemma someLemma :
    forall A B C C' (f : C ⇸ A) (g : C ⇸ B) (h : C' -> C)
    , (f &&&' g) ∘ h = f ∘ h &&&' g ∘ h.
  intros.
  transitivity (f ∘' (η ∘ h) &&&' g ∘' (η ∘ h)).
  transitivity ((f &&&' g) ∘' (η ∘ h)).
  reflexivity.
  apply partialProductFusionLaw.
  reflexivity.
Qed.

Lemma anotherLemma :
    forall A B C D (f : A -> B) (g : B ⇸ C) (h : C ⇸ D)
    , (h ∘' g) ∘ f = h ∘' (g ∘ f).
  reflexivity.
Qed.

Theorem pproductPreservesComposition :
    forall A A' A'' B B' B''
      (f : A -> A') (f' : A' -> A'')
      (g : B -> B') (g' : B' -> B'')
    , bimap (F := partialProd) (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
Admitted.

(* Keep. *)
Theorem p2ppCancellationLaw :
    forall A B
    , partialProductInverse ∘ p2pp = inl (A := A * B).
  intros.
  unfold p2pp.
  rewrite <- compose_assoc
    ; rewrite (proj1 partialProductInverseIsAnInverseOfPartialProduct)
    ; apply compose_id_left.
Qed.

(* p2pp : − * − ⇒ − × − *)
Theorem p2ppNaturality :
    forall A A' B B' (f : A -> A') (g : B -> B')
    , bimap (F := partialProd) f g ∘ p2pp = p2pp ∘ bimap (F := prod) f g.
  intros.
  unfold bimap at 1; unfold partialProductBifunctor at 1.
  rewrite compose_assoc; rewrite p2ppCancellationLaw.
  unfold bimap at 1; unfold coproductBifunctor at 1.
  rewrite compose_assoc; rewrite coproductCancellationLaw1.
  reflexivity.
Qed.

Theorem p2ppEquality : forall A B, @p2pp A B = uncurry midp.
  intros.
  unfold p2pp, partialProduct.
  apply coproductCancellationLaw1.
Qed.

Theorem commutativeSquare11 :
    forall A B
    , fst'' ∘ @p2pp A B = η ∘ fst.
  intros.
  unfold fst''.
  rewrite p2ppEquality.
  crush.
Qed.

Theorem commutativeSquare12 :
    forall A B
    , snd'' ∘ @p2pp A B = η ∘ snd.
  intros.
  unfold snd''.
  rewrite p2ppEquality.
  crush.
Qed.

Theorem ppPreservesComposition' :
    forall A A' A'' B B' B''
      (f : A -> A') (f' : A' ⇸ A'')
      (g : B -> B') (g' : B' ⇸ B'')
    , bimap' f' g' ∘ bimap f g = bimap' (f' ∘ f) (g' ∘ g).
  crush.
Qed.

Theorem commutativeSquare21 :
    forall A B C D
    , bimap' fst'' fst'' ∘ bimap p2pp p2pp = η ∘ bimap (@fst A B) (@fst C D).
  intros.
  rewrite ppPreservesComposition'.
  repeat rewrite commutativeSquare11.
  rewrite <- ppPreservesComposition'.
  rewrite partialProductPreservesIdentities.
  reflexivity.
Qed.

Theorem commutativeSquare22 :
    forall A B C D
    , bimap' snd'' snd'' ∘ bimap p2pp p2pp = η ∘ bimap (@snd A B) (@snd C D).
  intros.
  rewrite ppPreservesComposition'.
  repeat rewrite commutativeSquare12.
  rewrite <- ppPreservesComposition'.
  rewrite partialProductPreservesIdentities.
  reflexivity.
Qed.

Theorem productCancellationLaw1
    : forall A B C (f : C -> A) (g : C -> B), fst ∘ (f &&& g) = f.
Admitted.

Theorem productCancellationLaw2
    : forall A B C (f : C -> A) (g : C -> B), snd ∘ (f &&& g) = g.
Admitted.

Theorem unzipIsARetractionOfZip :
    forall F A B (p : ⟦F⟧ A * ⟦F⟧ B)
    , (unzip' _ _ _ ∘' zip _ _ _) p = η p
      \/ (unzip' _ _ _ ∘' zip _ _ _) p = None.
  induction F.
  admit.
  admit.
  admit.
  intros.
  unfold zip, unzip'.
  cbn [generalisedZip'].
  rewrite unzipDecompositionLaw'.
  cbn [pf2gpf gpf2pf].
  unfold unzip', zip in IHF1, IHF2.
  rewrite partialProductPreservesComposition.



  unfold unzip', zip.
Abort.

Theorem someTheorem2 :
    forall F A B (p : ⟦F⟧ A * ⟦F⟧ B)
    , equivalentlyShaped _ _ _ p -> exists fab, zip _ _ _ p = η fab.
  unfold zip.
  induction F.
  admit.
  intros * H.
  unfoldSingleFmap'.
  cbn [pf2gpf generalisedZip' gpf2pf "⟬ _ ⟭"].
  repeat
    (rewrite compositionAssociativity'; rewrite partialProductAbsorptionLaw).
  repeat rewrite p2ppNaturality.
  rewrite pproductPreservesComposition.
  rewrite <- compose_assoc.
  rewrite anotherLemma.
  rewrite someLemma.
  repeat rewrite anotherLemma.
  rewrite commutativeSquare21; rewrite commutativeSquare22.
  change (?g ∘' (η ∘ ?f)) with (g ∘ f).
  rewrite someLemma.
  rewrite anotherLemma.
  rewrite anotherLemma.
  rewrite compose_assoc.
  rewrite <- pproductPreservesComposition.
  unfold bimap at 2; unfold productBifunctor.
  unfold bimap at 2; unfold productBifunctor.
  repeat rewrite productCancellationLaw1.
  rewrite pproductPreservesComposition.
  repeat rewrite anotherLemma.
  rewrite compose_assoc.
  setoid_rewrite <- pproductPreservesComposition at 2.
  unfold bimap at 4 5.
  repeat rewrite productCancellationLaw2.
  rewrite pproductPreservesComposition.
  rewrite someLemma.
  repeat rewrite anotherLemma.
  repeat rewrite compose_assoc.
  repeat rewrite p2ppNaturality.
  unfold "_ ∘' _" at 1.
  unfold "_ ∘ _" at 1.
  unfold "_ &&&' _".
  repeat rewrite <- anotherLemma.
  repeat rewrite <- compose_assoc.
  change ((?g ∘ ?f) p) with (g (f p)).

  cbn [equivalentlyShaped FR_related] in H.
  destruct p as [[fa ga] [fb gb]].
  specialize (IHF1 A B (fa, fb) (proj1 H)).
  elim IHF1.
  intros fab' H1.
  change (bimap fst fst (fa, ga, (fb, gb))) with ((fa, fb)).
  change (bimap snd snd (fa, ga, (fb, gb))) with ((ga, gb)).
  rewrite <- compositionAssociativity'.
  fold denotation.
  rewrite H1.
  specialize (IHF2 A B (ga, gb) (proj2 H)).
  elim IHF2.
  intros gab H2.
  rewrite <- compositionAssociativity'.
  rewrite H2.
  change ((?h ∘ ?g) (?f ?x)) with ((h ∘ g ∘ f) x).
  change (μ ∘ option_map ?g ∘ ?f) with (g ∘' f).
  rewrite compositionRightUnitLaw'.
  change (midp ?x ?y) with (uncurry midp (x, y)).
  rewrite <- p2ppEquality.
  change (pp2p (p2pp ?x)) with ((pp2p ∘ p2pp) x).
  rewrite pp2pIsARetractionOfp2pp.
  exists (fab', gab); reflexivity.
  (* end of product ^^ *)

  admit.

  cbn [pf2gpf generalisedZip' gpf2pf].


  intros * H.
  induction F1; induction F2.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  destruct p as [fa fb].
  cbn [pf2gpf generalisedZip' gpf2pf].
  simpl.
Abort.
