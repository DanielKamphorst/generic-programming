Require Import Program.

Notation curry := prod_uncurry.
Notation uncurry := prod_curry.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Open Scope type_scope.

Class Functor F := fmap : forall A B, (A -> B) -> (F A -> F B).

Class Bifunctor F :=
  bimap : forall A A' B B', (A -> A') -> (B -> B') -> F A B -> F A' B'.

Notation "!" := (fun A (_ : A) => tt).

Definition pair' A B C (f : C -> A) (g : C -> B) : C -> A * B :=
  fun c => (f c, g c).
Infix "&&&" := pair' (at level 50).

Theorem productTrianglesCommutativity :
    forall X Y A (f : A -> X) (g : A -> Y)
    , fst ∘ (f &&& g) = f /\ snd ∘ (f &&& g) = g.
  auto.
Qed.

Instance productBifunctor : Bifunctor prod :=
  fun _ _ _ _ f g => f ∘ fst &&& g ∘ snd.

Theorem productPreservesIdentities : forall A B, bimap id id = @id (A * B).
  intros.
  extensionality p.
  symmetry; apply surjective_pairing.
Qed.

Theorem productPreservesComposition :
    forall A A' A'' B B' B''
    (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
    , bimap (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
  reflexivity.
Qed.

Definition caseAnalyse A B C (f : A -> C) (g : B -> C) : A + B -> C := fun cp =>
  match cp with
  | inl a => f a
  | inr b => g b
  end.
Infix "|||" := caseAnalyse (at level 60).

Instance coproductBifunctor : Bifunctor sum :=
  fun _ _ _ _ f g => inl ∘ f ||| inr ∘ g.

Theorem coproductPreservesIdentities : forall A B, bimap id id = @id (A + B).
  intros.
  extensionality cp; destruct cp as [a | b]; reflexivity.
Qed.

Theorem coproductPreservesComposition :
    forall A A' A'' B B' B''
    (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
    , bimap (F := sum) (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
  intros.
  extensionality cp; destruct cp as [a | b]; reflexivity.
Qed.

Definition fibreProduct X Y Z (f : X -> Z) (g : Y -> Z) :=
  {p : X * Y | (f ∘ fst) p = (g ∘ snd) p}.

Arguments fibreProduct : clear implicits.

Definition fst' X Y Z (f : X -> Z) (g : Y -> Z) : fibreProduct X Y Z f g -> X :=
  fst ∘ @proj1_sig _ _.

Definition snd' X Y Z (f : X -> Z) (g : Y -> Z) : fibreProduct X Y Z f g -> Y :=
  snd ∘ @proj1_sig _ _.

Definition pair'' X Y Z
    (t : X -> Z) (u : Y -> Z)
    A (f : A -> X) (g : A -> Y) (H : t ∘ f = u ∘ g)
    : A -> fibreProduct X Y Z t u :=
  fun a => exist _ ((f &&& g) a) (equal_f H a).

Theorem pullbackSquareCommutativity :
    forall X Y Z (f : X -> Z) (g : Y -> Z)
    , f ∘ fst' (f := f) = g ∘ snd' (g := g).
  intros.
  extensionality fp.
  exact (proj2_sig fp).
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

Infix "|*|" := product (at level 40).
Infix "|+|" := coproduct (at level 50).
Infix "|∘|" := composite (at level 40).

Reserved Notation "⟦ F ⟧".

Fixpoint denotation F' : Type -> Type :=
  match F' with
  | identityFunctor => id
  | F |*| G         => fun A => ⟦F⟧ A * ⟦G⟧ A
  | F |+| G         => fun A => ⟦F⟧ A + ⟦G⟧ A
  | G |∘| F         => ⟦G⟧ ∘ ⟦F⟧
  end
where "⟦ F ⟧" := (denotation F).

Fixpoint pfmap F' A B : (A -> B) -> (⟦F'⟧ A -> ⟦F'⟧ B) :=
  match F' with
  | identityFunctor => id
  | G |∘| F         => pfmap G ∘ pfmap F
  | _               => fun f => bimap (pfmap _ f) (pfmap _ f)
  end.

Instance polynomialFunctor F : Functor ⟦F⟧ := @pfmap F.

Theorem polynomialFunctorsPreserveIdentities
    : forall F' A, pfmap F' id = @id (⟦F'⟧ A).
  induction F' as [| F IHF G IHG | F IHF G IHG | G IHG F IHF]
  ; try reflexivity
  ; intro; cbn
  ; try unfold "_ ∘ _"
  ; rewrite IHF
  ; try apply IHG
  ; rewrite IHG
  ; [apply productPreservesIdentities | apply coproductPreservesIdentities].
Qed.

Theorem polynomialFunctorsPreserveComposition :
    forall F' A B C (f : A -> B) (g : B -> C)
    , pfmap F' (g ∘ f) = pfmap F' g ∘ pfmap F' f.
  induction F' as [| F IHF G IHG | F IHF G IHG | G IHG F IHF]
  ; try reflexivity
  ; intros; cbn
  ; try change ((pfmap G ∘ pfmap F) ?h) with (pfmap G (pfmap F h))
  ; rewrite IHF
  ; try apply IHG
  ; rewrite IHG
  ; [apply productPreservesComposition | apply coproductPreservesComposition].
Qed.

Definition unzipProduct X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    : fibreProduct X1 Y1 Z1 f1 g1 * fibreProduct X2 Y2 Z2 f2 g2
    -> fibreProduct (X1 * X2) (Y1 * Y2) (Z1 * Z2) (bimap f1 f2) (bimap g1 g2).
  refine (pair'' (f := bimap fst' fst') (g := bimap snd' snd') _).
  abstract
    ( repeat rewrite <- productPreservesComposition
    ; repeat rewrite pullbackSquareCommutativity
    ; reflexivity
    ).
Defined.

Definition zipProduct X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    : fibreProduct (X1 * X2) (Y1 * Y2) (Z1 * Z2) (bimap f1 f2) (bimap g1 g2)
    -> fibreProduct X1 Y1 Z1 f1 g1 * fibreProduct X2 Y2 Z2 f2 g2.
  refine (
      pair'' (t := f1) (u := g1) (f := fst ∘ fst') (g := fst ∘ snd') _
      &&& pair'' (t := f2) (u := g2) (f := snd ∘ fst') (g := snd ∘ snd') _)
  ; repeat rewrite <- compose_assoc
  ; [ rewrite <-
        (proj1 (productTrianglesCommutativity (f := f1 ∘ fst) (g := f2 ∘ snd)));
      rewrite <-
        (proj1 (productTrianglesCommutativity (f := g1 ∘ fst) (g := g2 ∘ snd)))
    | rewrite <-
        (proj2 (productTrianglesCommutativity (f := f1 ∘ fst) (g := f2 ∘ snd)));
      rewrite <-
        (proj2 (productTrianglesCommutativity (f := g1 ∘ fst) (g := g2 ∘ snd)))
    ]
  ; repeat rewrite compose_assoc; rewrite pullbackSquareCommutativity
  ; reflexivity.
Defined.

Theorem zipProductAndUnzipProductAreMutuallyInverse :
    forall X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    , unzipProduct ∘ zipProduct (f1 := f1) (f2 := f2) (g1 := g1) (g2 := g2) = id
      /\ zipProduct (f1 := f1) (f2 := f2) (g1 := g1) (g2 := g2) ∘ unzipProduct
        = id.
  split
  ; extensionality x
  ; [ destruct x as [[[x1 x2] [y1 y2]] H]
    | destruct x as [[[x1 y1] H1] [[x2 y2] H2]]; apply pair_equal_spec; split
    ]
  ; apply subset_eq_compat; reflexivity.
Qed.

Definition unzipCoproduct X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    : fibreProduct X1 Y1 Z1 f1 g1 + fibreProduct X2 Y2 Z2 f2 g2
    -> fibreProduct (X1 + X2) (Y1 + Y2) (Z1 + Z2) (bimap f1 f2) (bimap g1 g2).
  refine (pair'' (f := bimap fst' fst') (g := bimap snd' snd') _).
  abstract
    ( repeat rewrite <- coproductPreservesComposition
    ; repeat rewrite pullbackSquareCommutativity
    ; reflexivity
    ).
Defined.

Definition zipCoproduct X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    : fibreProduct (X1 + X2) (Y1 + Y2) (Z1 + Z2) (bimap f1 f2) (bimap g1 g2)
    -> fibreProduct X1 Y1 Z1 f1 g1 + fibreProduct X2 Y2 Z2 f2 g2.
  intros [[[x1 | x2] [y1 | y2]] [= H]];
    [ refine (inl (exist _ (x1, y1) H))
    | refine (inr (exist _ (x2, y2) H))
    ].
Defined.

Theorem zipCoproductAndUnzipCoproductAreMutuallyInverse :
    forall X1 X2 Y1 Y2 Z1 Z2
    (f1 : X1 -> Z1) (f2 : X2 -> Z2) (g1 : Y1 -> Z1) (g2 : Y2 -> Z2)
    , unzipCoproduct ∘ zipCoproduct (f1 := f1) (f2 := f2) (g1 := g1) (g2 := g2)
      = id
    /\ zipCoproduct (f1 := f1) (f2 := f2) (g1 := g1) (g2 := g2) ∘ unzipCoproduct
      = id.
  split
  ; extensionality x
  ; [ destruct x as [[[x1 | x2] [y1 | y2]] H]
    | destruct x as [[[x1 y1] H] | [[x2 y2] H]]
    ]
  ; try (cbn; unfold id; apply f_equal)
  ; ((apply subset_eq_compat; reflexivity) || discriminate H).
Qed.

Fixpoint zip F' X Y Z (f : X -> Z) (g : Y -> Z)
    : fibreProduct (⟦F'⟧ X) (⟦F'⟧ Y) (⟦F'⟧ Z) (pfmap F' f) (pfmap F' g)
    -> ⟦F'⟧ (fibreProduct X Y Z f g) :=
  match F' with
  | identityFunctor => id
  | F |*| G         => bimap (zip F _ _) (zip G _ _) ∘ zipProduct
  | F |+| G         => bimap (zip F _ _) (zip G _ _) ∘ zipCoproduct
  | G |∘| F         => pfmap G (zip F _ _) ∘ zip G _ _
  end.

Fixpoint unzip F' X Y Z (f : X -> Z) (g : Y -> Z)
    : ⟦F'⟧ (fibreProduct X Y Z f g)
    -> fibreProduct (⟦F'⟧ X) (⟦F'⟧ Y) (⟦F'⟧ Z) (pfmap F' f) (pfmap F' g) :=
  match F' with
  | identityFunctor => id
  | F |*| G         => unzipProduct ∘ bimap (unzip F _ _) (unzip G _ _)
  | F |+| G         => unzipCoproduct ∘ bimap (unzip F _ _) (unzip G _ _)
  | G |∘| F         => unzip G _ _ ∘ pfmap G (unzip F _ _)
  end.

Theorem zipAndUnzipAreMutuallyInverse :
    (forall F' X Y Z (f : X -> Z) (g : Y -> Z)
      , unzip F' _ _ ∘ zip F' f g = id)
    /\ (forall F' X Y Z (f : X -> Z) (g : Y -> Z)
      , zip F' f g ∘ unzip F' _ _ = id).
  split
  ; induction F' as [| F IHF G IHG | F IHF G IHG | G IHG F IHF]
  ; try reflexivity
  ; intros
  ; cbn
  ; change ((?k ∘ ?h) ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
  ; try rewrite (proj2 zipProductAndUnzipProductAreMutuallyInverse)
  ; try rewrite (proj2 zipCoproductAndUnzipCoproductAreMutuallyInverse)
  ; try rewrite compose_id_right
  ; try rewrite <- productPreservesComposition
  ; try rewrite <- coproductPreservesComposition
  ; try rewrite <- polynomialFunctorsPreserveComposition
  ; try rewrite IHF
  ; try rewrite IHG
  ; try rewrite productPreservesIdentities
  ; try rewrite coproductPreservesIdentities
  ; try rewrite polynomialFunctorsPreserveIdentities
  ; try reflexivity
  ; rewrite compose_id_right
  ; try (rewrite <- polynomialFunctorsPreserveComposition; rewrite IHF)
  ; [ apply (proj1 zipProductAndUnzipProductAreMutuallyInverse)
    | apply (proj1 zipCoproductAndUnzipCoproductAreMutuallyInverse)
    | apply IHG
    | apply polynomialFunctorsPreserveIdentities
    ].
Qed.

Definition pullbackOver1 X Y : X * Y -> fibreProduct X Y () (! X) (! Y) :=
  fun p => exist _ p eq_refl.

Theorem pullbackOver1IsAnIsomorphism :
    forall X Y
    , @proj1_sig _ _ ∘ @pullbackOver1 X Y = id
      /\ @pullbackOver1 X Y ∘ @proj1_sig _ _ = id.
  split;
    [ reflexivity
    | extensionality fp; destruct fp as [p H]
      ; unfold compose in H; simpl_uip
      ; apply sig_eta
    ].
Qed.

Definition zip' F X Y
    : fibreProduct (⟦F⟧ X) (⟦F⟧ Y) (⟦F⟧ ()) (pfmap F (! X)) (pfmap F (! Y))
    -> ⟦F⟧ (X * Y) :=
  pfmap F (@proj1_sig _ _) ∘ zip F (! X) (! Y).

Definition unzip' F X Y
    : ⟦F⟧ (X * Y)
    -> fibreProduct (⟦F⟧ X) (⟦F⟧ Y) (⟦F⟧ ()) (pfmap F (! X)) (pfmap F (! Y)) :=
  unzip F (! X) (! Y) ∘ pfmap F pullbackOver1.

Theorem zipAndUnzipAreMutuallyInverse' :
    forall F X Y
    , unzip' F _ _ ∘ zip' F X Y = id /\ zip' F X Y ∘ unzip' F _ _ = id.
  intros.
  unfold zip', unzip'.
  change ((?k ∘ ?h) ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f).
  split
    ; try
      ( rewrite (proj2 zipAndUnzipAreMutuallyInverse)
      ; rewrite compose_id_right
      )
    ; rewrite <- polynomialFunctorsPreserveComposition
    ; [ rewrite (proj2 pullbackOver1IsAnIsomorphism)
      | rewrite (proj1 pullbackOver1IsAnIsomorphism)
      ]
    ; rewrite polynomialFunctorsPreserveIdentities
    ; try reflexivity
    ; rewrite compose_id_right
    ; apply (proj1 zipAndUnzipAreMutuallyInverse).
Qed.
