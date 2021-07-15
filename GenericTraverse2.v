Require Import Program.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Open Scope type_scope.

Class Functor F :=
  { fmap : forall A B, (A -> B) -> (F A -> F B)
  ; functorsPreserveIdentityMorphisms : forall A, fmap id = @id (F A)
  ; functorsPreserveComposition
    : forall A B C (f : A -> B) (g : B -> C)
    , fmap (g ∘ f) = fmap g ∘ fmap f
  }.

Generalizable All Variables.

#[refine] Instance compositeOfTwoFunctors
    `(FF : Functor F, FG : Functor G) : Functor (G ∘ F) :=
  { fmap _ _ := fmap (F := G) ∘ fmap (F := F)
  }.
Proof.
  all: intros;
    change ((fmap (F := G) ∘ fmap (F := F)) ?f)
    with (fmap (F := G) (fmap (F := F) f)).
  1: repeat rewrite functorsPreserveIdentityMorphisms.
  2: repeat rewrite functorsPreserveComposition.
  all: reflexivity.
Defined.

Class Bifunctor F :=
  { bimap : forall A A' B B', (A -> A') -> (B -> B') -> (F A B -> F A' B')
  ; bifunctorsPreserveIdentityMorphisms : forall A B, bimap id id = @id (F A B)
  ; bifunctorsPreserveComposition
    : forall A A' A'' B B' B''
      (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
    , bimap (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g
  }.

Definition tuple A B X (f : X -> A) (g : X -> B) : X -> A * B :=
  fun x => (f x, g x).
Infix "&&&" := tuple (at level 50).

#[refine] Instance productBifunctor : Bifunctor prod :=
  { bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.
Proof.
Admitted.

Definition either A B X (f : A -> X) (g : B -> X) : A + B -> X := fun cp =>
  match cp with
  | inl a => f a
  | inr b => g b
  end.
Infix "|||" := either (at level 60).

Theorem coproductUniversalProperty
  : forall A B X (f : A -> X) (g : B -> X) h
  , h = f ||| g <-> f = h ∘ inl /\ g = h ∘ inr.
Proof.
  split
    ; [ intros ->
      | intros [-> ->]; apply functional_extensionality; intros [a | b]
      ]
    ; easy.
Qed.

Lemma coproductLemma1 : forall A B, @id (A + B) = inl ||| inr.
Proof.
  intros; apply coproductUniversalProperty; easy.
Qed.

Lemma coproductLemma2
  : forall A B X (f : A -> X) (g : B -> X)
  , f = (f ||| g) ∘ inl /\ g = (f ||| g) ∘ inr.
Proof.
  intros; apply coproductUniversalProperty; reflexivity.
Qed.

Lemma coproductLemma3
  : forall A B X X' (f : A -> X) (g : B -> X) (h : X -> X')
  , h ∘ (f ||| g) = h ∘ f ||| h ∘ g.
Proof.
  intros; apply coproductUniversalProperty.
  repeat rewrite compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2)
    ; easy.
Qed.

Lemma coproductLemma4
  : forall A A' B B' X (f : A -> A') (g : B -> B') (f' : A' -> X) (g' : B' -> X)
  , (f' ||| g') ∘ (inl ∘ f ||| inr ∘ g) = f' ∘ f ||| g' ∘ g.
Proof.
  intros.
  rewrite coproductLemma3.
  repeat rewrite <- compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2)
    ; reflexivity.
Qed.

#[refine] Instance coproductBifunctor : Bifunctor sum :=
  { bimap _ _ _ _ f g := inl ∘ f ||| inr ∘ g
  }.
Proof.
  symmetry; apply coproductLemma1.
  symmetry; repeat rewrite <- compose_assoc; apply coproductLemma4.
Defined.

Lemma coproductLemma4'
  : forall A A' B B' X (f : A -> A') (g : B -> B') (f' : A' -> X) (g' : B' -> X)
  , (f' ||| g') ∘ bimap f g = f' ∘ f ||| g' ∘ g.
Proof.
  exact @coproductLemma4.
Qed.

#[refine] Instance bifunctor1 `(FF : Functor F)
    : Bifunctor (fun A B => F A * F B) :=
  { bimap _ _ _ _ f g := bimap (fmap (F := F) f) (fmap (F := F) g)
  }.
Proof.
  all: intros.
  repeat rewrite functorsPreserveIdentityMorphisms
    ; apply bifunctorsPreserveIdentityMorphisms.
  repeat rewrite functorsPreserveComposition
    ; apply bifunctorsPreserveComposition.
Defined.

#[refine] Instance bifunctor2 `(FF : Functor F)
    : Bifunctor (fun A B => F (A * B)) :=
  { bimap _ _ _ _ f g := fmap (F := F) (bimap f g)
  }.
Proof.
  all: intros.
  rewrite bifunctorsPreserveIdentityMorphisms
    ; apply functorsPreserveIdentityMorphisms.
  rewrite bifunctorsPreserveComposition
    ; apply functorsPreserveComposition.
Defined.

Class NaturalTransformation
    `(FF : Functor F, FG : Functor G) (τ : forall A, F A -> G A) :=
  naturality : forall A B (f : A -> B), τ B ∘ fmap f = fmap f ∘ τ A.

Class NaturalTransformation'
    `(BFF : Bifunctor F, BFG : Bifunctor G) (τ' : forall A B, F A B -> G A B) :=
  naturality'
    : forall A A' B B' (f : A -> A') (g : B -> B')
    , τ' A' B' ∘ bimap f g = bimap f g ∘ τ' A B.

Definition bang A : A -> () := fun _ => tt.
Notation "!" := bang.

Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.

Definition λ A : () * A -> A := snd.

Definition ρ A : A * () -> A := fst.
Definition ρInverse A : A -> A * () := id &&& !.

Class LaxMonoidalFunctor `(FF : Functor F) :=
  { ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; NTμ : @NaturalTransformation' _ _ _ _ (@μ)
  ; associativity
    : forall A B C
    , fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α
  ; leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ
  ; rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ
  }.

#[refine] Instance compositeOfTwoLaxMonoidalFunctors
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    : LaxMonoidalFunctor (@compositeOfTwoFunctors F _ G _) :=
  { ε := fmap (F := G) (ε (F := F)) ∘ ε (F := G)
  ; μ _ _ := fmap (F := G) (μ (F := F) _ _) ∘ μ (F := G) _ _
  }.
Proof.
  all:
    intro; intros
    ; cbn
    ; change ((fmap (F := G) ∘ fmap (F := F)) ?f)
      with (fmap (F := G) (fmap (F := F) f))
    ; change ((G ∘ F) ?X) with (G (F X)).

  assert (H1 := NTμ (F := G) (fmap (F := F) f) (fmap (F := F) g)).
  assert (H2 := NTμ (F := F) f g)
    ; apply (f_equal (fmap (F := G))) in H2
    ; repeat rewrite functorsPreserveComposition in H2.
  cbn in H1, H2.
  rewrite compose_assoc; rewrite H1.
  rewrite <- compose_assoc; rewrite H2.
  reflexivity.

  assert (H1 := associativity (F := G) (F A) (F B) (F C)).
  assert (H2 := associativity (F := F) A B C)
    ; apply (f_equal (fmap (F := G))) in H2
    ; repeat rewrite functorsPreserveComposition in H2.
  assert (H3 := NTμ (F := G) (@id (F A)) (μ (F := F) B C))
    ; cbn in H3
    ; rewrite functorsPreserveIdentityMorphisms in H3.
  assert (H4 := NTμ (F := G) (μ (F := F) A B) (@id (F C)))
    ; cbn in H4
    ; rewrite functorsPreserveIdentityMorphisms in H4.
  rewrite <- (compose_id_left _ _ (@id (G (F A)))).
  rewrite <- (compose_id_left _ _ (@id (G (F C)))).
  repeat rewrite bifunctorsPreserveComposition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f); rewrite H3.
  change (?m ∘ ?k ∘ (?h ∘ ?g) ∘ ?f) with (m ∘ (k ∘ h) ∘ g ∘ f); rewrite H4.
  rewrite <- compose_assoc; rewrite H2.
  change (?m ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (m ∘ k ∘ (h ∘ g ∘ f)); rewrite H1.
  reflexivity.

  assert (H1 := leftUnitality (F := G) (F A)).
  assert (H2 := leftUnitality (F := F) A)
    ; apply (f_equal (fmap (F := G))) in H2
    ; repeat rewrite functorsPreserveComposition in H2.
  assert (H3 := NTμ (F := G) (ε (F := F)) (@id (F A)))
    ; cbn in H3
    ; rewrite functorsPreserveIdentityMorphisms in H3.
  rewrite <- (compose_id_left _ _ (@id (G (F A)))).
  rewrite bifunctorsPreserveComposition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f); rewrite H3.
  rewrite <- compose_assoc; rewrite H2.
  change (?m ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (m ∘ k ∘ (h ∘ g ∘ f)); rewrite H1.
  reflexivity.

  assert (H1 := rightUnitality (F := G) (F A)).
  assert (H2 := rightUnitality (F := F) A)
    ; apply (f_equal (fmap (F := G))) in H2
    ; repeat rewrite functorsPreserveComposition in H2.
  assert (H3 := NTμ (F := G) (@id (F A)) (ε (F := F)))
    ; cbn in H3
    ; rewrite functorsPreserveIdentityMorphisms in H3.
  rewrite <- (compose_id_left _ _ (@id (G (F A)))).
  rewrite bifunctorsPreserveComposition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f); rewrite H3.
  rewrite <- compose_assoc; rewrite H2.
  change (?m ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (m ∘ k ∘ (h ∘ g ∘ f)); rewrite H1.
  reflexivity.
Defined.

Class MonoidalNaturalTransformation
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    (θ : forall A, F A -> G A) :=
  { NTθ :> @NaturalTransformation _ _ _ _ θ
  ; compatibilityWithUnit : ε (F := G) = θ () ∘ ε (F := F)
  ; compatibilityWithProduct
    : forall A B
    , μ (F := G) _ _ ∘ bimap (θ A) (θ B) = θ (A * B) ∘ μ (F := F) _ _
  }.

(* Adjunction isomorphism *)
Definition curry A B C : (A * B -> C) -> (A -> (B -> C)) :=
  fun f a b => f (a, b).

Definition uncurry A B C : (A -> (B -> C)) -> (A * B -> C) :=
  fun f '(a, b) => f a b.

Theorem uncurryIsTheInverseOfCurry
  : forall A B C
  , uncurry ∘ curry = @id (A * B -> C) /\ curry ∘ uncurry = @id (A -> (B -> C)).
Proof.
  split
    ; extensionality f
    ; apply functional_extensionality
    ; unfold "∘", curry, uncurry
    ; [intros [a b]; reflexivity | intro; apply eta_expansion].
Qed.

(* Canonical strength *)
Definition strength `{FF : Functor F} A B : A * F B -> F (A * B) :=
  uncurry (fmap ∘ curry id).

Inductive polynomialFunctorExpression : Type :=
  | identityFunctor : polynomialFunctorExpression
  | constantFunctor : Type -> polynomialFunctorExpression
  | product : polynomialFunctorExpression
      -> polynomialFunctorExpression
      -> polynomialFunctorExpression
  | coproduct : polynomialFunctorExpression
      -> polynomialFunctorExpression
      -> polynomialFunctorExpression
  | composite : polynomialFunctorExpression
      -> polynomialFunctorExpression
      -> polynomialFunctorExpression.

Infix "|*|" := product (at level 40).
Infix "|+|" := coproduct (at level 50).
Infix "|∘|" := composite (at level 40).

Reserved Notation "⟦ F ⟧".

Fixpoint denotation H : Type -> Type :=
  match H with
  | identityFunctor   => id
  | constantFunctor X => fun _ => X
  | F1 |*| F2         => fun A => ⟦F1⟧ A * ⟦F2⟧ A
  | F1 |+| F2         => fun A => ⟦F1⟧ A + ⟦F2⟧ A
  | G |∘| F           => ⟦G⟧ ∘ ⟦F⟧
  end
where "⟦ F ⟧" := (denotation F).

Fixpoint pfmap H A B : (A -> B) -> (⟦H⟧ A -> ⟦H⟧ B) :=
  match H with
  | identityFunctor   => id
  | constantFunctor X => fun _ => id
  | F1 |*| F2         => fun f => bimap (pfmap F1 f) (pfmap F2 f)
  | F1 |+| F2         => fun f => bimap (pfmap F1 f) (pfmap F2 f)
  | G |∘| F           => pfmap G ∘ pfmap F
  end.

#[refine] Instance polynomialFunctor H : Functor ⟦H⟧ :=
  { fmap := @pfmap H
  }.
Proof.
  all:
    induction H
    ; cbn [pfmap]; intros
    ; try change ((pfmap ?G ∘ pfmap ?F) ?f) with (pfmap G (pfmap F f))
    ; try rewrite IHpolynomialFunctorExpression2
    ; try rewrite IHpolynomialFunctorExpression1
    ; try rewrite bifunctorsPreserveIdentityMorphisms
    ; try rewrite bifunctorsPreserveComposition
    ; reflexivity.
Defined.

#[refine] Instance identityLaxMonoidalFunctor
    : LaxMonoidalFunctor (@polynomialFunctor identityFunctor) :=
  { ε := id
  ; μ A B := id
  }.
Proof.
  all:
    intro; intros; cbn
    ; try repeat rewrite bifunctorsPreserveIdentityMorphisms
    ; reflexivity.
Defined.

Section s.
  Context `{LMFT : LaxMonoidalFunctor T}.

  Definition pure A : A -> T A := fmap ρ ∘ strength () ∘ bimap id ε ∘ ρInverse.

  Fixpoint traverse H A : ⟦H⟧ (T A) -> T (⟦H⟧ A) :=
    match H with
    | identityFunctor   => id
    | constantFunctor X => pure
    | F1 |*| F2         =>
        μ (⟦F1⟧ A) (⟦F2⟧ A)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | F1 |+| F2         =>
        (fmap inl ||| fmap inr)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | G |∘| F           => traverse G (⟦F⟧ A) ∘ fmap (traverse F A)
    end.
End s.

Theorem unitarity : forall H A, traverse (T := ⟦identityFunctor⟧) H A = id.
Proof.
  induction H
    ; intro; cbn [traverse]
    ; try rewrite IHpolynomialFunctorExpression1
    ; try rewrite IHpolynomialFunctorExpression2
    ; try unfold pure, strength
    ; try rewrite bifunctorsPreserveIdentityMorphisms
    ; try rewrite functorsPreserveIdentityMorphisms
    ; cbn
    ; try
      ( rewrite compose_id_left
      ; change (uncurry (curry ?f)) with ((uncurry ∘ curry) f)
      ; rewrite (proj1 uncurryIsTheInverseOfCurry)
      )
    ; try (rewrite compose_id_right; symmetry; apply coproductLemma1)
    ; reflexivity.
Qed.

Instance traverseNaturalTransformation
  `{LMFT : LaxMonoidalFunctor T} H
  : @NaturalTransformation (⟦H⟧ ∘ T) _ (T ∘ ⟦H⟧) _ (traverse (T := T) H).
Proof.
Admitted.

Theorem linearity
  : forall `{LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G} H A
  , fmap (F := G) (traverse (T := F) H A) ∘ traverse (T := G) H (F A)
    = traverse (T := G ∘ F) H A.
Proof.
  induction H; try rename H into F1, H0 into F2; cbn [traverse]; intro.

  rewrite functorsPreserveIdentityMorphisms; reflexivity.

  admit.

  rewrite functorsPreserveComposition.
  change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; generalize
      (NTμ (F := G) (traverse (T := F) F1 A) (traverse (T := F) F2 A))
    ; cbn
    ; intros <-.
  change (?k ∘ (?h ∘ ?g) ∘ ?f) with (k ∘ h ∘ (g ∘ f))
    ; rewrite <- bifunctorsPreserveComposition.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  reflexivity.

  rewrite <- compose_assoc; rewrite coproductLemma3.
  repeat rewrite <- functorsPreserveComposition.
  simpl bimap at - 3 4.
  repeat rewrite compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2).
  repeat rewrite <- compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2).
  repeat rewrite functorsPreserveComposition.
  rewrite <- coproductLemma4'.
  rewrite compose_assoc; rewrite <- bifunctorsPreserveComposition.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  reflexivity.

  rewrite <- IHpolynomialFunctorExpression1.
  rewrite <- (f_equal (fmap (F := ⟦F1⟧)) (IHpolynomialFunctorExpression2 A)).
  repeat rewrite functorsPreserveComposition.
  change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; generalize
      (@traverseNaturalTransformation G _ _ F1 (⟦F2⟧ (F A)) (F (⟦F2⟧ A)))
    ; cbn
    ; intros ->.
  reflexivity.
Admitted.











(*
Section s'.
  Context `{LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G}.
  Variable H : polynomialFunctorExpression.
  Variable A : Type.

  Theorem linearity
    : fmap (F := G) (traverse (T := F) H A) ∘ traverse (T := G) H (F A)
      = traverse (T := G ∘ F) H A.
  Proof.
    induction H.
    cbn.
    rewrite functorsPreserveIdentityMorphisms.
    reflexivity.

    cbn.
    unfold pure.
    cbn.
    unfold strength.
    cbn.
    admit.
Check fmap (F := G) (traverse (T := F) (p1 |*| p2) A).
Check traverse (T := G) (p1 |*| p2) (F A).
    Set Printing Implicit.
    cbn.
    Set Printing Implicit.
  Admitted.
End s'.

Check
fmap (fmap ρ ∘ uncurry (fmap ∘ curry id) ∘ bimap id ε ∘ ρInverse)
∘ (fmap ρ ∘ uncurry (fmap ∘ curry id) ∘ bimap id ε ∘ ρInverse)
=
(fmap ∘ fmap) ρ ∘ uncurry (fmap ∘ fmap ∘ curry id) ∘ bimap id (fmap ε ∘ ε)
∘ ρInverse


fmap (fmap ρ) ∘ fmap (uncurry (fmap ∘ curry id)) ∘ fmap (bimap id ε)
∘ uncurry (fmap ∘ curry id) ∘ bimap id ε ∘ ρInverse
=
fmap (fmap ρ) ∘ uncurry (fmap ∘ fmap ∘ curry id) ∘ bimap id (fmap ε ∘ ε)
∘ ρInverse


fmap (uncurry (fmap ∘ curry id)) ∘ fmap (bimap id ε)
∘ uncurry (fmap ∘ curry id) ∘ bimap id ε
=
uncurry (fmap ∘ fmap ∘ curry id) ∘ bimap id (fmap ε ∘ ε)




Check @traverse.
Check .
Theorem linearity : fmap (F := G) (traverse (T := F) H A) ∘ traverse (T := G) H (⟦F⟧ A) = traverse (T := G ∘ F) H.

HGFA -> GFHA
HGFA -traverse (T := G) H (F A)-> GHFA -fmap (F := G) (traverse (T := F) H A)-> GFHA

(* now linearity *)

(************)


(* Counit *)
Definition eval B C : (B -> C) * B -> C := uncurry id.

(* Unit *)
Definition pair' A B : A -> (B -> (A * B)) := curry id.



Class MonoidalNaturalTransformation
    `(LMFF : LaxMonoidalFunctor F) `(LMFG : LaxMonoidalFunctor G) :=
  { θ : forall A, F A -> G A
  ; compatibilityWithProduct
    : forall A B, μ (F := G) A B ∘ bimap θ θ = θ ∘ μ (F := F) A B
  ; compatibilityWithUnit : θ ∘ ε (F := F) = ε (F := G)
  }.

Section s.
  Context `{LMFT : LaxMonoidalFunctor T}.

  Definition strength A B : A * T B -> T (A * B) := uncurry (fmap ∘ pair').
  Definition pure A : A -> T A := fmap fst ∘ strength ∘ bimap id ε ∘ ρInverse.

  Fixpoint traverse H A : ⟦H⟧ (T A) -> T (⟦H⟧ A) :=
    match H with
    | identityFunctor   => id
    | constantFunctor X => pure
    | F1 |*| F2         =>
        μ (⟦F1⟧ A) (⟦F2⟧ A)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | F1 |+| F2         =>
        (fmap inl ||| fmap inr)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | G |∘| F           => traverse G (⟦F⟧ A) ∘ fmap (traverse F A)
    end.
End s.


(* strictly α is also a natural transformation (natural in 3 arguments), but better to ignore/avoid if possible and else separate naturality theorem/lemma *)






Definition bang A : A -> () := fun _ => tt.
Notation "!" := @bang.

Definition tuple A B X (f : X -> A) (g : X -> B) : X -> A * B :=
  fun x => (f x, g x).
Infix "&&&" := tuple (at level 50).

Instance productBifunctor : Bifunctor prod :=
  fun _ _ _ _ f g => f ∘ fst &&& g ∘ snd.

Definition either A B X (f : A -> X) (g : B -> X) : A + B -> X := fun cp =>
  match cp with
  | inl a => f a
  | inr b => g b
  end.
Infix "|||" := either (at level 60).

Instance coproductBifunctor : Bifunctor sum :=
  fun _ _ _ _ f g => inl ∘ f ||| inr ∘ g.

(* φ *)
Definition curry A B C : (A * B -> C) -> (A -> (B -> C)) :=
  fun f a b => f (a, b).

(* φ^{-1} *)
Definition uncurry A B C : (A -> (B -> C)) -> (A * B -> C) :=
  fun f '(a, b) => f a b.

(* Counit *)
Definition eval B C : (B -> C) * B -> C := uncurry id.

(* Unit *)
Definition pair' A B : A -> (B -> (A * B)) := curry id.

(* Associator *)
Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.

Definition αInverse A B C : (A * B) * C -> A * (B * C) :=
  fst ∘ fst &&& (snd ∘ fst &&& snd).

(* Left unitor *)
Definition λ A : () * A -> A := snd.
Definition λInverse A : A -> () * A := ! A &&& id.

(* Right unitor *)
Definition ρ A : A * () -> A := fst.
Definition ρInverse A : A -> A * () := id &&& ! A.

Fixpoint pfmap H A B : (A -> B) -> (⟦H⟧ A -> ⟦H⟧ B) :=
  match H with
  | identityFunctor   => id
  | constantFunctor X => fun _ => id
  | F1 |*| F2         => fun f => bimap (pfmap F1 f) (pfmap F2 f)
  | F1 |+| F2         => fun f => bimap (pfmap F1 f) (pfmap F2 f)
  | G |∘| F           => pfmap G ∘ pfmap F
  end.

Instance polynomialFunctor F : Functor ⟦F⟧ := @pfmap F.

Generalizable All Variables.

(* Class NaturalTransformation for functors *)
(* Class NaturalTransformation' for bifunctors *)

Class LaxMonoidalFunctor `(FF : Functor F) :=
  { ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; μNaturalInBothArguments
    : forall A A' B B' (f : A -> A') (g : B -> B')
    , μ ∘ bimap (fmap f) (fmap g) = fmap (bimap f g) ∘ μ
  ; associativity
    : forall A B C, fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α
  ; leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ
  ; rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ
  }.

(* Cat composition *)
Instance compositeOfTwoFunctors `(FF : Functor F, FG : Functor G)
    : Functor (G ∘ F) :=
  { fmap _ _ f := fmap (F := G) (fmap (F := F) f)
  }.

Check compositeOfTwoFunctors.
Check @compositeOfTwoFunctors.
(* MonCat composition *)
#[refine] Instance compositeOfTwoLaxMonoidalFunctors
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    : LaxMonoidalFunctor (@compositeOfTwoFunctors F _ G _) :=
  { ε := fmap (F := G) (ε (F := F)) ∘ ε (F := G)
  ; μ A B := fmap (F := G) (μ (F := F) A B) ∘ μ (F := G) (F A) (F B)
  }.
Proof.
  destruct LMFF
    as [εF μF μNaturalityF associativityF leftUnitalityF rightUnitalityF].
  destruct LMFG
    as [εG μG μNaturalityG associativityG leftUnitalityG rightUnitalityG].
  unfold μ.
  Check μNaturalityG.



  (* use naturality of μ twice to rewrite *)
  (* use associativity of G, use G preserves associativity diagram of F *)



  intros *.
  Check μ (F := G) (F A) (F B).
  Check fmap (F := G) (μ (F := F) A B) ∘ μ (F := G) (F A) (F B).



    {}.
  Check ε (F := F).
  Check .



  { ε := fmap (F := G) (ε (F := F)) ∘ ε (F := G)
  ; μ := fmap μ ∘ μ
  }.

(* Program Instance prod_eqb `(EA : EqDec A, EB : EqDec B) : EqDec (A * B) :=*)

#[refine] Instance identityLaxMonoidalFunctor
    : LaxMonoidalFunctor (@polynomialFunctor identityFunctor) :=
  { ε := id
  ; μ A B := id
  }.
Proof.
  all: trivial.
Defined.

Class MonoidalNaturalTransformation
    `(LMFF : LaxMonoidalFunctor F) `(LMFG : LaxMonoidalFunctor G) :=
  { θ : forall A, F A -> G A
  ; compatibilityWithProduct
    : forall A B, μ (F := G) A B ∘ bimap θ θ = θ ∘ μ (F := F) A B
  ; compatibilityWithUnit : θ ∘ ε (F := F) = ε (F := G)
  }.

Section s.
  Context `{LMFT : LaxMonoidalFunctor T}.

  Definition strength A B : A * T B -> T (A * B) := uncurry (fmap ∘ pair').
  Definition pure A : A -> T A := fmap fst ∘ strength ∘ bimap id ε ∘ ρInverse.

  Fixpoint traverse H A : ⟦H⟧ (T A) -> T (⟦H⟧ A) :=
    match H with
    | identityFunctor   => id
    | constantFunctor X => pure
    | F1 |*| F2         =>
        μ (⟦F1⟧ A) (⟦F2⟧ A)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | F1 |+| F2         =>
        (fmap inl ||| fmap inr)
        ∘ bimap (traverse F1 A) (traverse F2 A)
    | G |∘| F           => traverse G (⟦F⟧ A) ∘ fmap (traverse F A)
    end.
End s.

Lemma productLemma : forall A B, fst &&& snd = @id (A * B).
Proof.
  intros.
  apply functional_extensionality.
  symmetry.
  apply surjective_pairing.
Qed.

Lemma coproductLemma : forall A B, inl ||| inr = @id (A + B).
Proof.
  intros.
  apply functional_extensionality.
  intros [a | b]; reflexivity.
Qed.

Theorem productPreservesIdentityMorphisms
  : forall A B
  , bimap (F := prod) (@id A) (@id B) = id.
Proof.
  intros; apply productLemma.
Qed.

Theorem productPreservesComposition
  : forall A A' A'' B B' B''
    (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
  , bimap (F := prod) f' g' ∘ bimap f g = bimap (f' ∘ f) (g' ∘ g).
Proof.
Admitted.

Theorem coproductPreservesIdentityMorphisms
  : forall A B
  , bimap (F := sum) (@id A) (@id B) = id.
Proof.
  intros; apply coproductLemma.
Qed.

Theorem coproductPreservesComposition
  : forall A A' A'' B B' B''
    (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
  , bimap (F := sum) f' g' ∘ bimap f g = bimap (f' ∘ f) (g' ∘ g).
Proof.
Admitted.

Theorem polynomialFunctorsPreserveIdentityMorphisms
  : forall H A, fmap (F := ⟦H⟧) (@id A) = id.
Proof.
  induction H.
  reflexivity.
  reflexivity.

  intro.
  unfold fmap; simpl; change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  apply productPreservesIdentityMorphisms.

  intro.
  unfold fmap; simpl; change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  apply coproductPreservesIdentityMorphisms.

  intro.
  unfold fmap.
  simpl.
  unfold "∘".
  repeat change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite IHpolynomialFunctorExpression2
    ; apply IHpolynomialFunctorExpression1.
Qed.

Theorem unitarity : forall H A, traverse (T := ⟦identityFunctor⟧) H A = id.
Proof.
  induction H.
  reflexivity.
  reflexivity.

  intro.
  simpl.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite productPreservesIdentityMorphisms.
  reflexivity.

  intro.
  simpl.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite coproductPreservesIdentityMorphisms.
  rewrite compose_id_right.
  apply coproductLemma.

  intro.
  simpl.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite polynomialFunctorsPreserveIdentityMorphisms.
  reflexivity.
Qed.

(* compatibilityWithStrength *)
(* like compatProduct *)

(* θ is a natural transformation, create/define class *)
Theorem θNaturality
  : forall `(MNT : MonoidalNaturalTransformation F G) A B (f : A -> B)
  , θ B ∘ fmap f = fmap f ∘ θ A.
Admitted.

Check @strength.
Check strength.
(* try on paper and write unit and counit for curry id and uncurry id *)
(* try without functional extensionality *)
Theorem compatibilityWithStrength
  : forall `(MNT : MonoidalNaturalTransformation F G) A B
  , strength B ∘ bimap id (θ B) = θ (A * B) ∘ strength B.
Proof.
  intros.
  unfold strength, uncurry, bimap, productBifunctor, pair', curry, id.
  apply functional_extensionality.
  intros [a fb].
  unfold compose.
  simpl.
  change (fmap ?f (θ ?A fb)) with ((fmap f ∘ θ A) fb).
  change (θ ?B (fmap ?f fb)) with ((θ B ∘ fmap f) fb).
  rewrite θNaturality.
  reflexivity.
Qed.

(*
Also: ε = pure e
*)

(* see applicative morphism jaskelioff *)
(* question is if this is stronger than compatwithunit or not. *)
Lemma compatibilityWithPure
  : forall `(MNT : MonoidalNaturalTransformation F G) A
  , θ A ∘ pure (T := F) = pure (T := G).
Proof.
(* see sketch *)
(* nahhhh -> maybe maybe also try to prove with the other definition of pure *)
Admitted.

Theorem naturality
  : forall H `(MNT : MonoidalNaturalTransformation F G) A
  , traverse (T := G) H A ∘ fmap (F := ⟦H⟧) (θ A)
    = θ (⟦H⟧ A) ∘ traverse (T := F) H A.
Proof.
  induction H.
  reflexivity.
  symmetry; apply compatibilityWithPure.

  intros.
  unfold fmap.
  simpl.
  change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite compose_assoc.
  rewrite productPreservesComposition.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite <- productPreservesComposition.
  rewrite <- compose_assoc.
  rewrite compatibilityWithProduct.
  reflexivity.

  intros.
  unfold fmap.
  simpl.
  change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite compose_assoc.
  rewrite coproductPreservesComposition.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite <- coproductPreservesComposition.
  rewrite <- compose_assoc.
  (* see sketch (use naturality of θ) *)
  (* maybe after linearity 'work out' on paper to see if I do any unnecessary work *)

  (* maybe first continue with linearity to see how hard it is *)
Admitted.

Theorem linearity
  : forall H `(MNT : MonoidalNaturalTransformation F G) A
  , fmap (traverse (T := F) H A) ∘ traverse (T := G) H (F A) = traverse (T := G ∘ F) H A.



(* prove traverse laws *)

(* !! I actually think polynomial functors are STRONG monoidal (functors) *)
(* are polynomial functors itself lax monoidal functors? *)
(* don't forget all the coherence theorems in the process *)




(* 
Applicative functor = lax monoidal functor with tensorial strength.
Because Coq (Type) is (cartesian) closed (and "every closed category may be seen as a category enriched over itself"), every (lax) monoidal functor from Coq (Type) to Coq (Type) has a canonical strength.
So applicative functor = lax monoidal functor basically.



(all functors from Coq (Type) to Coq (Type) are strong)
In a ccc, enrichment = strength

also see chapter 6 http://brendanfong.com/programmingcats_files/cats4progs-DRAFT.pdf
lax monoidal functor
=
applicative functor



https://ncatlab.org/nlab/show/tensorial+strength
"(And going back the other way, from an enrichment to a strength, is also easy – there you have to dualize. That is, instead of using the evaluation which is the counit of the hom-tensor adjunction, you use the coevaluation which is the unit. )"

"After some work, one can convince oneself that the notions of strength and enrichment for endofunctors on closed monoidal categories really are equivalent notions."

"A functor T : V -> V with a strength is the same thing as a V-enrichment on T"

coevolution, unit hom-tensor adjunction?


Lax monoidal functors are often simply called monoidal functors (I think this is the case in Mac Lane as well)
(the other case being called 'strong')

https://ncatlab.org/nlab/show/closed+functor
^^ see for 'lax closed functor'
^^ see example 3.1 for lax monoidal functor stuff!!


https://openaccess.city.ac.uk/id/eprint/1141/1/Constructors.pdf
see 2.2

"lax monoidal functors C -> C are applicative if C is ccc (cartesian closed category)" verify??

98 Mac Lane
Evaluation map
Cartesian Closed Categories

184
Closed categories


Closed functors??

https://arxiv.org/pdf/1406.4823v1.pdf


Day convolution
https://ncatlab.org/nlab/show/Day+convolution

Yoneda

https://bartoszmilewski.com/2017/02/06/applicative-functors/

Ends coends

"component of _ at _"

Interesting: Mac Lane: each functor C -> B of one variable may be treated as a bifunctor C^op x C -> B, dummy in the first variable (page 219)
*)
(*
Section s.
  Context `{FT : Functor T}.

  Variable ε : () -> T ().
  Variable μ : forall A B, T A * T B -> T (A * B).

  Variable associativity
    : forall A B C
    , fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α.

  Variable leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ.
  Variable rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ.

  (* Canonical tensorial strength for T *)
  Definition strengthT A B : A * T B -> T (A * B) := uncurry (fmap ∘ pair).

  Definition pure A : A -> T A :=
    fmap fst ∘ strengthT ∘ bimap id ε ∘ ρInverse.

  Fixpoint traverse H A : ⟦H⟧ (T A) -> T (⟦H⟧ A) :=
    match H with
    | identityFunctor   => id
    | constantFunctor X => pure
    | F1 |*| F2         => μ ∘ bimap (traverse F1 A) (traverse F2 A)
    | F1 |+| F2         =>
        (fmap inl ||| fmap inr) ∘ bimap (traverse F1 A) (traverse F2 A)
    | G |∘| F           => traverse G (⟦F⟧ A) ∘ fmap (traverse F A)
    end.

  (* Variable θ : forall X, F X -> G X. *)
End s.
*)
(*
(* Associator *)
Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.

Definition αInverse A B C : (A * B) * C -> A * (B * C) :=
  fst ∘ fst &&& (snd ∘ fst &&& snd).

(* Left unitor *)
Definition λ A : () * A -> A := snd.
Definition λInverse A : A -> () * A := ! A &&& id.

(* Right unitor *)
Definition ρ A : A * () -> A := fst.
Definition ρInverse A : A -> A * () := id &&& ! A.

Class LaxMonoidalFunctor `(FF : Functor F) :=
  { ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; μNaturalInBothArguments
    : forall A A' B B' (f : A -> A') (g : B -> B')
    , μ ∘ bimap (fmap f) (fmap g) = fmap (bimap f g) ∘ μ
  ; associativity
    : forall A B C, fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α
  ; leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ
  ; rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ
  }.
*)
*)
