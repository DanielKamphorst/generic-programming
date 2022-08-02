Require Import Program.

Set Asymmetric Patterns.
Set Contextual Implicit.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Generalizable All Variables.

Open Scope type_scope.

Arguments compose {_ _ _} _ _ _ /.
Arguments pair_equal_spec : default implicits.

Class Functor F :=
  { fmap : forall A B, (A -> B) -> (F A -> F B)
  ; functorsPreserveIdentities : forall A, fmap id = @id (F A)
  ; functorsPreserveComposition
    : forall A B C (f : A -> B) (g : B -> C)
    , fmap (g ∘ f) = fmap g ∘ fmap f
  }.

Arguments fmap _ {_ _ _} _.
Arguments functorsPreserveIdentities _ {_} _.
Arguments functorsPreserveComposition _ {_ _ _ _} _ _.

Class Bifunctor F :=
  { bimap : forall A A' B B', (A -> A') * (B -> B') -> (F (A, B) -> F (A', B'))
  ; bifunctorsPreserveIdentities
    : forall A B, bimap (@id A, @id B) = @id (F (A, B))
  ; bifunctorsPreserveComposition
    : forall `(f : A -> A', f' : A' -> A'', g : B -> B', g' : B' -> B'')
    , bimap (f' ∘ f, g' ∘ g) = bimap (f', g') ∘ bimap (f, g)
  }.

Arguments bimap _ {_ _ _ _ _}.
Arguments bifunctorsPreserveIdentities _ {_} _ _.
Arguments bifunctorsPreserveComposition _ {_} {_ _} _ {_} _ {_ _} _ {_} _.

Ltac rewrite' F H := let H' := fresh in
  match type of F with
  | Type        -> Type =>
      assert (H' := f_equal (fmap F) H)
      ; repeat rewrite (functorsPreserveComposition F) in H'
  | Type * Type -> Type =>
      assert
        (H' := f_equal (bimap F) (proj2 pair_equal_spec (conj (fst H) (snd H))))
      ; repeat rewrite (bifunctorsPreserveComposition F) in H'
  end
  ; try (rewrite H'; clear H').

Class NaturalTransformation `{Functor F, Functor G}
    (α : forall A, F A -> G A) :=
  naturality : forall `(f : A -> B), α B ∘ fmap F f = fmap G f ∘ α A.

Class NaturalTransformation' `{Bifunctor F, Bifunctor G}
    (α : forall A B, F (A, B) -> G (A, B)) :=
  naturality'
    : forall `(f : A -> A', g : B -> B')
    , α A' B' ∘ bimap F (f, g) = bimap G (f, g) ∘ α A B.

Notation curry f := (fun a b => f (a, b)).
Notation uncurry f := (fun '(a, b) => f a b).

Notation prod' := (uncurry prod).
(* Definition prod' : Type * Type -> Type := uncurry prod. *)

(* new: F^2 := Lim(F ∘ D) where D = {a   b}. *)
(* F^2 := × ∘ (F × F) *)
Notation sup2 F := (fun '(A, B) => F A * F B).
(* Definition sup2 F : Type * Type -> Type := fun '(A, B) => F A * F B. *)

(* new: F_2 := F(Lim D) where D = {a   b}. *)
(* F_2 := F ∘ × *)
Notation sub2 F := (fun '(A, B) => F (A * B)).
(* Definition sub2 F : Type * Type -> Type := fun '(A, B) => F (A * B). *)

Definition tuple `(f : X -> A, g : X -> B) : X -> A * B := fun x => (f x, g x).
Infix "&&&" := tuple (at level 50).

Theorem productUniversalProperty
  : forall `(f : X -> A, g : X -> B) h
  , h = f &&& g <-> fst ∘ h = f /\ snd ∘ h = g.
Proof.
  split.
  now intros ->.
  intros [<- <-]
    ; apply functional_extensionality; intro
    ; apply surjective_pairing.
Qed.

#[refine] Instance productBifunctor : Bifunctor prod' :=
  { bimap _ _ _ _ '(f, g) := f ∘ fst &&& g ∘ snd
  }.
Proof.
  all: symmetry; now apply (proj2 productUniversalProperty).
Defined.

#[refine] Instance sup2Bifunctor `{Functor F} : Bifunctor (sup2 F) :=
  { bimap _ _ _ _ '(f, g) := bimap prod' (fmap F f, fmap F g)
  }.
Proof.
  all: intros.

  repeat rewrite functorsPreserveIdentities.
  apply (bifunctorsPreserveIdentities prod').

  now rewrite' (uncurry prod)
    ( functorsPreserveComposition F f f'
    , functorsPreserveComposition F g g'
    ).
Defined.

#[refine] Instance sub2Bifunctor `{Functor F} : Bifunctor (sub2 F) :=
  { bimap _ _ _ _ '(f, g) := fmap F (bimap prod' (f, g))
  }.
Proof.
  all: intros.

  rewrite bifunctorsPreserveIdentities.
  apply functorsPreserveIdentities.

  now rewrite' F (bifunctorsPreserveComposition prod' f f' g g').
Defined.

(* Associator *)
Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.
Arguments α : clear implicits.

(* Left unitor *)
Definition λ A : () * A -> A := snd.
Arguments λ : clear implicits.

(* Right unitor *)
Definition ρ A : A * () -> A := fst.
Arguments ρ : clear implicits.

Definition bang A : A -> () := fun _ => tt.
Notation "!" := bang.

Definition ρInverse A : A -> A * () := id &&& !.
Arguments ρInverse : clear implicits.

Class LaxMonoidalFunctor F :=
  { FF :> Functor F
  ; ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; NTμ : NaturalTransformation' (@μ)
  ; associativity
    : forall A B C
    , fmap F (α A B C) ∘ μ ∘ bimap prod' (id, μ)
      = μ ∘ bimap prod' (μ, id) ∘ α (F A) (F B) (F C)
  ; leftUnitality : forall A, fmap F (λ A) ∘ μ ∘ bimap prod' (ε, id) = λ (F A)
  ; rightUnitality : forall A, fmap F (ρ A) ∘ μ ∘ bimap prod' (id, ε) = ρ (F A)
  }.

Arguments ε _ {_}.
Arguments μ _ {_} _ _.
Arguments NTμ _ {_ _ _} _ {_ _} _.
Arguments associativity _ {_} _ _ _.
Arguments leftUnitality _ {_} _.
Arguments rightUnitality _ {_} _.

Class MonoidalNaturalTransformation
    `{LaxMonoidalFunctor F, LaxMonoidalFunctor G} (θ : forall A, F A -> G A) :=
  { NTθ :> NaturalTransformation θ
  ; compatibilityWithUnit : ε G = θ () ∘ ε F
  ; compatibilityWithProduct
    : forall A B, μ G A B ∘ bimap prod' (θ A, θ B) = θ (A * B) ∘ μ F A B
  }.

Arguments NTθ {_ _ _ _} _ {_ _ _} _.
Arguments compatibilityWithUnit {_ _ _ _} _ {_}.
Arguments compatibilityWithProduct {_ _ _ _} _ {_} _ _.

#[refine] Instance compositeOfTwoFunctors `{Functor G, Functor F}
    : Functor (G ∘ F) :=
  { fmap _ _ := fmap G ∘ fmap F
  }.
Proof.
  all: intros; cbn ["∘"].
  now repeat rewrite functorsPreserveIdentities.
  now rewrite' G (functorsPreserveComposition F f g).
Defined.

Arguments compositeOfTwoFunctors _ {_} _ {_}.

Lemma sup2Definition
  : forall `{Functor F} `(f : A -> A', g : B -> B')
  , bimap (sup2 F) (f, g) = bimap prod' (fmap F f, fmap F g).
Proof.
  reflexivity.
Qed.

Arguments sup2Definition _ {_} {_ _} _ {_ _} _.

Lemma sub2Definition
  : forall `{Functor F} `(f : A -> A', g : B -> B')
  , bimap (sub2 F) (f, g) = fmap F (bimap prod' (f, g)).
Proof.
  reflexivity.
Qed.

Arguments sub2Definition _ {_} {_ _} _ {_ _} _.

#[refine] Instance compositeOfTwoLaxMonoidalFunctors
    `{LMFG : LaxMonoidalFunctor G, LMFF : LaxMonoidalFunctor F}
    : LaxMonoidalFunctor (G ∘ F) :=
  { ε := fmap G (ε F) ∘ ε G
  ; μ A B := fmap G (μ F A B) ∘ μ G (F A) (F B)
  }.
Proof.
  all:
    intro; intros
    ; assert (H' : forall A, id = fmap G (@id (F A)) ∘ id)
      by (intros; now rewrite functorsPreserveIdentities).

  rewrite sup2Definition; rewrite sub2Definition
    ; cbn ["∘" compositeOfTwoFunctors fmap]
    ; rewrite <- sup2Definition; rewrite <- sub2Definition.
  rewrite compose_assoc; rewrite (NTμ G).
  rewrite <- compose_assoc; rewrite sub2Definition; rewrite <- sup2Definition.
  now rewrite' G (NTμ F f g).

  all: cbn [fmap compositeOfTwoFunctors "∘"].

  rewrite' (uncurry prod) (H' A, eq_refl (fmap G (μ F B C) ∘ μ G (F B) (F C))).
  repeat rewrite <- sup2Definition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f)
    ; rewrite (NTμ G).
  rewrite sub2Definition.
  rewrite <- compose_assoc; rewrite' G (associativity F A B C).
  change (?m ∘ ?k ∘ ?h ∘ ?g ∘ ?f) with (m ∘ k ∘ (h ∘ g ∘ f))
    ; rewrite (associativity G).
  rewrite <- sub2Definition.
  change (?m ∘ ?k ∘ (?h ∘ ?g ∘ ?f)) with (m ∘ (k ∘ h) ∘ g ∘ f)
    ; rewrite <- (NTμ G).
  now rewrite' (uncurry prod)
    ( eq_refl (fmap G (μ F A B) ∘ μ G (F A) (F B))
    , H' C
    ).

  rewrite' (uncurry prod) (eq_refl (fmap G (ε F) ∘ ε G), H' A).
  rewrite <- sup2Definition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f)
    ; rewrite (NTμ G).
  rewrite sub2Definition.
  rewrite <- compose_assoc; rewrite' G (leftUnitality F A).
  apply (leftUnitality G).

  rewrite' (uncurry prod) (H' A, eq_refl (fmap G (ε F) ∘ ε G)).
  rewrite <- sup2Definition.
  change (?m ∘ (?k ∘ ?h) ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f)
    ; rewrite (NTμ G).
  rewrite sub2Definition.
  rewrite <- compose_assoc; rewrite' G (rightUnitality F A).
  apply (rightUnitality G).
Defined.

Arguments compositeOfTwoLaxMonoidalFunctors _ {_} _ {_}.

Definition either `(f : A -> X, g : B -> X) : A + B -> X := fun cp =>
  match cp with
  | inl a => f a
  | inr b => g b
  end.
Infix "|||" := either (at level 60).

Theorem coproductUniversalProperty
  : forall `(f : A -> X, g : B -> X) h
  , h = f ||| g <-> f = h ∘ inl /\ g = h ∘ inr.
Proof.
  split.
  now intros ->.
  intros [-> ->]; apply functional_extensionality; now intros [a | b].
Qed.

Notation sum' := (uncurry sum).

#[refine] Instance coproductBifunctor : Bifunctor sum' :=
  { bimap _ _ _ _ '(f, g) := inl ∘ f ||| inr ∘ g
  }.
Proof.
  all: symmetry; now apply (proj2 coproductUniversalProperty).
Defined.

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
  | F1 |*| F2         => fun f => bimap prod' (pfmap F1 f, pfmap F2 f)
  | F1 |+| F2         => fun f => bimap sum' (pfmap F1 f, pfmap F2 f)
  | G |∘| F           => pfmap G ∘ pfmap F
  end.

#[refine] Instance polynomialFunctor F : Functor ⟦F⟧ :=
  { fmap := @pfmap F
  }.
Proof.
  all: now
    ( induction F
    ; intros; cbn [pfmap "∘"]
    ; try rewrite IHF2
    ; try rewrite IHF1
    ; try rewrite bifunctorsPreserveIdentities
    ; try rewrite bifunctorsPreserveComposition
    ).
Defined.

Definition strength `{Functor F} A B : A * F B -> F (A * B) :=
  uncurry (fmap F ∘ curry id).

Arguments strength _ {_} _ _.

Definition η `{LaxMonoidalFunctor F} A : A -> F A :=
  fmap F (ρ A) ∘ strength F A () ∘ bimap prod' (id, ε F) ∘ ρInverse A.

Arguments η _ {_} _.

Fixpoint traverse H `(LMFT : LaxMonoidalFunctor T) A
    : (⟦H⟧ ∘ T) A -> (T ∘ ⟦H⟧) A :=
  match H with
  | identityFunctor   => id
  | constantFunctor X => η T X
  | F1 |*| F2         =>
      μ T (⟦F1⟧ A) (⟦F2⟧ A)
      ∘ bimap prod' (traverse F1 _ A, traverse F2 _ A)
  | F1 |+| F2         =>
      (fmap T inl ||| fmap T inr)
      ∘ bimap sum' (traverse F1 _ A, traverse F2 _ A)
  | G |∘| F           => traverse G LMFT (⟦F⟧ A) ∘ fmap ⟦G⟧ (traverse F _ A)
  end.

Arguments traverse _ _ {_} _.

Lemma coproductLemma1
  : forall `(f : A -> X, g : B -> X, h : X -> X')
  , h ∘ (f ||| g) = h ∘ f ||| h ∘ g.
Proof.
  intros.
  apply (proj2 coproductUniversalProperty).
  split; rewrite compose_assoc.
  now rewrite <- (proj1 (proj1 coproductUniversalProperty eq_refl)).
  now rewrite <- (proj2 (proj1 coproductUniversalProperty eq_refl)).
Qed.

Lemma coproductLemma2
  : forall `(f : A -> A', f' : A' -> X, g : B -> B', g' : B' -> X)
  , (f' ||| g') ∘ bimap sum' (f, g) = f' ∘ f ||| g' ∘ g.
Proof.
  intros; cbn [bimap coproductBifunctor].
  rewrite coproductLemma1.
  now
    ( repeat rewrite <- compose_assoc
    ; rewrite <- (proj1 (proj1 coproductUniversalProperty eq_refl))
    ; rewrite <- (proj2 (proj1 coproductUniversalProperty eq_refl))
    ).
Qed.

Notation sup2' F := (fun '(A, B) => F A + F B).
Notation sub2' F := (fun '(A, B) => F (A + B)).

#[refine] Instance sup2Bifunctor' `{Functor F} : Bifunctor (sup2' F) :=
  { bimap _ _ _ _ '(f, g) := bimap sum' (fmap F f, fmap F g)
  }.
Proof.
  all: intros.

  rewrite' (uncurry sum)
    ( functorsPreserveIdentities F A
    , functorsPreserveIdentities F B
    ).
  apply (bifunctorsPreserveIdentities sum').

  now rewrite' (uncurry sum)
    ( functorsPreserveComposition F f f'
    , functorsPreserveComposition F g g'
    ).
Defined.

#[refine] Instance sub2Bifunctor' `{Functor F} : Bifunctor (sub2' F) :=
  { bimap _ _ _ _ '(f, g) := fmap F (bimap sum' (f, g))
  }.
Proof.
  all: intros.

  rewrite' F (bifunctorsPreserveIdentities sum' A B).
  apply functorsPreserveIdentities.

  now rewrite' F (bifunctorsPreserveComposition sum' f f' g g').
Defined.

Lemma sup2Definition'
  : forall `{Functor F} `(f : A -> A', g : B -> B')
  , bimap (sup2' F) (f, g) = bimap sum' (fmap F f, fmap F g).
Proof.
  reflexivity.
Qed.

Arguments sup2Definition' _ {_} {_ _} _ {_ _} _.

Lemma sub2Definition'
  : forall `{Functor F} `(f : A -> A', g : B -> B')
  , bimap (sub2' F) (f, g) = fmap F (bimap sum' (f, g)).
Proof.
  reflexivity.
Qed.

(* Isn't + just another monoid like ×??? Lims, Colims, F(Lim D), Lim(F ∘ D), preservation etc opposite category unzip^op, interchange monoids aguiar etc *)
Instance NT1 `{Functor F}
  : NaturalTransformation' (fun A B => fmap F (@inl A B) ||| fmap F (@inr A B)).
Proof.
  intro; intros; cbn [bimap sup2Bifunctor' sub2Bifunctor'].
Admitted.

Lemma coproductLemma3
  : forall `{Functor F} `(f : A -> X, g : B -> X)
  , fmap F f ||| fmap F g = fmap F (f ||| g) ∘ (fmap F inl ||| fmap F inr).
Proof.
  intros.
  rewrite coproductLemma1.
  now
    ( rewrite' F
      (proj1 (proj1 (coproductUniversalProperty (f := f) (g := g)) eq_refl))
    ; rewrite' F
      (proj2 (proj1 (coproductUniversalProperty (f := f) (g := g)) eq_refl))
    ).
Qed.

Instance traverseNaturalTransformation H `{LaxMonoidalFunctor T}
  : NaturalTransformation (traverse H T).
Proof.
  induction H
    ; try rename
      H into F1, H1 into F2
      , IHpolynomialFunctorExpression1 into IH1
      , IHpolynomialFunctorExpression2 into IH2
    ; intro; intros
    ; cbn - [bimap].

  reflexivity.

  now rewrite functorsPreserveIdentities.

  rewrite compose_assoc; rewrite' (uncurry prod) (IH1 _ _ f, IH2 _ _ f)
    ; cbn - [bimap] in H; rewrite H; clear H.
  rewrite <- sup2Definition; rewrite <- compose_assoc; now rewrite (NTμ T).

  rewrite compose_assoc; rewrite' (uncurry sum) (IH1 _ _ f, IH2 _ _ f)
    ; cbn - [bimap] in H; fold denotation; rewrite H; clear H.
  rewrite <- sup2Definition'; rewrite <- compose_assoc; now rewrite NT1.

  rewrite compose_assoc; rewrite' ⟦F1⟧ (IH2 A B f)
    ; cbn - [bimap] in H; rewrite H; clear H.
  specialize (IH1 (⟦F2⟧ A)); cbn - [bimap] in IH1
    ; rewrite <- compose_assoc; now rewrite IH1.
Defined.

#[refine] Instance idLaxMonoidalFunctor
    : LaxMonoidalFunctor ⟦identityFunctor⟧ :=
  { ε := id
  ; μ _ _ := id
  }.
Proof.
  all: easy.
Defined.

Theorem unitarity : forall F A, traverse F id A = id.
Proof.
  now
    ( induction F; intro; cbn [traverse]
    ; try rewrite IHF1
    ; try rewrite IHF2
    ; try rewrite bifunctorsPreserveIdentities
    ; try (symmetry; apply (proj2 coproductUniversalProperty))
    ; try rewrite functorsPreserveIdentities
    ).
Qed.

Theorem naturality''
  : forall H `{MonoidalNaturalTransformation (F := F) (G := G) θ} A
  , traverse H G A ∘ fmap ⟦H⟧ (θ A) = θ (⟦H⟧ A) ∘ traverse H F A.
Proof.
  induction H
    ; try rename
      H into F1, H0 into F2
      , IHpolynomialFunctorExpression1 into IH1
      , IHpolynomialFunctorExpression2 into IH2
    ; intros F LMFF G LMFG θ MNTθ A
    ; cbn ["∘" denotation fmap pfmap polynomialFunctor traverse] in *.

  reflexivity.

  admit.

  rewrite compose_assoc
    ; rewrite' (uncurry prod) (IH1 F _ G _ θ _ A, IH2 F _ G _ θ _ A).
  rewrite <- compose_assoc; now rewrite (compatibilityWithProduct θ).

  rewrite compose_assoc
    ; rewrite' (uncurry sum) (IH1 F _ G _ θ _ A, IH2 F _ G _ θ _ A)
    ; cbn - [bimap] in *; fold denotation; rewrite H; clear H.
  rewrite <- compose_assoc; rewrite coproductLemma2.
  repeat rewrite <- (NTθ θ).
  now rewrite <- coproductLemma1.

  rewrite compose_assoc; rewrite' ⟦F1⟧ (IH2 F _ G _ θ _ A)
    ; cbn [fmap polynomialFunctor "∘"] in H; rewrite H; clear H.
  rewrite <- compose_assoc; now rewrite (IH1 F _ G _ θ _ (⟦F2⟧ A)).
Admitted.

Theorem linearity
  : forall `{LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G} H A
  , traverse H (G ∘ F) A = fmap G (traverse H F A) ∘ traverse H G (F A).
Proof.
  induction H
    ; try rename
      H into F1, H0 into F2
      , IHpolynomialFunctorExpression1 into IH1
      , IHpolynomialFunctorExpression2 into IH2
    ; intro; cbn - [bimap] in *.

  (* "The horizontal composite of two vertical identities is itself a vertical identity." Remark: same thing as encountered in previous proof(s)! *)
  (* horizontal composition is a bifunctor between vertical categories *)
  now rewrite functorsPreserveIdentities.

  admit.

  rewrite' (uncurry prod) (IH1 A, IH2 A).
  rewrite <- sup2Definition
    ; change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; rewrite (NTμ G).
  rewrite sub2Definition
    ; rewrite <- compose_assoc
    ; now rewrite <- functorsPreserveComposition.

  rewrite' (uncurry sum) (IH1 A, IH2 A).
  rewrite <- compose_assoc; rewrite coproductLemma2.
  repeat rewrite <- functorsPreserveComposition.
  rewrite coproductLemma3.
  now rewrite <- coproductLemma2.

  rewrite IH1.
  rewrite' ⟦F1⟧ (IH2 A); cbn [fmap polynomialFunctor] in H; rewrite H; clear H.
  change (?k ∘ ?h ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f)
    ; assert (H := traverseNaturalTransformation F1 (traverse F2 F A))
    ; cbn - [bimap] in *
    ; rewrite H
    ; clear H.
  rewrite <- compose_assoc; now rewrite <- functorsPreserveComposition.
Admitted.



  (* Page 699 (751) of aguiar (lax functor between 2-categories) *)



(*

(* Canonical strength *)
Definition strength `{Functor F} A B : A * F B -> F (A * B) :=
  uncurry (fmap ∘ curry id).



Definition horizontallyCompose `{Functor F, Functor F', Functor G, Functor G'}
    (τ : forall A, G A -> G' A) (σ : forall A, F A -> F' A)
    : forall A, (G ∘ F) A -> (G' ∘ F') A :=
  fun A => τ (F' A) ∘ fmap (F := G) (σ A).
Infix "◇" := horizontallyCompose (at level 40).

Instance horizontalCompositeOfTwoNaturalTransformations
  `{NTτ : NaturalTransformation G G' τ, NTσ : NaturalTransformation F F' σ}
  : NaturalTransformation (τ ◇ σ).
Proof.
  intro; intros; unfold "◇"; simpl.
  rewrite compose_assoc
    ; rewrite <- functorsPreserveComposition
    ; rewrite NTσ
    ; rewrite functorsPreserveComposition
    ; rewrite <- compose_assoc.
  now rewrite NTτ.
Defined.

Notation id' F := (fun A => @id (F A)).

Instance identityNaturalTransformation `{Functor F}
  : NaturalTransformation (id' F).
Proof.
  easy.
Defined.

Instance MNT1 `{MonoidalNaturalTransformation F F' θ, Functor G}
  : MonoidalNaturalTransformation (id' G ◇ θ).
(* 
page 72 http://www.math.iitb.ac.in/~swapneel/aguiar.pdf
(composites of lax monoidal is lax monoidal with reference)
page 114 of http://www.math.iitb.ac.in/~swapneel/aguiar.pdf
M ∘ (F x F)
F ∘ M
*)

Class LaxMonoidalFunctor `(FF : Functor F) :=
  { ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; NTμ : NaturalTransformation' _ _ (@μ)
  ; associativity
    : forall A B C
    , fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α
  ; leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ
  ; rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ
  }.



Class MonoidalNaturalTransformation
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    (θ : forall A, F A -> G A) :=
  { NTθ :> NaturalTransformation _ _ θ
  ; compatibilityWithUnit : ε (F := G) = θ () ∘ ε (F := F)
  ; compatibilityWithProduct
    : forall A B
    , μ (F := G) _ _ ∘ bimap (θ A) (θ B) = θ (A * B) ∘ μ (F := F) _ _
  }.





Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.

Definition λ A : () * A -> A := snd.

Definition bang A : A -> () := fun _ => tt.
Notation "!" := bang.

Definition ρ A : A * () -> A := fst.
Definition ρInverse A : A -> A * () := id &&& !.








Class Bifunctor F :=
  { bimap : forall A A' B B', (A -> A') -> (B -> B') -> (F A B -> F A' B')
  ; bifunctorsPreserveIdentities : forall A B, bimap id id = @id (F A B)
  ; bifunctorsPreserveComposition
    : forall A A' A'' B B' B''
      (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
    , bimap (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g
  }.

Definition bang A : A -> () := fun _ => tt.
Notation "!" := bang.

Definition tuple A B X (f : X -> A) (g : X -> B) : X -> A * B :=
  fun x => (f x, g x).
Infix "&&&" := tuple (at level 50).

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
  now split;
    [ intros ->
    | intros [-> ->]; apply functional_extensionality; intros [a | b]
    ].
Qed.

Lemma coproductLemma1 : forall A B, @id (A + B) = inl ||| inr.
Proof.
  intros; now apply coproductUniversalProperty.
Qed.

Lemma coproductLemma2
  : forall A B X (f : A -> X) (g : B -> X)
  , f = (f ||| g) ∘ inl /\ g = (f ||| g) ∘ inr.
Proof.
  intros; now apply coproductUniversalProperty.
Qed.

Lemma coproductLemma3
  : forall A B X X' (f : A -> X) (g : B -> X) (h : X -> X')
  , h ∘ (f ||| g) = h ∘ f ||| h ∘ g.
Proof.
  intros; apply coproductUniversalProperty.
  now repeat rewrite compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2).
Qed.

Lemma coproductLemma4
  : forall A A' B B' X (f : A -> A') (g : B -> B') (f' : A' -> X) (g' : B' -> X)
  , (f' ||| g') ∘ (inl ∘ f ||| inr ∘ g) = f' ∘ f ||| g' ∘ g.
Proof.
  intros.
  rewrite coproductLemma3.
  now repeat rewrite <- compose_assoc
    ; rewrite <- (proj1 coproductLemma2)
    ; rewrite <- (proj2 coproductLemma2).
Qed.

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
    ; [now intros [a b] | intro; apply eta_expansion].
Qed.

Generalizable All Variables.

(* Canonical strength *)
Definition strength `{Functor F} A B : A * F B -> F (A * B) :=
  uncurry (fmap ∘ curry id).

Ltac functorsPreserveCommutativeDiagrams F :=
  repeat rewrite <- (functorsPreserveComposition (F := F)); f_equal.

Ltac unfoldFunctorComposition :=
  change ((fmap (F := ?G) ∘ fmap (F := ?F)) ?f)
    with (fmap (F := G) (fmap (F := F) f))
  ; change ((?G ∘ ?F) ?A) with (G (F A)).

#[refine] Instance compositeOfTwoFunctors
    `(Functor G, Functor F) : Functor (G ∘ F) :=
  { fmap _ _ := fmap (F := G) ∘ fmap (F := F)
  }.
Proof.
  all: intros; unfoldFunctorComposition.
  rewrite functorsPreserveIdentities
    ; apply functorsPreserveIdentities.
  functorsPreserveCommutativeDiagrams G; apply functorsPreserveComposition.
Defined.

Definition verticallyCompose {F G H : Type -> Type}
    (τ : forall A, G A -> H A) (σ : forall A, F A -> G A)
    : forall A, F A -> H A :=
  fun A => τ A ∘ σ A.
Infix "◆" := verticallyCompose (at level 40).

Definition horizontallyCompose
    {F1 F2 : Type -> Type} `{Functor G1, Functor G2}
    (τ : forall A, G1 A -> G2 A) (σ : forall A, F1 A -> F2 A)
    : forall A, (G1 ∘ F1) A -> (G2 ∘ F2) A :=
  fun A => τ (F2 A) ∘ fmap (F := G1) (σ A).
Infix "◇" := horizontallyCompose (at level 40).

Ltac splitCommutativeRectangle :=
  match goal with
  | [|- ?h ∘ ?g ∘ ?f = ?h' ∘ ?g' ∘ ?f'] =>
      let H1 := fresh in
      let H2 := fresh in
      enough (exists k, g ∘ f = k ∘ f' /\ h ∘ k = h' ∘ g')
      as [k [H1 H2]]
      by (
        rewrite compose_assoc; rewrite H1
        ; rewrite <- compose_assoc; now rewrite H2)
      ; eexists; split
  end.

Instance verticalCompositeOfTwoNaturalTransformations
  `(NTτ : @NaturalTransformation G FG H FH τ)
  `(NTσ : @NaturalTransformation F FF G FG σ)
  : NaturalTransformation (τ ◆ σ).
Proof.
  intro; intros; unfold "◆".
  rewrite <- compose_assoc; splitCommutativeRectangle.
  apply NTσ.
  apply NTτ.
Defined.

Instance horizontalCompositeOfTwoNaturalTransformations
  `(NTτ : NaturalTransformation G1 G2 τ, NTσ : NaturalTransformation F1 F2 σ)
  : NaturalTransformation (τ ◇ σ).
Proof.
  intro; intros; simpl fmap; unfoldFunctorComposition; unfold "◇".
  rewrite <- compose_assoc; splitCommutativeRectangle.
  functorsPreserveCommutativeDiagrams G1; apply NTσ.
  apply NTτ.
Defined.

Ltac bifunctorsPreserveCommutativeDiagrams F :=
  repeat rewrite <- (bifunctorsPreserveComposition (F := F)); f_equal.


(*
to-do:
- get rid of vertical and horizontal composition
- only define/add vertical composition of binatural transformations
- see coherence strength jaskelioff!! (define class applicative functor subclass of lax monoidal functor)
- read proof lemma 3.6 jaskelioff!!




- keep vertical composition
- proof _.

- μGF = pre ∘ postwhisker or whatever, but not horizontal composition.
- also: in coq, mixing functors and bifunctors not as elegant.
*)


(* do the proofs the easy way, let's not overcomplicate things *)
(* bifunctor type * type -> type *)



(*
https://inspirehep.net/files/1e02ad81af7a278f19b217e99715a973
mac lane
*)

(* 
2-category stuff, referred to by jaskelioff paper
https://link.springer.com/chapter/10.1007%2FBFb0063101 
*)

(* ignore stuff below, just do everything the 'easy' way *)


(*
2-functors
pseudofunctors
pseudomonoids
lax functors
*)

(*
https://arxiv.org/pdf/1809.00727.pdf
see pseudomonoid
see also page 14

https://www.brics.dk/NS/98/7/BRICS-NS-98-7.pdf
see pseudofunctor
*)
(**)




Instance compositeOfTwoNaturalTransformations'
  `(NTσ : @NaturalTransformation' F BFF G BFG σ)
  `(NTτ : @NaturalTransformation' G BFG H BFH τ)
  : @NaturalTransformation' F BFF H BFH (fun A B => τ A B ∘ σ A B).
◆
Definition horizontallyCompose.






#[refine] Instance compositeOfTwoFunctors1'
    `(BFF : Bifunctor F, FG : Functor G) : Bifunctor (fun A B => G (F A B)) :=
  { bimap _ _ _ _ f g := fmap (F := G) (bimap (F := F) f g)
  }.
Proof.
  all: intros.
  rewrite bifunctorsPreserveIdentities
    ; apply functorsPreserveIdentities.
  functorsPreserveCommutativeDiagrams G; apply bifunctorsPreserveComposition.
Defined.

#[refine] Instance compositeOfTwoFunctors2'
    `(FF : Functor F, BFG : Bifunctor G)
    : Bifunctor (fun A B => G (F A) (F B)) :=
  { bimap _ _ _ _ f g := bimap (F := G) (fmap (F := F) f) (fmap (F := F) g)
  }.
Proof.
  all: intros.
  repeat rewrite functorsPreserveIdentities
    ; apply bifunctorsPreserveIdentities.
  bifunctorsPreserveCommutativeDiagrams G; apply functorsPreserveComposition.
Defined.

#[refine] Instance productBifunctor : Bifunctor prod :=
  { bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.
Proof.
Admitted.

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
    ; intros; cbn [pfmap]; unfoldFunctorComposition
    ; try rewrite IHpolynomialFunctorExpression2
    ; try rewrite IHpolynomialFunctorExpression1
    ; try rewrite bifunctorsPreserveIdentities
    ; try rewrite bifunctorsPreserveComposition
    ; reflexivity.
Defined.

Instance compositeOfTwoNaturalTransformations
  `(NTσ : @NaturalTransformation F FF G FG σ)
  `(NTτ : @NaturalTransformation G FG H FH τ)
  : @NaturalTransformation F FF H FH (fun A => τ A ∘ σ A).
Proof.
  intro; intros.
  rewrite compose_assoc; rewrite NTσ.
  rewrite <- compose_assoc; rewrite NTτ.
  reflexivity.
Defined.

Instance prewhiskering
  `(NTτ : NaturalTransformation F G τ, FH : Functor H)
  : @NaturalTransformation (F ∘ H) _ (G ∘ H) _ (fun A => τ (H A)).
Proof.
  intro; intros.
  apply NTτ.
Defined.

Instance postwhiskering
  `(NTτ : NaturalTransformation F G τ, FH : Functor H)
  : @NaturalTransformation (H ∘ F) _ (H ∘ G) _ (fun A => fmap (F := H) (τ A)).
Proof.
  intro; intros; simpl fmap; unfoldFunctorComposition.
  functorsPreserveCommutativeDiagrams H.
  apply NTτ.
Defined.

Class NaturalTransformation'
    `(BFF : Bifunctor F, BFG : Bifunctor G) (τ' : forall A B, F A B -> G A B) :=
  naturality'
    : forall A A' B B' (f : A -> A') (g : B -> B')
    , τ' A' B' ∘ bimap (F := F) f g = bimap (F := G) f g ∘ τ' A B.

Instance compositeOfTwoNaturalTransformations'
  `(NTσ : @NaturalTransformation' F BFF G BFG σ)
  `(NTτ : @NaturalTransformation' G BFG H BFH τ)
  : @NaturalTransformation' F BFF H BFH (fun A B => τ A B ∘ σ A B).
Proof.
  intro; intros.
  rewrite compose_assoc; rewrite NTσ.
  rewrite <- compose_assoc; rewrite NTτ.
  reflexivity.
Defined.

Instance prewhiskering'
  `(NTτ : NaturalTransformation' F G τ, FH : Functor H)
  : @NaturalTransformation'
    (fun A B => F (H A) (H B)) _
    (fun A B => G (H A) (H B)) _
    (fun A B => τ (H A) (H B)).
Proof.
  intro; intros; apply NTτ.
Defined.

Instance postwhiskering'
  `(NTτ : NaturalTransformation' F G τ, FH : Functor H)
  : @NaturalTransformation'
    (fun A B => H (F A B)) _
    (fun A B => H (G A B)) _
    (fun A B => fmap (F := H) (τ A B)).
Proof.
  intro; intros; simpl bimap.
  functorsPreserveCommutativeDiagrams H.
  apply NTτ.
Defined.

Definition α A B C : A * (B * C) -> (A * B) * C :=
  (fst &&& fst ∘ snd) &&& snd ∘ snd.

Definition λ A : () * A -> A := snd.

Definition ρ A : A * () -> A := fst.
Definition ρInverse A : A -> A * () := id &&& !.

Class LaxMonoidalFunctor `(FF : Functor F) :=
  { ε : () -> F ()
  ; μ : forall A B, F A * F B -> F (A * B)
  ; NTμ : NaturalTransformation' _ _ (@μ)
  ; associativity
    : forall A B C
    , fmap (@α A B C) ∘ μ ∘ bimap id μ = μ ∘ bimap μ id ∘ α
  ; leftUnitality : forall A, fmap (@λ A) ∘ μ ∘ bimap ε id = λ
  ; rightUnitality : forall A, fmap (@ρ A) ∘ μ ∘ bimap id ε = ρ
  }.

(* Instead of defining whiskering, define horizontal composition and use hor comp with id *)
(* for horizontal composition, see mac lane page 272 *)
(* 275 mac lane matches 'whisker' *)

(* https://ncatlab.org/nlab/show/Godement+product *)
(* https://ncatlab.org/nlab/show/ETCC *)

#[refine] Instance compositeOfTwoLaxMonoidalFunctors
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    : LaxMonoidalFunctor (@compositeOfTwoFunctors F _ G _) :=
  { ε := fmap (F := G) (ε (F := F)) ∘ ε (F := G)
  ; μ A B := fmap (F := G) (μ (F := F) A B) ∘ μ (F := G) (F A) (F B)
  }.
Proof.
  apply compositeOfTwoNaturalTransformations';
    [ apply (prewhiskering' (@NTμ G _ _))
    | apply (postwhiskering' (@NTμ F _ _))
    ].

  admit.
  (* is μ itself horizontal composition of the 2 bifunctors? pre and postwhiskering? *)

  admit.

  admit.
Admitted.

Class MonoidalNaturalTransformation
    `(LMFF : LaxMonoidalFunctor F, LMFG : LaxMonoidalFunctor G)
    (θ : forall A, F A -> G A) :=
  { NTθ :> NaturalTransformation _ _ θ
  ; compatibilityWithUnit : ε (F := G) = θ () ∘ ε (F := F)
  ; compatibilityWithProduct
    : forall A B
    , μ (F := G) _ _ ∘ bimap (θ A) (θ B) = θ (A * B) ∘ μ (F := F) _ _
  }.




(**)









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
    ; rewrite functorsPreserveIdentities in H3.
  assert (H4 := NTμ (F := G) (μ (F := F) A B) (@id (F C)))
    ; cbn in H4
    ; rewrite functorsPreserveIdentities in H4.
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
    ; rewrite functorsPreserveIdentities in H3.
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
    ; rewrite functorsPreserveIdentities in H3.
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
    ; try rewrite bifunctorsPreserveIdentities
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
    ; try repeat rewrite bifunctorsPreserveIdentities
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
    ; try rewrite bifunctorsPreserveIdentities
    ; try rewrite functorsPreserveIdentities
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

  rewrite functorsPreserveIdentities; reflexivity.

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
wanneer wetten enzo bewezen, schrijf op (masterthesis). 
daarna kijken of poly functors (lax of strong) monoidal functors zijn
*)










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
    rewrite functorsPreserveIdentities.
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

Theorem productPreservesIdentities
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

Theorem coproductPreservesIdentities
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

Theorem polynomialFunctorsPreserveIdentities
  : forall H A, fmap (F := ⟦H⟧) (@id A) = id.
Proof.
  induction H.
  reflexivity.
  reflexivity.

  intro.
  unfold fmap; simpl; change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  apply productPreservesIdentities.

  intro.
  unfold fmap; simpl; change (polynomialFunctor ?F ?f) with (fmap (F := ⟦F⟧) f).
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  apply coproductPreservesIdentities.

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
  rewrite productPreservesIdentities.
  reflexivity.

  intro.
  simpl.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite coproductPreservesIdentities.
  rewrite compose_id_right.
  apply coproductLemma.

  intro.
  simpl.
  rewrite IHpolynomialFunctorExpression1
    ; rewrite IHpolynomialFunctorExpression2.
  rewrite polynomialFunctorsPreserveIdentities.
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
*)
