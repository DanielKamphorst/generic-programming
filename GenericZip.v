Require Import List Program.

Arguments "∘" {_ _ _} _ _ _ /.

Open Scope type_scope.

Definition α {X A B} : (X -> A) * (X -> B) -> (X -> A * B) :=
  fun τ x => (fst τ x, snd τ x).

Definition αInv {X A B} : (X -> A * B) -> (X -> A) * (X -> B) :=
  fun t => (fst ∘ t, snd ∘ t).

Definition ε A B : (A * B -> A) * (A * B -> B) := αInv id.

Notation "f *' g" := (α (f ∘ fst, g ∘ snd)) (at level 30).

Definition β {A B X} : (A + B -> X) -> (A -> X) * (B -> X) :=
  fun t => (t ∘ inl, t ∘ inr).

Definition βInv {A B X} : (A -> X) * (B -> X) -> (A + B -> X) := fun τ m =>
  match m with
  | inl a => fst τ a
  | inr b => snd τ b
  end.

Notation "f +' g" := (βInv (inl ∘ f, inr ∘ g)) (at level 35).

Definition pullback {A B C} (f : A -> C) (g : B -> C) :=
  {x : A * B | f (fst x) = g (snd x)}.

Definition fst' {A B C} {f : A -> C} {g : B -> C} : pullback f g -> A :=
  fst ∘ @proj1_sig _ _.

Definition snd' {A B C} {f : A -> C} {g : B -> C} : pullback f g -> B :=
  snd ∘ @proj1_sig _ _.

Definition Hom {A A' B B'}
    : (A' -> A) * (B -> B') -> ((A -> B) -> (A' -> B')) :=
  fun '(f, h) g => h ∘ g ∘ f.

Definition ε' {A B C} (f : A -> C) (g : B -> C)
    : pullback (Hom (@id (pullback f g), f)) (Hom (@id (pullback f g), g)).
  refine (exist _ (fst', snd') _).
  apply functional_extensionality, proj2_sig.
Defined.

Definition γ {X A B C} {f : A -> C} {g : B -> C}
    : pullback (Hom (@id X, f)) (Hom (@id X, g)) -> (X -> pullback f g).
  refine (fun τ x => exist _ (fst' τ x, snd' τ x) _).
  apply (equal_f (proj2_sig τ)).
Defined.

Definition γInv {X A B C} {f : A -> C} {g : B -> C}
    : (X -> pullback f g) -> pullback (Hom (@id X, f)) (Hom (@id X, g)).
  refine (fun t => exist _ (fst' ∘ t, snd' ∘ t) _).
  exact (f_equal (Hom (t, id)) (proj2_sig (ε' f g))).
Defined.

Definition η' X : X -> pullback (@id X) (@id X).
  now refine (γ (exist _ (id, id) _)).
Defined.

Definition η'Inv X : pullback (@id X) (@id X) -> X := fst' (ε' id id).

Definition κProduct {A1 A2 B1 B2 C1 C2}
    {f1 : A1 -> C1} {f2 : A2 -> C2}
    {g1 : B1 -> C1} {g2 : B2 -> C2}
    : pullback f1 g1 * pullback f2 g2
    -> pullback (f1 *' f2) (g1 *' g2).
  refine (γ (exist _
    ( fst' (ε' f1 g1) *' fst' (ε' f2 g2)
    , snd' (ε' f1 g1) *' snd' (ε' f2 g2)
    ) _)).
  admit.
Admitted.

Definition κProductInv {A1 A2 B1 B2 C1 C2}
    {f1 : A1 -> C1} {f2 : A2 -> C2}
    {g1 : B1 -> C1} {g2 : B2 -> C2}
    : pullback (f1 *' f2) (g1 *' g2)
    -> pullback f1 g1 * pullback f2 g2.
  refine (α
    ( γ (exist _
      ( fst (ε A1 A2) ∘ fst' (ε' (f1 *' f2) (g1 *' g2))
      , fst (ε B1 B2) ∘ snd' (ε' (f1 *' f2) (g1 *' g2))
      ) _)
    , γ (exist _
      ( snd (ε A1 A2) ∘ fst' (ε' (f1 *' f2) (g1 *' g2))
      , snd (ε B1 B2) ∘ snd' (ε' (f1 *' f2) (g1 *' g2))
      ) _)
    )).
  admit.
Admitted.

Definition κCoproduct {A1 A2 B1 B2 C1 C2}
    {f1 : A1 -> C1} {f2 : A2 -> C2}
    {g1 : B1 -> C1} {g2 : B2 -> C2}
    : pullback f1 g1 + pullback f2 g2
    -> pullback (f1 +' f2) (g1 +' g2).
  refine (γ (exist _
    ( fst' (ε' f1 g1) +' fst' (ε' f2 g2)
    , snd' (ε' f1 g1) +' snd' (ε' f2 g2)
    ) _)).
  admit.
Admitted.

Definition κCoproductInv {A1 A2 B1 B2 C1 C2}
    {f1 : A1 -> C1} {f2 : A2 -> C2}
    {g1 : B1 -> C1} {g2 : B2 -> C2}
    : pullback (f1 +' f2) (g1 +' g2)
    -> pullback f1 g1 + pullback f2 g2.
  intros [[[a1 | a2] [b1 | b2]] [= H]].
  exact (inl (exist _ (a1, b1) H)).
  exact (inr (exist _ (a2, b2) H)).
Defined.

Inductive Poly (T : Type -> Type) : Type :=
  | identityFunctor : Poly T
  | constantFunctor : Type -> Poly T
  | typeConstructor : Poly T
  | product : Poly T -> Poly T -> Poly T
  | coproduct : Poly T -> Poly T -> Poly T
  | composite : Poly T -> Poly T -> Poly T.

Arguments identityFunctor {T}.
Arguments constantFunctor {T}.
Arguments product {T}.
Arguments coproduct {T}.
Arguments composite {T}.

Infix "|*|" := product (at level 30).
Infix "|+|" := coproduct (at level 35).
Infix "|∘|" := composite (at level 40).

Reserved Notation "⟦ P ⟧".

Fixpoint denotation {T} (P'' : Poly T) : Type -> Type :=
  match P'' with
  | identityFunctor   => id
  | constantFunctor A => const A
  | typeConstructor _ => T
  | P1 |*| P2         => fun X => ⟦P1⟧ X * ⟦P2⟧ X
  | P1 |+| P2         => fun X => ⟦P1⟧ X + ⟦P2⟧ X
  | P' |∘| P          => ⟦P'⟧ ∘ ⟦P⟧
  end
where "⟦ P ⟧" := (denotation P).

Fixpoint arrowFunc' {T} (T' : forall X Y, (X -> Y) -> (T X -> T Y))
    (P'' : Poly T) {X Y}
    : (X -> Y) -> (⟦P''⟧ X -> ⟦P''⟧ Y) := fun f =>
  match P'' with
  | identityFunctor   => f
  | constantFunctor A => @id A
  | typeConstructor _ => T' _ _ f
  | P1 |*| P2         => arrowFunc' T' P1 f *' arrowFunc' T' P2 f
  | P1 |+| P2         => arrowFunc' T' P1 f +' arrowFunc' T' P2 f
  | P' |∘| P          => arrowFunc' T' P' (arrowFunc' T' P f)
  end.

Unset Guard Checking.

Fixpoint arrowFunc T {P : Poly T}
    (θ : forall X, ⟦P⟧ X -> T X)
    (θInv : forall X, T X -> ⟦P⟧ X)
    {X Y} {struct T}
    : (X -> Y) -> (T X -> T Y) :=
  fun f => θ Y ∘ arrowFunc' (@arrowFunc T P θ θInv) P f ∘ θInv X.

Set Guard Checking.

Axiom arrowFuncDefinition
  : forall T P θ θInv X Y f
  , arrowFunc T θ θInv f
    = θ Y ∘ arrowFunc' (@arrowFunc T P θ θInv) P f ∘ θInv X.

Fixpoint κ' {T}
    (T' : forall X Y, (X -> Y) -> (T X -> T Y))
    (κT
      : forall A B C (f : A -> C) (g : B -> C)
      , T (pullback f g) -> pullback (T' _ _ f) (T' _ _ g))
    (P'' : Poly T) {A B C} {f : A -> C} {g : B -> C}
    : ⟦P''⟧ (pullback f g)
    -> pullback (arrowFunc' T' P'' f) (arrowFunc' T' P'' g) :=
  match P'' with
  | identityFunctor   => id
  | constantFunctor A => η' A
  | typeConstructor _ => κT _ _ _ f g
  | P1 |*| P2         => κProduct ∘ (κ' T' κT P1 *' κ' T' κT P2)
  | P1 |+| P2         => κCoproduct ∘ (κ' T' κT P1 +' κ' T' κT P2)
  | P' |∘| P          => κ' T' κT P' ∘ arrowFunc' T' P' (κ' T' κT P)
  end.

Unset Guard Checking.

Fixpoint κ T {P : Poly T}
    (θ : forall X, ⟦P⟧ X -> T X)
    (θInv : forall X, T X -> ⟦P⟧ X)
    {A B C} {f : A -> C} {g : B -> C} {struct P}
    : T (pullback f g)
    -> pullback (arrowFunc T θ θInv f) (arrowFunc T θ θInv g).
  refine (
    γ (exist _ (θ A ∘ fst', θ B ∘ snd') _)
    ∘ κ' (@arrowFunc T P θ θInv) (κ T P θ θInv) P
    ∘ θInv (pullback f g)
  ).
  repeat rewrite arrowFuncDefinition.
  simpl.
  repeat rewrite compose_id_right.
  change (?m ∘ ?k ∘ ?h ∘ (?g ∘ ?f)) with (m ∘ k ∘ (h ∘ g) ∘ f).
  change_no_check (θInv ?A ∘ θ ?A) with (@id (⟦P⟧ A)).
  repeat rewrite compose_id_right.
  exact (f_equal (Hom (id, θ C)) (proj2_sig (ε' (arrowFunc' (@arrowFunc T P θ θInv) P f) (arrowFunc' (@arrowFunc T P θ θInv) P g)))).
Admitted.

Set Guard Checking.

Fixpoint κ'Inv {T}
    (T' : forall X Y, (X -> Y) -> (T X -> T Y))
    (κTInv
      : forall A B C (f : A -> C) (g : B -> C)
      , pullback (T' _ _ f) (T' _ _ g) -> T (pullback f g))
    (P'' : Poly T) {A B C} {f : A -> C} {g : B -> C}
    : pullback (arrowFunc' T' P'' f) (arrowFunc' T' P'' g)
    -> ⟦P''⟧ (pullback f g) :=
  match P'' with
  | identityFunctor   => id
  | constantFunctor A => η'Inv A
  | typeConstructor _ => κTInv _ _ _ f g
  | P1 |*| P2         => (κ'Inv T' κTInv P1 *' κ'Inv T' κTInv P2) ∘ κProductInv
  | P1 |+| P2         =>
      (κ'Inv T' κTInv P1 +' κ'Inv T' κTInv P2)
      ∘ κCoproductInv 
  | P' |∘| P          => arrowFunc' T' P' (κ'Inv T' κTInv P) ∘ κ'Inv T' κTInv P'
  end.

Unset Guard Checking.

Fixpoint κInv T {P : Poly T}
    (θ : forall X, ⟦P⟧ X -> T X)
    (θInv : forall X, T X -> ⟦P⟧ X)
    {A B C} {f : A -> C} {g : B -> C} {struct P}
    : pullback (arrowFunc T θ θInv f) (arrowFunc T θ θInv g)
    -> T (pullback f g).
  refine (
    θ (pullback f g)
    ∘ κ'Inv (@arrowFunc T P θ θInv) (κInv T P θ θInv) P
    ∘ γ (exist _ (θInv A ∘ fst', θInv B ∘ snd') _)
  ).
  admit.
Admitted.

Set Guard Checking.

Definition curry {A B C} : (A * B -> C) -> (A -> (B -> C)) :=
  fun f a b => f (a, b).

Definition uncurry {A B C} : (A -> (B -> C)) -> (A * B -> C) :=
  fun f '(a, b) => f a b.

Definition θ X
    : ⟦constantFunctor () |+| (identityFunctor |*| typeConstructor list)⟧ X
    -> list X :=
  βInv (const nil, uncurry cons).

Definition θInv X
    : list X
    -> ⟦constantFunctor () |+| (identityFunctor |*| typeConstructor list)⟧ X :=
  fun xs =>
    match xs with
    | nil        => inl tt
    | cons x xs' => inr (x, xs')
    end.

Check κ list θ θInv.
Check κInv list θ θInv.

Theorem t : @arrowFunc list _ θ θInv = map.
Proof.
  extensionality X; extensionality Y; extensionality f; extensionality xs.
  induction xs; rewrite arrowFuncDefinition; [| simpl; rewrite IHxs]; auto.
Qed.
