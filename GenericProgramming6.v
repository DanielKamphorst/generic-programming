Require Import FunctionalExtensionality Program.

Set Asymmetric Patterns.
Set Implicit Arguments.

(* A subset of the endofunctors from Set to Set. *)
Inductive functor : Type := 
  | idSet : functor
  | Δ : Set -> functor
  | product : functor -> functor -> functor
  | composition : functor -> functor -> functor.

Infix "|*|" := product (at level 40).
Infix "|∘|" := composition (at level 40).
Reserved Notation "⟦ F ⟧".

Open Scope type_scope.

Fixpoint evaluate (F : functor) : Set -> Set := 
  match F with
  | idSet     => id
  | Δ A       => const A
  | F1 |*| F2 => fun A => ⟦F1⟧ A * ⟦F2⟧ A
  | F1 |∘| F2 => ⟦F1⟧ ∘ ⟦F2⟧
  end
where "⟦ F ⟧" := (evaluate F).

(* The universal property of product. *)
Definition pair'
    (A B C : Set) (f : C -> A) (g : C -> B) 
    : C -> A * B := 
  fun c => (f c, g c).
Infix "&&&" := pair' (at level 80).

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
        | idSet     => id
        | Δ _       => const id
        | F1 |*| F2 => fun f => bimap (fmap' _ _ _ f) (fmap' _ _ _ f)
        | F1 |∘| F2 => fmap' _ _ _ ∘ fmap' _ _ _
        end
      in fmap' F
  }.

(* Proof can be found in algprog. Admitted for now. *)
Theorem productPreservesComposition 
  : forall (A A' A'' B B' B'' : Set) (f : A -> A') (f' : A' -> A'') (g : B -> B') (g' : B' -> B'')
  , bimap (f' ∘ f) (g' ∘ g) = bimap f' g' ∘ bimap f g.
Admitted.
  
Theorem evaluatedFunctorsPreserveComposition1 
    : forall F G : functor
    , (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G |∘| F⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  match goal with
  | |- ?x = ?y => change (fmap (F := ⟦G⟧) (fmap (F := ⟦F⟧) (g ∘ f)) = y)
  end.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Theorem evaluatedFunctorsPreserveComposition2 
    : forall F G : functor
    , (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall (A B C : Set) (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F |*| G⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  (*
  match goal with
  | |- context G [fmap ?h] => let P := context G [bimap (fmap h) (fmap h)] in change P
  end.
  *)
  unfold fmap; simpl; fold (fmap (F := ⟦F⟧)); fold (fmap (F := ⟦G⟧)).
  rewrite H1.
  rewrite H2.
  apply productPreservesComposition.
Qed.

Fixpoint zipWith (A B C : Set) (F : functor)
    : (A -> B -> C) -> ⟦F⟧ A -> ⟦F⟧ B -> ⟦F⟧ C :=
  match F return (A -> B -> C) -> (⟦F⟧ A -> ⟦F⟧ B -> ⟦F⟧ C) with
  | idSet     => id
  | Δ _       => const const
  | F1 |*| F2 => fun f '(as1, as2) '(bs1, bs2) => 
      (zipWith F1 f as1 bs1, zipWith F2 f as2 bs2)
  | F1 |∘| F2 => fun f => zipWith F1 (zipWith F2 f)
  end.

Notation curry := prod_uncurry.
Notation uncurry := prod_curry.

Definition zip (A B : Set) (F : functor) 
    : ⟦F⟧ A * ⟦F⟧ B -> ⟦F⟧ (A * B) := 
  uncurry (zipWith _ pair).

Definition unzip (A B : Set) (F : functor) 
    : ⟦F⟧ (A * B) -> ⟦F⟧ A * ⟦F⟧ B :=
  fmap fst &&& fmap snd.

Theorem someTheorem
  : forall (A B : Set) (F G : functor)
  , zip A B (G |∘| F) = fmap (zip A B F) ∘ zip _ _ G.
Admitted.

Theorem anotherTheorem
  : forall (A B : Set) (F G : functor)
  , unzip A B (G |∘| F) = unzip _ _ G ∘ fmap (unzip A B F).
Admitted.

(* old >>> *)
(* Prove for poly functors using induction (in the same way as someLemma) *)
Theorem functorsPreserveComposition 
  : forall `(F : Functor) (A B C : Set) (f : A -> B) (g : B -> C)
  , fmap (g ∘ f) = fmap g ∘ fmap f.
Admitted.

Theorem functorsPreserveIdentityMorphisms
  : forall `(F : Functor) (A : Set), fmap (@id A) = id.
Admitted.
(* <<< old *)

Lemma someLemma 
    : forall (F G : functor)
    , (forall A B : Set, zip A B F ∘ unzip A B F = id) 
    -> (forall A B : Set, zip A B G ∘ unzip A B G = id) 
    -> forall A B : Set, zip A B (G |∘| F) ∘ unzip A B (G |∘| F) = id.
  intros * H1 H2 *.
  rewrite someTheorem.
  rewrite anotherTheorem.
  match goal with
  | |- context G [?f1 ∘ ?f2 ∘ (?f3 ∘ ?f4)] => 
      let t := context G [f1 ∘ (f2 ∘ f3) ∘ f4]
      in change t
  end.
  rewrite H2.
  rewrite compose_id_right.
  rewrite <- functorsPreserveComposition.
  rewrite H1.
  rewrite functorsPreserveIdentityMorphisms.
  reflexivity.
Qed.
