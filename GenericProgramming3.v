Require Import Program.
Set Implicit Arguments.

(* A subset of the endofunctors from Set to Set. *)
Inductive functor : Type := 
  | idSet : functor
  | Δ : Set -> functor
  | product : functor -> functor -> functor
  | coproduct : functor -> functor -> functor
  | composition : functor -> functor -> functor.

Infix "|*|" := product (at level 40).
Infix "|+|" := coproduct (at level 50).
Infix "|∘|" := composition (at level 40).
Reserved Notation "⟦ F ⟧".

Open Scope type_scope.

Fixpoint evaluate (H : functor) : Set -> Set := 
  match H with
  | idSet => id
  | Δ A   => const A
  | F |*| G => fun A : Set => ⟦F⟧ A * ⟦G⟧ A
  | F |+| G => fun A : Set => ⟦F⟧ A + ⟦G⟧ A
  | F |∘| G => ⟦F⟧ ∘ ⟦G⟧
  end
where "⟦ F ⟧" := (evaluate F).

Class Functor (F : Set -> Set) := 
  fmap : forall A B : Set, (A -> B) -> (F A -> F B).

Class Bifunctor (F : Set -> Set -> Set) := 
  bimap 
    : forall A A' B B' : Set
    , (A -> A') -> (B -> B') -> (F A B -> F A' B').

(* The universal property of product. *)
Definition pairing 
    (A B C : Set) (f : C -> A) (g : C -> B) 
    : C -> A * B := 
  fun c : C => (f c, g c).
Infix "&&&" := pairing (at level 80).

(* The universal property of coproduct. *)
Definition copairing (A B C : Set) (f : A -> C) (g : B -> C) 
    : A + B -> C := 
  fun cp : A + B => 
    match cp with
    | inl a => f a
    | inr b => g b
    end.
Infix "|||" := copairing (at level 85).

Instance productBifunctor : Bifunctor prod := 
  { bimap _ _ _ _ f g := f ∘ fst &&& g ∘ snd
  }.

Instance coproductBifunctor : Bifunctor sum :=
  { bimap _ _ _ _ f g := inl ∘ f ||| inr ∘ g
  }.

Instance evaluatedFunctor (H : functor) : Functor ⟦H⟧ := 
  { fmap := 
      let fix fmap' (H' : functor) (A B : Set) 
          : (A -> B) -> (⟦H'⟧ A -> ⟦H'⟧ B) :=
        match H' with
        | idSet   => id
        | Δ _     => const id
        | F |∘| G => fmap' _ _ _ ∘ fmap' _ _ _
        | _       => fun f => bimap (fmap' _ _ _ f) (fmap' _ _ _ f)
        end
      in fmap' H
  }.

Definition braiding (A B : Set) : A * B -> B * A := snd &&& fst.

Definition curry (A B C : Set) (f : A * B -> C) : A -> (B -> C) := 
  fun (a : A) (b : B) => f (a, b).

(* broadcast is actually an instance of zip (namely 'zip ( * B) F') if we allow/include partial applications of product *)
Definition broadcast (F : functor) (A B : Set) 
    : ⟦F⟧ A * B -> ⟦F⟧ (A * B) := 
  fun p : ⟦F⟧ A * B => fmap (curry (@braiding B A) (snd p)) (fst p).

Definition zip (F G : functor) (A : Set)
    : (⟦F⟧ ∘ ⟦G⟧) A -> (⟦G⟧ ∘ ⟦F⟧) A.
refine (match F with
 | idSet => id
 | Δ B => _
 | F1 |*| F2 => _
 | F1 |+| F2 => _
 | F1 |∘| F2 => _
 end).
unfold compose.
unfold evaluate at 1 4.
unfold const.
refine (match G with
 | idSet => id
 | Δ B => _
 | F1 |*| F2 => _
 | F1 |+| F2 => _
 | F1 |∘| F2 => _
 end).
Admitted.
