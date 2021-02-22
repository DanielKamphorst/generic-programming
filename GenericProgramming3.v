Require Import List Program.
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
  | idSet   => id
  | Δ A     => const A
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
Definition pair 
    (A B C : Set) (f : C -> A) (g : C -> B) 
    : C -> A * B := 
  fun c : C => (f c, g c).
Infix "&&&" := pair (at level 80).

(* The universal property of coproduct. *)
Definition copair (A B C : Set) (f : A -> C) (g : B -> C) 
    : A + B -> C := 
  fun cp : A + B => 
    match cp with
    | inl a => f a
    | inr b => g b
    end.
Infix "|||" := copair (at level 85).

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

Definition swap {A B : Set} : A * B -> B * A := snd &&& fst.

Definition curry (A B C : Set) (f : A * B -> C) : A -> (B -> C) := 
  fun (a : A) (b : B) => f (a, b).

(* broadcast is actually an instance of zip (namely 'zip ( * B) F') if we allow/include partial applications of product *)
Definition broadcast {F : functor} {A B : Set} 
    : ⟦F⟧ A * B -> ⟦F⟧ (A * B) := 
  fun p : ⟦F⟧ A * B => fmap (curry swap (snd p)) (fst p).

Definition zip1 {F G : functor} {A B : Set} : ⟦F⟧ A * ⟦G⟧ B -> (⟦G⟧ ∘ ⟦F⟧) (A * B) :=
  fmap (broadcast ∘ swap) ∘ broadcast ∘ swap.

Definition zip2 {F G : functor} {A B : Set} : ⟦F⟧ A * ⟦G⟧ B -> (⟦F⟧ ∘ ⟦G⟧) (A * B) :=
  fmap (fmap swap ∘ broadcast ∘ swap) ∘ broadcast.

Definition zip12 {F G : functor} {A B : Set} 
    : ⟦F⟧ A * ⟦G⟧ B 
    -> (⟦G⟧ ∘ ⟦F⟧) (A * B) * (⟦F⟧ ∘ ⟦G⟧) (A * B) :=
  zip1 &&& zip2.

Definition unzip {F G : functor} {A B : Set}
    : ⟦F⟧ (A * B) -> ⟦F⟧ A * ⟦F⟧ B :=
  fmap fst &&& fmap snd.

(* Note that broadcast, zip1, zip2, zip12 and unzip actually do not depend on F and G being polynomial functors (these functions are defined on all endofunctors on Set). *)

Definition uncurry (A B C : Set) (f : A -> B -> C) : A * B -> C := fun '(a, b) => f a b.

(* Natural transformation from ⟦F⟧ to P (well, actually, list). P is a terminal object in the category of polynomial functors. *)
(* Isn't this basically the power transpose of the membership relation on polynomial functors? *)
(* Important: "++" (app) corresponds to disjoint union rather than union when using lists. *)
Fixpoint listify (A : Set) (F : functor) : ⟦F⟧ A -> list A :=
  match F with
  | idSet     => flip cons nil
  | Δ B       => const nil
  | F1 |*| F2 => uncurry (@app _) ∘ bimap (listify _ _) (listify _ _)
  | F1 |+| F2 => listify _ _ ||| listify _ _
  | F1 |∘| F2 => @concat _ ∘ listify _ _ ∘ fmap (listify _ _)
  end.

(* Without any (pre)conditions, we can't define a function of type (⟦F⟧ ∘ ⟦F⟧) A -> ⟦F⟧ A. However, we can define a function of type PPA -> PA. *)
Definition zip3 {F : functor} {A B : Set} : ⟦F⟧ A * ⟦F⟧ B -> list (A * B) :=
  listify _ (F |∘| F) ∘ zip1.

Definition mu {F : functor} {A : Set} : (⟦F⟧ ∘ ⟦F⟧) A -> ⟦F⟧ A.
induction F.
exact id.
exact id.
unfold compose.
simpl.
exact (IHF1 ∘ fmap (@fst (⟦F1⟧ A) (⟦F2⟧ A)) ∘ fst &&& IHF2 ∘ fmap (@snd (⟦F1⟧ A) (⟦F2⟧ A)) ∘ snd).
unfold compose.
simpl.
apply copair.
admit.
admit.
unfold compose.
simpl.
admit.
Admitted.

Definition zip' (F G : functor) (A : Set)
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
