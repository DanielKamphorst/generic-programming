Require Import List Program.

Set Asymmetric Patterns.
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

(* The universal property of product. *)
Definition pair 
    (A B C : Type) (f : C -> A) (g : C -> B) 
    : C -> A * B := 
  fun c : C => (f c, g c).
Infix "&&&" := pair (at level 80).

(* The universal property of coproduct. *)
Definition copair (A B C : Type) (f : A -> C) (g : B -> C) 
    : A + B -> C := 
  fun cp : A + B => 
    match cp with
    | inl a => f a
    | inr b => g b
    end.
Infix "|||" := copair (at level 85).

Class Functor (F : Set -> Set) := 
  fmap : forall A B : Set, (A -> B) -> (F A -> F B).

Class Bifunctor (F : Set -> Set -> Set) := 
  bimap 
    : forall A A' B B' : Set
    , (A -> A') -> (B -> B') -> (F A B -> F A' B').

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

Definition curry (A B C : Set) (f : A * B -> C) : A -> (B -> C) := 
  fun (a : A) (b : B) => f (a, b).

Definition uncurry (A B C : Set) (f : A -> B -> C) : A * B -> C := fun '(a, b) => f a b.

Definition swap {A B : Set} : A * B -> B * A := snd &&& fst.

Fixpoint memberOf (A : Set) (F : functor) (a : A) : ⟦F⟧ A -> Prop :=
  match F with
  | idSet     => eq a
  | Δ B       => const False
  | F1 |*| F2 => fun p => 
      (memberOf F1 a ∘ fst) p 
      \/ (memberOf F2 a ∘ snd) p
  | F1 |+| F2 => memberOf F1 a ||| memberOf F2 a
  | F1 |∘| F2 => fun ass => 
      exists as' : ⟦F2⟧ A, memberOf F1 as' ass /\ memberOf F2 a as'
  end.

Theorem membershipExampleTheorem : memberOf ((Δ () |*| idSet) |+| (idSet |*| Δ bool)) 3 (inr (3, false)).
Proof.
  simpl; auto.
Qed.

Fixpoint identicallyShaped (F : functor) (A B : Set) {struct F} : ⟦F⟧ A -> ⟦F⟧ B -> Prop.
  refine (
    match F with
    | idSet     => fun _ _ => True
    | Δ C       => eq
    | F1 |*| F2 => fun p1 p2 => 
        identicallyShaped _ _ _ (fst p1) (fst p2) 
        /\ identicallyShaped _ _ _ (snd p1) (snd p2)
    | F1 |+| F2 => fun cp1 cp2 => 
        match cp1, cp2 with
        | inl as', inl bs => identicallyShaped _ _ _ as' bs
        | inr as', inr bs => identicallyShaped _ _ _ as' bs
        | _, _            => False
        end
    | F1 |∘| F2 => fun ass bss => 
        identicallyShaped _ (⟦F2⟧ A) (⟦F2⟧ B) ass bss 
        /\ forall as' : ⟦F2⟧ A, memberOf _ as' ass 
          -> forall bs : ⟦F2⟧ B, memberOf _ bs bss 
            -> identicallyShaped _ _ _ as' bs
    end).
Defined.

(* broadcast is actually an instance of zip (namely 'zip ( * B) F') if we allow/include partial applications of product *)
Definition broadcast {F : functor} {A B : Set} 
    : ⟦F⟧ A * B -> ⟦F⟧ (A * B) := 
  fun p : ⟦F⟧ A * B => fmap (curry swap (snd p)) (fst p).

Fixpoint zip'' (F : functor) (A B : Set) {struct F} 
    : forall (p : ⟦F⟧ A * ⟦F⟧ B)
    , identicallyShaped _ _ _ (fst p) (snd p) 
    -> ⟦F⟧ (A * B).
  refine (
    match F with
    | idSet     => fun p _ => p
    | Δ C       => fun p _ => fst p
    | F1 |*| F2 => fun p H => _
    | F1 |+| F2 => fun p H => _
    | F1 |∘| F2 => fun p H => _
    end).
  simpl in p.
  simpl.
  generalize p.
  apply pair.
  intros _.
  exact (zip'' F1 A B (fst (fst p), fst (snd p)) (proj1 H)).
  intros _.
  exact (zip'' F2 A B (snd (fst p), snd (snd p)) (proj2 H)).
  simpl.
  destruct (fst p); destruct (snd p).
  refine (inl _).
  simpl in H.
  exact (zip'' F1 A B (e, e0) H).
  simpl in H; elim H.
  simpl in H; elim H.
  refine (inr _).
  simpl in H.
  exact (zip'' F2 A B (e, e0) H).
  (* difference with Tex: he defined 'zipWith', which makes comp case easy *)
  (* Maybe F-related, see container types categorically, or papers that Wouter sent *)
Admitted.

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
