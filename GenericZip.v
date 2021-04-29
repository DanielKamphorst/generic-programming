Require Import Arith List Program.

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

Theorem productUniversalProperty :
    forall A B C (f : C -> A) (g : C -> B) (l : C -> A * B)
    , l = f &&& g <-> fst ∘ l = f /\ snd ∘ l = g.
  split; 
    [ intros ->; auto 
    | intros [<- <-]; extensionality c; apply surjective_pairing
    ].
Qed.

Definition caseAnalyse A B C (f : A -> C) (g : B -> C) : A + B -> C := fun cp =>
  match cp with
  | inl a => f a
  | inr b => g b
  end.
Infix "|||" := caseAnalyse (at level 60).

Instance productBifunctor : Bifunctor prod :=
  fun _ _ _ _ f g => f ∘ fst &&& g ∘ snd.

Instance coproductBifunctor : Bifunctor sum :=
  fun _ _ _ _ f g => inl ∘ f ||| inr ∘ g.

Definition fibreProduct X Y Z (f : X -> Z) (g : Y -> Z) :=
  {(x, y) : X * Y | f x = g y}.

Arguments fibreProduct : clear implicits.

Definition fst' X Y Z (f : X -> Z) (g : Y -> Z) : fibreProduct X Y _ f g -> X :=
  fst ∘ @proj1_sig _ _.

Definition snd' X Y Z (f : X -> Z) (g : Y -> Z) : fibreProduct X Y _ f g -> Y :=
  snd ∘ @proj1_sig _ _.

Definition pair'' X Y Z
    (t : X -> Z) (u : Y -> Z)
    A (f : A -> X) (g : A -> Y) (H : t ∘ f = u ∘ g)
    : A -> fibreProduct X Y _ t u :=
  fun a => exist _ ((f &&& g) a) (equal_f H a).

Theorem pullbackUniversalProperty :
    forall X Y Z
      (t : X -> Z) (u : Y -> Z)
      A (f : A -> X) (g : A -> Y) (H : t ∘ f = u ∘ g)
      (h : A -> fibreProduct X Y Z t u)
    , f = fst' ∘ h /\ g = snd' ∘ h <-> h = pair'' H.
  split;
    [ intros [-> ->]
      ; extensionality a
      ; case_eq (h a); intros xy H1 H2
      ; apply subset_eq_compat
      ; unfold "_ &&& _", "_ ∘ _"
      ; rewrite H2
      ; apply surjective_pairing
    | intros ->; auto
    ].
Qed.

Definition prewhisker F G1 G2
    {F' : Functor F} {G1' : Functor G1} {G2' : Functor G2}
    (α : forall A, G1 A -> G2 A)
    : forall A, G1 (F A) -> G2 (F A) :=
  fun A => α (F A).

Definition postwhisker G1 G2 H
    {G1' : Functor G1} {G2' : Functor G2} {H' : Functor H}
    (α : forall A, G1 A -> G2 A)
    : forall A, H (G1 A) -> H (G2 A) :=
  fun A => fmap (α A).

Definition horizontallyCompose F1 F2 G1 G2
    {F1' : Functor F1} {F2' : Functor F2} {G1' : Functor G1} {G2' : Functor G2}
    (β : forall A, G1 A -> G2 A) (α : forall A, F1 A -> F2 A)
    : forall A, G1 (F1 A) -> G2 (F2 A) :=
  fun A => postwhisker α _ ∘ prewhisker β _.
Infix "◇" := horizontallyCompose (at level 40).

Definition shape F {F' : Functor F} A : F A -> F () := fmap (! A).
Arguments shape (F) {F'} (A).
Notation "#" := shape.

Instance listFunctor : Functor list := map.

Definition η A : A -> list A := flip cons nil.
Notation μ := (@concat _).

Fixpoint lengthInverse (n : nat) : list () :=
  match n with
  | O    => nil
  | S n' => tt :: lengthInverse n'
  end.

Theorem lengthIsInvertible
    : lengthInverse ∘ @length () = id /\ @length () ∘ lengthInverse = id.
  split
    ; extensionality x
    ; unfold "_ ∘ _"
    ; [induction x as [| [] l IH] | induction x as [| n IH]]
    ; try (cbn; rewrite IH)
    ; reflexivity.
Qed.

(* A list of type 'list ()' is uniquely determined by its length. *)
Theorem length_equal
    : forall l1 l2 : list (), l1 = l2 <-> length l1 = length l2.
  split; [apply f_equal |].
  intros H % (f_equal lengthInverse).
  change (lengthInverse (length ?l)) with ((lengthInverse ∘ @length _) l) in H
    ; rewrite (proj1 lengthIsInvertible) in H.
  assumption.
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
  | F |*| G         => uncurry prod ∘ (⟦F⟧ &&& ⟦G⟧)
  | F |+| G         => uncurry sum ∘ (⟦F⟧ &&& ⟦G⟧)
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

Fixpoint data F' A : ⟦F'⟧ A -> list A :=
  match F' with
  | identityFunctor => η
  | F |*| G         => uncurry (@app _) ∘ bimap (data F) (data G)
  | F |+| G         => data F ||| data G
  | G |∘| F         => μ ∘ (@data G ◇ @data F) A
  end.

Fixpoint partition' A (ns : list nat) (as' : list A) : list (list A) :=
  match ns with
  | n :: ns' => firstn n as' :: partition' ns' (skipn n as')
  | nil      => nil
  end.

Fixpoint partition'' A (toss : list (list ())) (as' : list A) : list (list A) :=
  match toss with
  | tos :: toss' =>
      let n := length tos
      in firstn n as' :: partition'' toss' (skipn n as')
  | nil          => nil
  end.

Definition productRightPullbackSquare A
    : fibreProduct (list () * list ()) (list A) (list ())
      (uncurry (@app _)) (# list A)
    -> list A * list A.
  refine (fun fp =>
    let ass := partition'
      (map (@length _) (uncurry (@app _) (bimap η η (fst' fp))))
      (snd' fp)
    in (
      match ass as ass' return ass = ass' -> list A * list A with
      | as1 :: as2 :: _ => fun _ => (as1, as2)
      | _               => _
      end) eq_refl); intros [=].
Defined.

Lemma ridOfDestructeringLet :
    forall X Y (xy : X * Y) (P : X -> Y -> Prop)
    , (let (x, y) := xy in P x y) -> P (fst xy) (snd xy).
  intros X Y [x y]; trivial.
Qed.

Definition productLeftPullbackSquare F G A
    : (fibreProduct (⟦F⟧ ()) (list A) (list ()) (data F) (# list A) -> ⟦F⟧ A)
    -> (fibreProduct (⟦G⟧ ()) (list A) (list ()) (data G) (# list A) -> ⟦G⟧ A)
    -> fibreProduct (⟦F⟧ () * ⟦G⟧ ()) (list A * list A) (list () * list ())
      (bimap (data F) (data G)) (bimap (# list A) (# list A))
    -> ⟦F⟧ A * ⟦G⟧ A.
  refine (fun f g fp =>
    let p := proj1 (pair_equal_spec _ _ _ _)
      (ridOfDestructeringLet _ _ (proj2_sig fp))
    in
      ( f (exist _ (fst (fst' fp), fst (snd' fp)) (proj1 p))
      , g (exist _ (snd (fst' fp), snd (snd' fp)) (proj2 p))
      )).
Defined.

Theorem partitionFunctionsEquality
    : forall A, @partition'' A = partition' ∘ map (@length _).
  intro; extensionality toss.
  induction toss as [| * IH]; [| cbn; rewrite IH]; reflexivity.
Qed.

Definition compositionRightPullbackSquare A
    : fibreProduct (list (list ())) (list A) (list ()) μ (# list A)
    -> list (list A) :=
  fun fp => partition' (map (@length _) (fst' fp)) (snd' fp).

(* list preserves pullbacks. *)
Fixpoint zipList' X Y Z (f : X -> Z) (g : Y -> Z) (xs : list X) (ys : list Y)
    : map f xs = map g ys -> list (fibreProduct X Y Z f g).
  refine (
    match xs, ys with
    | x :: xs', y :: ys' => fun H =>
        exist _ (x, y) _ :: zipList' _ _ _ _ _ xs' ys' _
    | x :: xs', nil      => _
    | nil     , y :: ys' => _
    | nil     , nil      => fun _ => nil
    end); try intros [=]; inversion H; reflexivity.
Defined.

(* https://coq.inria.fr/library/Coq.Program.Wf.html *)

Definition compositionMiddlePullbackSquare F A
    : (fibreProduct (⟦F⟧ ()) (list A) (list ()) (data F) (# list A) -> ⟦F⟧ A)
    -> fibreProduct (list (⟦F⟧ ())) (list (list A)) (list (list ()))
      (map (data F)) (map (# list A))
    -> list (⟦F⟧ A) :=
  fun f fp => map f
    (zipList' (fst' fp) (snd' fp) (ridOfDestructeringLet _ _ (proj2_sig fp))).

Definition compositionLeftPullbackSquare F G A
    : (fibreProduct (⟦F⟧ ()) (list A) (list ()) (data F) (# list A) -> ⟦F⟧ A)
    -> (fibreProduct (⟦G⟧ ()) (list (⟦F⟧ A)) (list ()) (data G) (# list (⟦F⟧ A)) -> ⟦G⟧ (⟦F⟧ A))
    -> fibreProduct (⟦G⟧ (⟦F⟧ ())) (list (⟦F⟧ A)) (list (⟦F⟧ ()))
      (data G) (map (# ⟦F⟧ A))
    -> ⟦G⟧ (⟦F⟧ A).
  refine (fun f g fp => g (exist _ (# ⟦G⟧ (⟦F⟧ ()) (fst' fp), snd' fp) _)).
  Check ridOfDestructeringLet _ _ (proj2_sig fp).
Admitted.

(* 'Plugs the data into the template'. *)
Fixpoint insertData F' A {struct F'}
    : fibreProduct (⟦F'⟧ ()) (list A) (list ()) (data F') (# list A) -> ⟦F'⟧ A.
Admitted.

(* Old
Definition unzip F' A B
    : data F' *' # (A * B)
    -> fst' (f := data F') (g := # A) *' fst' (f := data F') (g := # B).
  unfold fibreProduct.
  intros [[s abs] H].
  assert (H' := H).
  rewrite <- split_length_l' in H.
  rewrite <- split_length_r' in H'.
  refine (exist _ (exist _ (s, fst (split abs)) H, exist _ (s, snd (split abs)) H') _).
  reflexivity.
Defined.

Lemma split_combine' :
    forall A B (abs : list (A * B))
    , combine (fst (split abs)) (snd (split abs)) = abs.
  intros.
  assert (H := split_combine abs).
  destruct (split abs).
  assumption.
Qed.

Lemma combine_split' :
    forall A B (as' : list A) (bs : list B)
    , # _ as' = # _ bs -> split (combine as' bs) = (as', bs).
Admitted.

Lemma someLemma
    : forall A (P : A -> Prop) x y H1 H2, x = y -> exist P x H1 = exist P y H2.
  intros * ->.
  rewrite (proof_irrelevance (P y) H1 H2).
  reflexivity.
Qed.

Theorem unzipIsASectionOfZip : forall F A B, @zip F A B ∘ @unzip F A B = id.
  intros.
  extensionality fp.
  destruct fp as [[s abs] H].
  cbn.
  apply someLemma.
  rewrite split_combine'.
  reflexivity.
Qed.

Theorem unzipIsARetractionOfZip : forall F A B, @unzip F A B ∘ @zip F A B = id.
  intros.
  extensionality fp.
  destruct fp as [[[[s1 as'] H1] [[s2 bs] H2]] H].
  cbn in *.
  apply someLemma.
  apply pair_equal_spec; split; apply someLemma
    ; rewrite H in H1; rewrite H1 in H2
    ; rewrite (combine_split' H2).
  reflexivity.
  rewrite H; reflexivity.
Qed.
*)
