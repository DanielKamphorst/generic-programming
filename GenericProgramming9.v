Require Import CategoryTheoryLibrary Program.

Set Asymmetric Patterns.
Set Implicit Arguments.

Inductive polynomialFunctorExpression : Set :=
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

Fixpoint denotation (F : polynomialFunctorExpression) : Type -> Type :=
  match F with
  | identityFunctor => id
  | F' |*| G        => fun A => ⟦F'⟧ A * ⟦G⟧ A
  | F' |+| G        => fun A => ⟦F'⟧ A + ⟦G⟧ A
  | G  |∘| F'       => ⟦G⟧ ∘ ⟦F'⟧
  end
where "⟦ F ⟧" := (denotation F).

Instance polynomialFunctor (F : polynomialFunctorExpression) : Functor ⟦F⟧ := {
  fmap := (fix fmap' F' A B : (A -> B) -> (⟦F'⟧ A -> ⟦F'⟧ B) :=
    match F' with
    | identityFunctor => id
    | G   |∘| F''     => fmap' _ _ _ ∘ fmap' _ _ _
    | _               => fun f => bimap (fmap' _ _ _ f) (fmap' _ _ _ f)
    end) F
}.

Ltac unfoldSingleFmap :=
  match goal with
  | |- context G [fmap (F := ⟦?F⟧) ?f] =>
      let g :=
        match F with
        | identityFunctor => f
        | _ |*| _         => constr:(bimap (F := prod) (fmap f) (fmap f))
        | _ |+| _         => constr:(bimap (F := sum) (fmap f) (fmap f))
        | _ |∘| _         => constr:(fmap (fmap f))
        end
      in let t := context G [g] in change t
  end.

Lemma polynomialFunctorsPreserveIdentities1
    : forall F G
    , (forall A, fmap (F := ⟦F⟧) (@id A) = id)
    -> (forall A, fmap (F := ⟦G⟧) (@id A) = id)
    -> forall A, fmap (F := ⟦F |*| G⟧) (@id A) = id.
  intros * H1 H2 *.
  unfoldSingleFmap.
  rewrite H1; rewrite H2.
  apply productPreservesIdentities.
Qed.

Lemma polynomialFunctorsPreserveIdentities2
    : forall F G
    , (forall A, fmap (F := ⟦F⟧) (@id A) = id)
    -> (forall A, fmap (F := ⟦G⟧) (@id A) = id)
    -> forall A, fmap (F := ⟦F |+| G⟧) (@id A) = id.
  intros * H1 H2 *.
  unfoldSingleFmap.
  rewrite H1; rewrite H2.
  apply coproductPreservesIdentities.
Qed.

Lemma polynomialFunctorsPreserveIdentities3
    : forall F G
    , (forall A, fmap (F := ⟦F⟧) (@id A) = id)
    -> (forall A, fmap (F := ⟦G⟧) (@id A) = id)
    -> forall A, fmap (F := ⟦G |∘| F⟧) (@id A) = id.
  intros * H1 H2 *.
  unfoldSingleFmap.
  rewrite H1; apply H2.
Qed.

Theorem polynomialFunctorsPreserveIdentities
    : forall F A, fmap (F := ⟦F⟧) (@id A) = id.
  induction F.
  reflexivity.
  apply polynomialFunctorsPreserveIdentities1; assumption.
  apply polynomialFunctorsPreserveIdentities2; assumption.
  apply polynomialFunctorsPreserveIdentities3; assumption.
Qed.

Lemma polynomialFunctorsPreserveComposition1
    : forall F G
    , (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F |*| G⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  repeat unfoldSingleFmap.
  rewrite H1; rewrite H2.
  apply productPreservesComposition.
Qed.

Lemma polynomialFunctorsPreserveComposition2
    : forall F G
    , (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F |+| G⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  repeat unfoldSingleFmap.
  rewrite H1; rewrite H2.
  apply coproductPreservesComposition.
Qed.

Lemma polynomialFunctorsPreserveComposition3
    : forall F G
    , (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> (forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G⟧) (g ∘ f) = fmap g ∘ fmap f)
    -> forall A B C (f : A -> B) (g : B -> C)
      , fmap (F := ⟦G |∘| F⟧) (g ∘ f) = fmap g ∘ fmap f.
  intros * H1 H2 *.
  repeat unfoldSingleFmap.
  rewrite H1; apply H2.
Qed.

Theorem polynomialFunctorsPreserveComposition
    : forall F A B C (f : A -> B) (g : B -> C)
    , fmap (F := ⟦F⟧) (g ∘ f) = fmap g ∘ fmap f.
  induction F.
  reflexivity.
  apply polynomialFunctorsPreserveComposition1; assumption.
  apply polynomialFunctorsPreserveComposition2; assumption.
  apply polynomialFunctorsPreserveComposition3; assumption.
Qed.

Definition bang A : A -> () := fun _ : A => tt.
Notation "!" := bang.
Arguments "!" : clear implicits.




(* In a Boolean extensive category (like Set), a map A -> B + 1 is equivalent to a decomposition of A as a coproduct D + E together with a map D -> B (the map E -> 1 being unique), and in a Boolean category every subobject of A is complemented and hence induces such a coproduct decomposition. (D subobject of A and is complemented) *)


(* Every function with codomain B + 1 corresponds to a unique partial function to B *)

(* maybe first show that there exists such a decomposition. *)
(* Not A = D + E, but isomorphism/bijection. *)
Check forall A B D E (f : A -> B + ()) (g g' : D -> B), A = D + E -> (f = bimap (F := sum) g (! E) <-> f = bimap (F := sum) g' (! E)).

(* zip ∘ unzip = bimap f g -> f = id. *)





Definition join {A} (ooa : (option ∘ option) A) : option A :=
  match ooa with
  | Some oa => oa
  | None    => None
  end.

Definition compose' A B C (g : B -> option C) (f : A -> option B)
    : A -> option C :=
  join ∘ option_map g ∘ f.
Infix "∘'" := compose' (at level 40).

Reserved Notation "A *' B" (at level 40).

Inductive prod' A B : Type :=
  | inl' : A      -> A *' B
  | mid' : A -> B -> A *' B
  | inr' :      B -> A *' B
where "A *' B" := (prod' A B).

Arguments inl' {A B}.
Arguments mid' {A B}.
Arguments inr' {A B}.

Definition outl' {A B} (p : A *' B) : option A :=
  match p with
  | inl' a   => Some a
  | mid' a _ => Some a
  | _        => None
  end.

Definition outr' {A B} (p : A *' B) : option B :=
  match p with
  | inr'   b => Some b
  | mid' _ b => Some b
  | _        => None
  end.

Definition pair' A B C (f : C -> option A) (g : C -> option B) 
    : C -> option (A *' B) :=
  fun c =>
    match f c, g c with
    | Some a, None   => Some (inl' a)
    | Some a, Some b => Some (mid' a b)
    | None  , Some b => Some (inr' b)
    | None  , None   => None
    end.
Infix "&&&'" := pair' (at level 50).

Theorem someTheorem
    : forall A B C (f : C -> option A) (g : C -> option B)
    , outl' ∘' (f &&&' g) = f.
  intros.
  extensionality c.
  case_eq (f c)
    ; only 1 : intro a
    ; intro H; unfold "_ ∘' _", "_ ∘ _", "_ &&&' _"; rewrite H
    ; case (g c); auto.
Qed.



(* product laws *)




Notation pure := Some.

Definition join A (ooa : (option ∘ option) A) : option A :=
  match ooa with
  | Some oa => oa
  | None    => None
  end.

Definition bind A B (oa : option A) (f : A -> option B) : option B :=
  join (option_map f oa).
Infix ">>=" := bind (at level 80).

Definition pairOption A B : option A * option B -> option (A * B) :=
  fun '(oa, ob) =>
    oa >>= fun a =>
    ob >>= fun b =>
    pure (a, b).

Fixpoint sequence F A : ⟦F⟧ (option A) -> option (⟦F⟧ A) :=
  match F with
  | identityFunctor => id
  | F' |*| G        => @pairOption _ _ ∘ bimap (sequence F' _) (sequence G _)
  | F' |+| G        => 
      option_map inl ∘ sequence F' _ 
      ||| option_map inr ∘ sequence G _
  | G  |∘| F'       => sequence G _ ∘ fmap (sequence F' _)
  end.

Definition KleisliCompose A B C (g : B -> option C) (f : A -> option B)
    : A -> option C :=
  @join _ ∘ option_map g ∘ f.
Infix "<=<" := KleisliCompose (at level 40).

Definition outl A B (cp : A + B) : option A :=
  match cp with
  | inl a => Some a
  | _     => None
  end.

Definition outr A B (cp : A + B) : option B :=
  match cp with
  | inr b => Some b
  | _     => None
  end.

Definition pairOption' A B C (f : C -> option A) (g : C -> option B) 
    : C -> option (A * B) :=
  @pairOption _ _ ∘ (f &&& g).
Infix "&&&'" := pairOption' (at level 50).

Check bimap (@outl _ _) (@outl _ _).

Definition someFunction A B C D : (A + B) * (C + D) -> option (A * C + B * D) :=


  option_map inl ∘ @pairOption _ _ ∘ bimap (@outl _ _) (@outl _ _)
  option_map inr ∘ @pairOption _ _ ∘ bimap (@outr _ _) (@outr _ _).





  bimap (@outl _ _) (@outl _ _) &&&' bimap (@outr _ _) (@outr _ _).




  pairOption' (bimap (@outl _) outl) (bimap outr outr).



  bimap outl outl : (A + B) * (C + D) -> option (A * C)
  bimap outr outr : (A + B) * (C + D) -> option (B * D).

Fixpoint zip F A B : ⟦F⟧ A * ⟦F⟧ B -> option (⟦F⟧ (A * B)) :=
  match F return ⟦F⟧ A * ⟦F⟧ B -> option (⟦F⟧ (A * B)) with
  | identityFunctor => pure
  | F' |*| G        =>
      @pairOption _ _ 
      ∘ (zip F' _ _ ∘ bimap fst fst &&& zip G _ _ ∘ bimap snd snd)
  | F' |+| G        => fun p =>
      match p with
      | (inl fa, inl fb) => (option_map inl ∘ zip F' _ _) (fa, fb)
      | (inr ga, inr gb) => (option_map inr ∘ zip G _ _) (ga, gb)
      | _                => None
      end
  | G  |∘| F'       => (sequence G _ ∘ fmap (zip F' _ _)) <=< zip G _ _
  end.

Definition unzip F A B : ⟦F⟧ (A * B) -> ⟦F⟧ A * ⟦F⟧ B :=
  fmap fst &&& fmap snd.

Theorem productPreservesUnits 
    : forall A B
    , @pairOption A B ∘ bimap (F := prod) pure pure = pure.
  intros; extensionality p; destruct p; auto.
Qed.

Lemma zipIsTheInverseOfUnzip1
    : forall A B
    , zip identityFunctor A B ∘ unzip _ _ _ = pure.
  intros.
  simpl.
  unfold unzip.
  rewrite <- reflectionLawForProducts.
  apply compose_id_right.
Qed.

Lemma zipIsTheInverseOfUnzip2
    : forall F G
    , (forall A B, zip F A B ∘ unzip _ _ _ = pure)
    -> (forall A B, zip G A B ∘ unzip _ _ _ = pure)
    -> forall A B, zip (F |*| G) A B ∘ unzip _ _ _ = pure.
  intros * H1 H2 *.
  simpl; change (?f ∘ fst &&& ?g ∘ snd) with (bimap (F := prod) f g).
  rewrite compose_assoc; rewrite fusionLawForProducts.
  unfold unzip; repeat unfoldSingleFmap.
  repeat (rewrite compose_assoc; rewrite absorptionLawForProducts).
  unfold bimap, productBifunctor.
  simpl "⟦ _ ⟧".
  repeat rewrite cancellationLawForProducts1.
  repeat rewrite cancellationLawForProducts2.
  repeat rewrite <- fusionLawForProducts.
  repeat rewrite <- compose_assoc; rewrite H1; rewrite H2.
  apply productPreservesUnits.
Qed.

Theorem exchangeLaw 
    : forall A B C D (f : A -> C) (g : B -> C) (h : A -> D) (k : B -> D)
    , (f ||| g) &&& (h ||| k) = (f &&& h) ||| (g &&& k).
  idtac.
Admitted.

Lemma zipIsTheInverseOfUnzip3
    : forall F G
    , (forall A B, zip F A B ∘ unzip _ _ _ = pure)
    -> (forall A B, zip G A B ∘ unzip _ _ _ = pure)
    -> forall A B, zip (F |+| G) A B ∘ unzip _ _ _ = pure.
  intros * H1 H2 *.
  unfold unzip.
  repeat unfoldSingleFmap.
  unfold bimap, coproductBifunctor.
  simpl "⟦ _ ⟧".
  rewrite exchangeLaw.
  rewrite fusionLawForCoproducts.
  change (zip _ _ _ ∘ (inl ∘ _ &&& inl ∘ _)) 
    with ((option_map inl ∘ zip F _ _) (_, _)).


  unfold pairing.
  unfold compose.
  (option_map inl ∘ zip F' _ _) (fmap fst x, fmap snd x) 



  simpl zip.

  extensionality cp.


  change (?f ∘ fst &&& ?g ∘ snd) with (bimap (F := prod) f g).



  _ ∘ bimap inl inl.
  _ ∘ bimap inr inr.



  extensionality cp; destruct cp as [fab | gab].
  unfold unzip.
  repeat unfoldSingleFmap.
  unfold pairing.



Definition comparable A B C D (p : (A + B) * (C + D)) : Prop :=
  match p with
  | (inl _, inl _) => True
  | (inr _, inr _) => True
  | _              => False
  end.

(* comparable bimap (F := prod) inl inl. *)

Lemma someLemma : forall F G A B cp, comparable (unzip (F |+| G) A B cp).
  intros.
  unfold unzip.
  repeat unfoldSingleFmap.
  unfold bimap, coproductBifunctor.
  unfold "⟦ _ ⟧".
  rewrite exchangeLaw.
  unfold copairing.
  unfold comparable.
simpl in cp.



  unfold copairing.
  destruct cp; simpl; trivial.
Qed.



  unfold unzip.
  repeat unfoldSingleFmap.
  destruct cp as [fab | gab].
  simpl.
  trivial.
  simpl.
  trivial.




Lemma _ : unzip (F + G) (A * B) = inl x inl or inr x inr

Lemma zipIsTheInverseOfUnzip3
    : forall F G
    , (forall A B, zip F A B ∘ unzip _ _ _ = pure)
    -> (forall A B, zip G A B ∘ unzip _ _ _ = pure)
    -> forall A B, zip (F |+| G) A B ∘ unzip _ _ _ = pure.
  intros * H1 H2 *.
  extensionality cp; destruct cp as [fab | gab].
  unfold unzip.
  repeat unfoldSingleFmap.
  unfold pairing.



  simpl.


  simpl.



  unfold compose, unzip.
  repeat unfoldSingleFmap.


  simpl.


  unfold compose.
  simpl.


simpl in cp.
  unfold denotation in cp.


  unfold unzip.
  repeat unfoldSingleFmap.
  unfold bimap, coproductBifunctor.
  simpl.


  Set Printing All.
Admitted.






Lemma zipIsTheInverseOfUnzip3 
    : forall F G : functor
    , (forall A B : Set, zip F A B ∘ unzip _ _ _ = id)
    -> (forall A B : Set, zip G A B ∘ unzip _ _ _ = id)
    -> forall A B : Set, zip (G |∘| F) A B ∘ unzip _ _ _ = id.
  intros * H1 H2 *.
  simpl.
  rewrite unzipDecomposition.
  change ((?k ∘ ?h) ∘ (?g ∘ ?f)) with (k ∘ (h ∘ g) ∘ f).
  rewrite H2.
  rewrite compose_id_right.
  rewrite <- evaluatedFunctorsPreserveComposition.
  rewrite H1.
  apply evaluatedFunctorsPreserveIdentities.
Qed.





(* forall x y, (zip ∘ unzip) x            = Some y -> x = y *)
(* forall x y, ((pure ∘ unzip) <=< zip) x = Some y -> x = y *)





Lemma zipIsTheInverseOfUnzip1 
    : forall A B : Set
    , zip idSet A B ∘ unzip _ _ _ = id.
  intros.
  simpl.
  rewrite compose_id_left.
  unfold unzip.
  repeat unfoldSingleFmap.
  apply reflectionLaw.
Qed.







Inductive zippablePair A B : forall F, ⟦F⟧ A * ⟦F⟧ B -> Type :=
  | c1 : forall p, zippablePair A B identityFunctor p
  | c2 : forall F' G p
      , ((zippablePair _ _ F' ∘ bimap fst fst) p)
      -> ((zippablePair _ _ G ∘ bimap snd snd) p)
      -> zippablePair A B (F' |*| G) p
  | c3 : forall F' G p
      , zippablePair _ _ F' p
      -> zippablePair _ _ (F' |+| G) (bimap inl inl p)
  | c4 : forall F' G p
      , zippablePair _ _ G p
      -> zippablePair _ _ (F' |+| G) (bimap inr inr p)
  | c5 : zippablePair _ _ (G |∘| F') (_, _).





(* cataPFE *)
Fixpoint someFunction A a f g h F : A :=
  match F with
  | identityFunctor => a
  | F' |+| G        => f (someFunction _ a f g h F') (someFunction _ a f g h G)
  | F' |*| G        => g (someFunction _ a f g h F') (someFunction _ a f g h G)
  | G  |∘| F'       => h (someFunction _ a f g h G) (someFunction _ a f g h F')
  end.






Fixpoint zippable F A : ⟦F⟧ A * ⟦F⟧ B -> Prop :=
  match F with
  | identityFunctor => fun _ => True
  | F' |+| G        => _
  | F' |*| G        =>
      zippable F' _ ∘ bimap fst fst
      &&& zippable G _ ∘ bimap snd snd
  | G  |∘| F'       => _
  end.




  | id
Check fun _ : unit => identityFunctor.
Check uncurry product.
_ |||




Definition P F :=
  match F with
  | 



  match F with
  | F' |+| G => fun A B (p : ⟦F' |+| G⟧ A * ⟦F' |+| G⟧ B) => False
  | _        => True
  end.



Check fun F =>
  match F with
  | F' |+| G => fun A B (p : ⟦F⟧ A * ⟦F⟧ B) =>
      match p return with
      | (inl _, inr _) => False
      | (inr _, inl _) => False
      | _              => True
      end
  | _        => True
  end.

Check fun F A B => fun p : ⟦F⟧ A * ⟦F⟧ B =>
  match F with
  | F' |+| G =>
      match p with
      | (inl _, inr _) => False
      | (inr _, inl _) => False
      | _              => True
      end
  | _        => True
  end.


{p : ⟦F⟧ A * ⟦F⟧ B | P p}





Reserved Infix "*Par" (at level 40).

Inductive prodPar A B : Type :=
  | inlPar : A -> A *Par B
  | midPar : A -> B -> A *Par B
  | inrPar : B -> A *Par B
where "A *Par B" := (prodPar A B).

Definition outl A B (p : A *Par B) : option A :=
  match p with
  | inlPar a   => Some a
  | midPar a _ => Some a
  | inrPar _   => None
  end.

Definition outr A B (p : A *Par B) : option B :=
  match p with
  | inlPar _   => None
  | midPar _ b => Some b
  | inrPar b   => Some b
  end.

Definition pairingPar A B C (f : C -> option A) (g : C -> option B) (c : C)
    : option (A *Par B) :=
  match f c, g c with
  | Some a, Some b => Some (midPar a b)
  | Some a, None   => Some (inlPar _ a)
  | None  , Some b => Some (inrPar _ b)
  | None  , None   => None
  end.
Infix "&&&Par" := pairingPar (at level 50).

Definition pure A : A -> option A := Some.
Definition mu A (ooa : (option ∘ option) A) : option A :=
  match ooa with
  | Some oa => oa
  | None    => None
  end.

Definition composePar A B C (g : B -> option C) (f : A -> option B)
    : A -> option C :=
  @mu C ∘ option_map g ∘ f.
Infix "∘Par" := composePar (at level 40).

F A * G A = (F * G) A
F A *Par G A = (F *Par G) A???

Fixpoint zip F A B : ⟦F⟧ A * ⟦F⟧ B -> option (⟦F⟧ (A *Par B)) :=
  match F return ⟦F⟧ A * ⟦F⟧ B -> option (⟦F⟧ (A * B)) with
  | identityFunctor => Some ∘ id
  | F' |*| G        => Some ∘ (zip F' _ _ ∘ bimap fst fst &&& zip G _ _ ∘ bimap snd snd)
  | _               => fun _ => None
  end.
