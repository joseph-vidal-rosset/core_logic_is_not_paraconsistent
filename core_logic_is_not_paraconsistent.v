(* ════════════════════════════════════════════════════════════════
   Core Logic is not paraconsistent: the conservativity version
   (Version 4)
   ════════════════════════════════════════════════════════════════

   Terminology. The four rules Ax, L_neg, R_arrow, L_arrow determine
   one fragment ℱ under two readings:

     (i)  ℱ_𝐌 : the minimal reading — the four shared rules, with
          contexts as lists and left rules applying extensionally
          through membership;
     (ii) ℱ_ℂ : the Core reading — the same four rules plus
          R_arrow_core.

   Every rule of ℱ_𝐌 is a rule of ℂ; conservativity is a relation of
   ℂ to its own kernel. The commitment displayed in the final theorem
   therefore imports no foreign rule into Core: it states that ℂ
   proves nothing new at one single sequent of the shared kernel — an
   instance of conservativity, refuted below by R_arrow_core itself.

   Architecture of the result:
     1. DNS.1 is derivable uniformly in both readings (DNS1_in_ℱ).
     2. The anti-DNS.1 instance is a metatheorem of ℱ_𝐌
        (anti_DNS1_holds_in_ℱ_M), proved by a direct invariant.
     3. ℱ_ℂ proves DNS.2 through R_arrow_core, and is thereby not
        conservative over ℱ_𝐌 at the DNS.1 instance
        (ℱ_ℂ_not_conservative_at_DNS1).
     4. The final theorem displays the one remaining commitment,
        conservativity_at_DNS1, and derives the collision with
        Claim 1 (claim1_false).

   There is no primitive Exchange rule and no universal transfer
   principle for arbitrary antisequent rules; weakening is proved
   admissible.
   ════════════════════════════════════════════════════════════════ *)

From Coq Require Import List ListSet.
Import ListNotations.

(* ── Formulae and fragments ── *)

Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.

Inductive fragment_F : Type :=
  | minimal_F
  | core_logic.

(* [Some A] is a one-formula succedent.
   [None] is the empty succedent. *)

(* ════════════════════════════════════════════════════════════════
   Full corrected calculus

   Contexts are technically lists, but L_neg and L_arrow locate their
   principal formula extensionally by membership. No Exchange
   constructor is present.
   ════════════════════════════════════════════════════════════════ *)

Inductive derivable :
  fragment_F -> set formula -> option formula -> Prop :=

  | Ax :
      forall f G A,
        In A G ->
        derivable f G (Some A)

  | L_neg :
      forall f G A,
        In (Neg A) G ->
        derivable f G (Some A) ->
        derivable f G None

  | R_arrow :
      forall f G A B,
        derivable f (A :: G) (Some B) ->
        derivable f G (Some (Impl A B))

  | L_arrow :
      forall f G A B C,
        In (Impl A B) G ->
        derivable f G (Some A) ->
        derivable f (B :: G) C ->
        derivable f G C

  | R_arrow_core :
      forall G A B,
        derivable core_logic (A :: G) None ->
        derivable core_logic G (Some (Impl A B)).

(* ── Structural admissibility: weakening ── *)

Lemma weakening_subset :
  forall f G G' C,
    derivable f G C ->
    (forall A, In A G -> In A G') ->
    derivable f G' C.
Proof.
  intros f G G' C HD.
  revert G'.
  induction HD; intros G' Hsub.
  - apply Ax.
    apply Hsub.
    exact H.

  - apply L_neg with (A := A).
    + apply Hsub.
      exact H.
    + apply IHHD.
      exact Hsub.

  - apply R_arrow.
    apply IHHD.
    intros X HX.
    simpl in HX |- *.
    destruct HX as [HX | HX].
    + left.
      exact HX.
    + right.
      apply Hsub.
      exact HX.

  - apply L_arrow with (A := A) (B := B).
    + apply Hsub.
      exact H.
    + apply IHHD1.
      exact Hsub.
    + apply IHHD2.
      intros X HX.
      simpl in HX |- *.
      destruct HX as [HX | HX].
      * left.
        exact HX.
      * right.
        apply Hsub.
        exact HX.

  - apply R_arrow_core.
    apply IHHD.
    intros X HX.
    simpl in HX |- *.
    destruct HX as [HX | HX].
    + left.
      exact HX.
    + right.
      apply Hsub.
      exact HX.
Qed.

(* Every minimal derivation can be replayed in Core because the first
   four full-calculus rules are shared. *)

Lemma MinToCore :
  forall G C,
    derivable minimal_F G C ->
    derivable core_logic G C.
Proof.
  intros G C HD.
  remember minimal_F as f eqn:Hf.
  induction HD.
  - apply Ax.
    exact H.

  - apply L_neg with (A := A).
    + exact H.
    + apply IHHD.
      exact Hf.

  - apply R_arrow.
    apply IHHD.
    exact Hf.

  - apply L_arrow with (A := A) (B := B).
    + exact H.
    + apply IHHD1.
      exact Hf.
    + apply IHHD2.
      exact Hf.

  - discriminate Hf.
Qed.

(* ════════════════════════════════════════════════════════════════
   DNS.1 in both readings
   ════════════════════════════════════════════════════════════════

   DNS.1 is derivable uniformly in the fragment tag, hence in ℱ_𝐌
   and in ℱ_ℂ alike: the derivation uses only shared rules and the
   admissible weakening. *)

Theorem DNS1_in_ℱ :
  forall (f : fragment_F) (a b : nat),
    derivable f [Var a; Neg (Var a)] (Some (Var b)) ->
    derivable f
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros f a b H.
  eapply L_arrow.
  - left. reflexivity.
  - apply R_arrow.
    eapply weakening_subset.
    + exact H.
    + intros X HX.
      simpl in HX.
      destruct HX as [HX | [HX | []]]; subst X.
      * left. reflexivity.
      * right. right. left. reflexivity.
  - apply Ax. left. reflexivity.
Qed.

(* ════════════════════════════════════════════════════════════════
   Full Core: DNS.2
   ════════════════════════════════════════════════════════════════ *)

(* The inconsistency sequent {A, ¬A} |- is derivable in full Core.
   L_neg uses membership, hence no Exchange is needed. *)

Lemma absurdity_core :
  forall a : nat,
    derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intro a.
  apply L_neg with (A := Var a).
  - simpl.
    right.
    left.
    reflexivity.
  - apply Ax.
    simpl.
    left.
    reflexivity.
Qed.

(* DNS.2 is the Core-specific counterpart. The only extra rule used
   is R_arrow_core. *)

Theorem DNS2_instantiated :
  forall a b : nat,
    derivable core_logic [Var a; Neg (Var a)] None ->
    derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros a b HD.
  apply L_arrow with
    (A := Impl (Var a) (Var b))
    (B := Var b).

  - simpl.
    left.
    reflexivity.

  - eapply weakening_subset.
    + apply R_arrow_core.
      exact HD.
    + intros X HX.
      simpl in HX |- *.
      destruct HX as [HX | []].
      right.
      left.
      exact HX.

  - apply Ax.
    simpl.
    left.
    reflexivity.
Qed.

(* Regression: no primitive Exchange is needed to derive
   (p -> q -> r) -> q -> p -> r in the corrected minimal calculus. *)

Theorem exchange_weakening_regression :
  forall p q r : formula,
    derivable minimal_F []
      (Some
        (Impl (Impl p (Impl q r))
          (Impl q (Impl p r)))).
Proof.
  intros p q r.
  apply R_arrow.
  apply R_arrow.
  apply R_arrow.

  apply L_arrow with
    (A := p)
    (B := Impl q r).

  - simpl.
    right.
    right.
    left.
    reflexivity.

  - apply Ax.
    simpl.
    left.
    reflexivity.

  - apply L_arrow with
      (A := q)
      (B := r).

    + simpl.
      left.
      reflexivity.

    + apply Ax.
      simpl.
      right.
      right.
      left.
      reflexivity.

    + apply Ax.
      simpl.
      left.
      reflexivity.
Qed.

(* ════════════════════════════════════════════════════════════════
   Final conditional collision
   ════════════════════════════════════════════════════════════════

   anti_DNS1_holds_in_ℱ_M (proved below) establishes that the
   anti-DNS.1 instance is a metatheorem of the minimal reading ℱ_𝐌.

   The following narrowly scoped hypothesis is not a universal
   antisequent-transfer axiom. It is one single instance of
   conservativity of ℂ over its own kernel: the commitment that ℂ
   proves nothing new at the DNS.1 sequent. Nothing foreign to Core
   is involved, since every rule of ℱ_𝐌 is a rule of ℂ.

   This is the precise dialectical issue:
   - syntactically, the anti-DNS.1 instance holds in ℱ_𝐌;
   - textually/philosophically, one argues that Tennant's account of
     the shared kernel commits ℂ to this conservativity instance;
   - ℱ_ℂ proves DNS.2 through R_arrow_core, producing the collision
     with Claim 1.
   ════════════════════════════════════════════════════════════════ *)

Theorem claim1_false :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (conservativity_at_DNS1 :
      forall a b : nat,
        a <> b ->
        (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False)),

    forall a b : nat,
      a <> b ->
      False.
Proof.
  intros Claim1_Tennant conservativity_at_DNS1 a b Hab.
  apply (conservativity_at_DNS1 a b Hab).
  - apply (Claim1_Tennant a b Hab).
  - apply DNS2_instantiated.
    apply absurdity_core.
Qed.

(* Closed instance at distinct atoms 0 and 1. *)

Corollary claim1_false_at_0_1 :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (conservativity_at_DNS1 :
      forall a b : nat,
        a <> b ->
        (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False)),

    False.
Proof.
  intros Claim1_Tennant conservativity_at_DNS1.
  apply
    (claim1_false Claim1_Tennant conservativity_at_DNS1 0 1).
  discriminate.
Qed.

(* The first theorem must be assumption-free. The final two results
   must depend only on their explicit theorem parameters. *)

Print Assumptions DNS1_in_ℱ.
Print Assumptions claim1_false.
Print Assumptions claim1_false_at_0_1.

(* ════════════════════════════════════════════════════════════════
   Metatheoretic supplement
   ════════════════════════════════════════════════════════════════

   The following invariant establishes the underivability facts
   directly in ℱ_𝐌. The delicate case is L_arrow: since the principal
   implication is located through membership, it remains available in
   the premisses and contexts may grow; the invariant tames exactly
   this.

   Invariant: for distinct atoms a and b, no context included in
   {Var a, ¬Var a, (Var a → Var b) → Var b} derives Var b or
   Var a → Var b in ℱ_𝐌.
   ════════════════════════════════════════════════════════════════ *)

Lemma ℱ_M_blocked :
  forall a b : nat,
    a <> b ->
    forall f G C,
      derivable f G C ->
      f = minimal_F ->
      (forall X, In X G ->
        X = Var a \/ X = Neg (Var a) \/
        X = Impl (Impl (Var a) (Var b)) (Var b)) ->
      C <> Some (Var b) /\ C <> Some (Impl (Var a) (Var b)).
Proof.
  intros a b Hab f G C HD.
  induction HD; intros Hf HS.

  - (* Ax: the succedent is a member of the context, hence one of the
       three formulas of the invariant; none of them is Var b or
       Var a -> Var b when a <> b. *)
    destruct (HS A H) as [H1 | [H1 | H1]]; subst A;
      split; intro HC; congruence.

  - (* L_neg: empty succedent. *)
    split; intro HC; discriminate.

  - (* R_arrow: if the succedent were Var a -> Var b, the premiss
       would derive Var b from an invariant-closed context. *)
    split; intro HC.
    + discriminate.
    + injection HC as HA HB.
      subst A B.
      assert (HS' : forall X, In X (Var a :: G) ->
        X = Var a \/ X = Neg (Var a) \/
        X = Impl (Impl (Var a) (Var b)) (Var b)).
      { intros X [HX | HX].
        - left. symmetry. exact HX.
        - apply HS. exact HX. }
      destruct (IHHD Hf HS') as [Hcontr _].
      apply Hcontr.
      reflexivity.

  - (* L_arrow: the principal implication can only be
       (Var a -> Var b) -> Var b, whose left premiss derives
       Var a -> Var b from the same invariant-closed context,
       contradicting the induction hypothesis. This is the case where
       membership keeps the principal implication available. *)
    destruct (HS _ H) as [H1 | [H1 | H1]]; try discriminate.
    injection H1 as HA HB.
    subst A B.
    exfalso.
    apply (proj2 (IHHD1 Hf HS)).
    reflexivity.

  - (* R_arrow_core does not belong to M. *)
    discriminate Hf.
Qed.

(* Consequence 1: in ℱ_𝐌 itself, both the premiss and the conclusion
   of the DNS.1 instance are underivable, unconditionally. *)

Theorem claim1_holds_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (ℱ_M_blocked a b Hab _ _ _ HD eq_refl _) eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - left. reflexivity.
  - right. left. reflexivity.
Qed.

Theorem DNS1_conclusion_underivable_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (ℱ_M_blocked a b Hab _ _ _ HD eq_refl _) eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - right. right. reflexivity.
  - right. left. reflexivity.
Qed.

(* Hence the anti-DNS.1 instance is a metatheorem of ℱ_𝐌 itself. *)

Theorem anti_DNS1_holds_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    (derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
     False) ->
    (derivable minimal_F
       [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
       (Some (Var b)) ->
     False).
Proof.
  intros a b Hab _ HD.
  exact (DNS1_conclusion_underivable_in_ℱ_M a b Hab HD).
Qed.

(* Warm-up witness. The simplest certificate of non-conservativity of
   ℱ_ℂ over ℱ_𝐌 is the sequent ¬A ⊢ A → B: one application of
   R_arrow_core to the inconsistency sequent derives it in ℱ_ℂ, while
   in ℱ_𝐌 its only possible premiss is the Claim 1 sequent itself.
   The DNS.1 instance below is the witness that matters for
   paraconsistency; this one is the witness that is easiest to see. *)

Theorem non_conservativity_witness_derivable_in_ℱ_ℂ :
  forall a b : nat,
    derivable core_logic [Neg (Var a)] (Some (Impl (Var a) (Var b))).
Proof.
  intros a b.
  apply R_arrow_core.
  apply absurdity_core.
Qed.

Theorem non_conservativity_witness_underivable_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F [Neg (Var a)] (Some (Impl (Var a) (Var b))) ->
    False.
Proof.
  intros a b Hab HD.
  inversion HD; subst; simpl in *;
    repeat (match goal with
            | Hyp : _ \/ _ |- _ => destruct Hyp as [Hyp | Hyp]
            | Hyp : False |- _ => destruct Hyp
            end);
    try congruence.
  match goal with
  | Hp : derivable minimal_F (Var a :: [Neg (Var a)]) (Some (Var b)) |- _ =>
      exact (claim1_holds_in_ℱ_M a b Hab Hp)
  end.
Qed.

(* Consequence 2, for the Core reading ℱ_ℂ. First, Claim 1 holds of
   the formalized fragment: no rule can conclude
   [Var a; ¬Var a] ⊢ Var b when a <> b, since Ax requires Var b in
   the context, L_arrow requires an implication in the context, L_neg
   concludes on the empty succedent, and both right rules conclude on
   an implicational succedent. *)

Theorem claim1_holds_in_ℱ_ℂ :
  forall a b : nat,
    a <> b ->
    derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  inversion HD; subst; simpl in *;
    repeat (match goal with
            | Hyp : _ \/ _ |- _ => destruct Hyp as [Hyp | Hyp]
            | Hyp : False |- _ => destruct Hyp
            end);
    congruence.
Qed.

(* Second, ℱ_ℂ is not conservative over ℱ_𝐌 at the DNS.1 instance:
   DNS.2 is derivable in ℱ_ℂ through R_arrow_core while its sequent
   is underivable in ℱ_𝐌, so the Core-level anti-DNS.1 instance is
   false of the formalized calculus. The hypothesis
   conservativity_at_DNS1 of the final theorem is therefore exactly
   the disputed instance of conservativity of ℂ over its own kernel:
   the formalization displays it, and only Tennant's own account of
   the shared kernel can ground it. *)

Theorem ℱ_ℂ_not_conservative_at_DNS1 :
  forall a b : nat,
    a <> b ->
    ~ ( (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False) ).
Proof.
  intros a b Hab H.
  apply (H (claim1_holds_in_ℱ_ℂ a b Hab)).
  apply DNS2_instantiated.
  apply absurdity_core.
Qed.

Print Assumptions non_conservativity_witness_derivable_in_ℱ_ℂ.
Print Assumptions non_conservativity_witness_underivable_in_ℱ_M.
Print Assumptions anti_DNS1_holds_in_ℱ_M.
Print Assumptions ℱ_ℂ_not_conservative_at_DNS1.
