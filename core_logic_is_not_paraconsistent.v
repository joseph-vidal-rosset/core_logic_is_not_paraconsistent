(* ════════════════════════════════════════════════════════════════
   Core Logic is not paraconsistent: the refutation-system version
   (Version 6 — the arXiv/AJL appendix file)
   ════════════════════════════════════════════════════════════════

   This file certifies, block by block, the four-step proof of the
   paper. The blocks correspond to the steps as follows.

     Block A — the language and the calculus: one fragment ℱ (rules
        Ax, L¬, R→, L→) under two readings, ℱ_𝐌 (minimal) and ℱ_ℂ
        (Core, adding R→ℂ). Section 2.1 of the paper.
     Block B — Step 1: DNS.1 and DNS.2 are derivable. Section 2.2.
     Block C — Step 2: DNS.1 is invertible in ℱ_𝐌, by structural
        induction on derivations. Section 2.3.
     Block D — Step 3: the refutation rule anti-DNS.1, contrapositive
        of the invertibility, and the refutation system in the sense
        of Łukasiewicz, Tiomkin and Goranko: Claim 1 as its only
        rejection axiom, anti-DNS.1 as its only refutation rule,
        Ł-correct for ℱ_𝐌. Section 2.4.
     Block E — Step 4: the contradiction. The same refutation system
        is Ł-incorrect for ℱ_ℂ, and the conditional collision theorem
        derives False from the two displayed commitments. Section 2.5.
     Block F — the status of the second commitment: the fragment
        verifies Claim 1, and refutes the commitment through R→ℂ.
        Reply to the anticipated objection, Section 2.5.

   Verification: every Print Assumptions at the end of this file
   returns "Closed under the global context" — nothing is assumed;
   the two principles the argument grants to Tennant are explicit
   hypotheses of the final theorem, not axioms.
   ════════════════════════════════════════════════════════════════ *)

(* ══ Block A — Language and calculus ══ *)

From Coq Require Import List ListSet.
Import ListNotations.

Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.

Inductive fragment_F : Type :=
  | minimal_F
  | core_logic.

(* [Some A] is a one-formula succedent.
   [None] is the empty succedent.
   Contexts are technically lists, but the left rules locate their
   principal formula extensionally, by membership: no structural
   rule is primitive. An antisequent Γ ⊬ C is rendered directly as
   the type [derivable f G C -> False]. *)

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

(* ══ Block B — Step 1: DNS.1 and DNS.2 are derivable ══ *)

(* Context monotonicity. This lemma is NOT Tennant's Weakening —
   no such rule exists in ℂ, and none is added here — and it is
   NEITHER Cut NOR transitivity: no two derivations are composed,
   no cut formula exists, no formula is eliminated. It rebuilds ONE
   derivation, unchanged and height-preservingly, in a larger pool
   of available assumptions. Its ground is the set convention on
   contexts: [derivable f G C] says that some subsequent Δ ⊆ G is
   Tennant-derivable ⊢ C, so extending the pool is deductively
   inert — it is the very junction of contexts (Δ, Γ) that
   Tennant's own rule L→ performs notationally when it introduces
   its principal formula beside the contexts of its premisses.
   Safety is two-directional: the monotone encoding derives MORE
   sequents than Tennant's strict reading, so every underivability
   proved below holds a fortiori of the strict reading; and the
   derivable witness of the collision uses every formula of its
   context, so no dilution slack is exploited on the positive side.
   Proof by induction on the derivation. *)

Lemma context_monotonicity :
  forall f G G' C,
    derivable f G C ->
    (forall A, In A G -> In A G') ->
    derivable f G' C.
Proof.
  intros f G G' C HD.
  revert G'.
  induction HD; intros G' Hsub.
  - apply Ax. apply Hsub. exact H.
  - apply L_neg with (A := A).
    + apply Hsub. exact H.
    + apply IHHD. exact Hsub.
  - apply R_arrow.
    apply IHHD.
    intros X HX. simpl in HX |- *.
    destruct HX as [HX | HX].
    + left. exact HX.
    + right. apply Hsub. exact HX.
  - apply L_arrow with (A := A) (B := B).
    + apply Hsub. exact H.
    + apply IHHD1. exact Hsub.
    + apply IHHD2.
      intros X HX. simpl in HX |- *.
      destruct HX as [HX | HX].
      * left. exact HX.
      * right. apply Hsub. exact HX.
  - apply R_arrow_core.
    apply IHHD.
    intros X HX. simpl in HX |- *.
    destruct HX as [HX | HX].
    + left. exact HX.
    + right. apply Hsub. exact HX.
Qed.

(* The inconsistency sequent ¬A, A ⊢ that feeds DNS.2, immediate
   since L¬ locates ¬A by membership. *)

Lemma absurdity_core :
  forall a : nat,
    derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intro a.
  apply L_neg with (A := Var a).
  - simpl. right. left. reflexivity.
  - apply Ax. simpl. left. reflexivity.
Qed.

(* DNS.1, proved uniformly in the fragment indicator f, hence at
   once in ℱ_𝐌 and in ℱ_ℂ: its derivation uses only the four shared
   rules and context monotonicity. *)

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
    eapply context_monotonicity.
    + exact H.
    + intros X HX. simpl in HX.
      destruct HX as [HX | [HX | []]]; subst X.
      * left. reflexivity.
      * right. right. left. reflexivity.
  - apply Ax. left. reflexivity.
Qed.

(* DNS.2 in the Core reading, through R→ℂ. *)

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
  - simpl. left. reflexivity.
  - eapply context_monotonicity.
    + apply R_arrow_core. exact HD.
    + intros X HX. simpl in HX |- *.
      destruct HX as [HX | []].
      right. left. exact HX.
  - apply Ax. simpl. left. reflexivity.
Qed.

(* ══ Block C — Step 2: DNS.1 is invertible in ℱ_𝐌 ══ *)

(* The inversion lemma, by structural induction on derivations —
   von Plato's method, adapted to extensional contexts: since the
   left rules locate their principal formula by membership, the
   principal implication remains available in the premisses and
   contexts may grow; the induction is therefore carried under an
   invariant on contexts included in {A, ¬A, (A→B)→B}, and it
   establishes that no ℱ_𝐌-derivation from such a context concludes
   B or A→B. The case R_arrow_core is excluded by typing
   (discriminate Hf): the Coq counterpart of Tennant's consistency
   proviso for contexts. *)

Lemma DNS1_inversion_lemma :
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

  - (* Ax: the succedent is a member of the context, hence one of
       the three formulas of the invariant; none of them is Var b or
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
       contradicting the induction hypothesis. This is the case
       where membership keeps the principal implication available. *)
    destruct (HS _ H) as [H1 | [H1 | H1]]; try discriminate.
    injection H1 as HA HB.
    subst A B.
    destruct (proj2 (IHHD1 Hf HS) eq_refl).

  - (* R_arrow_core does not belong to ℱ_𝐌. *)
    discriminate Hf.
Qed.

(* First corollary: the invertibility of DNS.1 at the decisive
   instance is a metatheorem of ℱ_𝐌. *)

Theorem DNS1_invertible_at_decisive_instance_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)) ->
    derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b Hab HD.
  assert (HS : forall X,
      In X [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)] ->
      X = Var a \/ X = Neg (Var a) \/
      X = Impl (Impl (Var a) (Var b)) (Var b)).
  { intros X HX.
    simpl in HX.
    destruct HX as [HX | [HX | []]]; subst X.
    - right. right. reflexivity.
    - right. left. reflexivity. }
  (* The antecedent is refuted by the inversion lemma; the final
     step is a case analysis with zero cases on the resulting proof
     of False — the empty recursor of the inductive type False, not
     an ex falso axiom: the object calculus has no ⊥ and no such
     rule. *)
  destruct (proj1 (DNS1_inversion_lemma a b Hab _ _ _ HD eq_refl HS)
              eq_refl).
Qed.

(* Second corollary: Claim 1 holds of ℱ_𝐌 — the premiss of the
   DNS.1 instance is underivable there, unconditionally, for
   distinct atoms. *)

Theorem claim1_holds_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (DNS1_inversion_lemma a b Hab _ _ _ HD eq_refl _)
            eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - left. reflexivity.
  - right. left. reflexivity.
Qed.

(* Third corollary: the conclusion of the DNS.1 instance is
   underivable in ℱ_𝐌 as well. *)

Theorem DNS1_conclusion_underivable_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (DNS1_inversion_lemma a b Hab _ _ _ HD eq_refl _)
            eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - right. right. reflexivity.
  - right. left. reflexivity.
Qed.

(* ══ Block D — Step 3: the refutation rule anti-DNS.1 and the
   refutation system ══ *)

(* Anti-DNS.1 holds in ℱ_𝐌 as the CONTRAPOSITIVE of the certified
   invertibility — Goranko's correctness discipline for refutation
   calculi: a refutation rule is licensed by the correctness of its
   converse. Anti-DNS.1 is therefore not a meta-rule imported into
   the kernel: it is a rule derivable from the kernel's own
   invertibility, dormant in the shadow of the system. *)

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
  intros a b Hab Hprem HD.
  apply Hprem.
  apply (DNS1_invertible_at_decisive_instance_in_ℱ_M a b Hab).
  exact HD.
Qed.

(* The refutation system, in the sense of Łukasiewicz, Tiomkin
   (1988) and Goranko (Studia Logica 53, 1994): a deductive system
   for NON-provability, made of rejection axioms and refutation
   rules. Below, the smallest refutation system that the kernel
   licenses: Claim 1 as its only rejection axiom, anti-DNS.1 as its
   only refutation rule — the converse of the latter being the
   certified DNS1_invertible_at_decisive_instance_in_ℱ_M. *)

Inductive refutable : set formula -> option formula -> Prop :=

  | claim1_axiom :
      forall a b,
        a <> b ->
        refutable [Var a; Neg (Var a)] (Some (Var b))

  | anti_DNS1 :
      forall a b,
        refutable [Var a; Neg (Var a)] (Some (Var b)) ->
        refutable
          [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
          (Some (Var b)).

(* Ł-correctness for ℱ_𝐌: everything the refutation system rejects
   is underivable in the minimal reading. Induction on the
   refutation derivation; both cases discharge through the
   inversion lemma. *)

Theorem refutation_system_Ł_correct_for_ℱ_M :
  forall G C,
    refutable G C ->
    derivable minimal_F G C ->
    False.
Proof.
  intros G C HR.
  induction HR; intro HD.
  - exact (claim1_holds_in_ℱ_M a b H HD).
  - inversion HR; subst;
    match goal with
    | Hab : a <> b |- _ =>
        exact (DNS1_conclusion_underivable_in_ℱ_M a b Hab HD)
    end.
Qed.

(* ══ Block E — Step 4: the contradiction ══ *)

(* Ł-incorrectness for ℱ_ℂ: the same refutation system rejects a
   sequent that the Core reading derives, the witness being produced
   by R→ℂ alone. A rejection assertion has inferential content only
   inside a refutation system; the smallest one available to Core's
   kernel rejects what Core proves. This is the certified form of
   the contradiction involved in asserting Claim 1. *)

Theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
  exists G C,
    refutable G C /\ derivable core_logic G C.
Proof.
  exists [Impl (Impl (Var 0) (Var 1)) (Var 1); Neg (Var 0)].
  exists (Some (Var 1)).
  split.
  - apply anti_DNS1.
    apply claim1_axiom.
    discriminate.
  - apply DNS2_instantiated.
    apply absurdity_core.
Qed.

(* The conditional collision theorem. False is derived from two
   NAMED HYPOTHESES and the proved lemmas of this file — no axiom
   is declared anywhere. The first hypothesis states Claim 1,
   restricted to distinct atoms (so that the axiom rule cannot
   trivialise it), as Tennant posits it. The second,
   anti_DNS1_rule_for_ℂ, states that the kernel's refutation rule
   anti-DNS.1 governs ℂ's rejection assertion at this single
   sequent — in Goranko's discipline, that the licence of the rule,
   the invertibility of DNS.1 certified above for the kernel,
   survives in ℂ's own reading. Nothing foreign to Core is involved,
   since every rule of ℱ_𝐌 is a rule of ℂ. *)

Theorem claim1_false :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_rule_for_ℂ :
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
  intros Claim1_Tennant anti_DNS1_rule_for_ℂ a b Hab.
  apply (anti_DNS1_rule_for_ℂ a b Hab).
  - apply (Claim1_Tennant a b Hab).
  - apply DNS2_instantiated.
    apply absurdity_core.
Qed.

(* A closed instance at the concrete atoms 0 and 1 discharges the
   last quantifiers. *)

Corollary claim1_false_at_0_1 :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_rule_for_ℂ :
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
  intros Claim1_Tennant anti_DNS1_rule_for_ℂ.
  apply (claim1_false Claim1_Tennant anti_DNS1_rule_for_ℂ 0 1).
  discriminate.
Qed.

(* ══ Block F — Status of the second commitment ══ *)

(* The certification settles the status of anti_DNS1_rule_for_ℂ
   completely, on both sides. In the minimal reading it is a
   metatheorem, proved outright (anti_DNS1_holds_in_ℱ_M above). In
   the Core reading, the formalisation is charitable to Tennant —
   the fragment verifies Claim 1 itself, by structural inversion,
   not by failure of search: *)

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

(* — and yet, DNS.2 being derivable through R→ℂ, the Core reading
   refutes the commitment: the converse of anti-DNS.1, the
   invertibility of DNS.1, does not survive the passage from ℱ_𝐌 to
   ℱ_ℂ. The refutation rule anti-DNS.1 is thereby Ł-incorrect for
   ℱ_ℂ — the rule-level form of the system-level verdict of
   Block E, and the exact refutation, inside the calculus, of the
   hypothesis anti_DNS1_rule_for_ℂ of the final theorem. (In
   Versions 4 and 5 of this file the same certified fact was named
   ℱ_ℂ_not_conservative_at_DNS1.) *)

Theorem anti_DNS1_Ł_incorrect_for_ℱ_ℂ :
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

(* ══ Verification ══ *)

Print Assumptions DNS1_in_ℱ.
Print Assumptions DNS2_instantiated.
Print Assumptions DNS1_invertible_at_decisive_instance_in_ℱ_M.
Print Assumptions claim1_holds_in_ℱ_M.
Print Assumptions DNS1_conclusion_underivable_in_ℱ_M.
Print Assumptions anti_DNS1_holds_in_ℱ_M.
Print Assumptions refutation_system_Ł_correct_for_ℱ_M.
Print Assumptions refutation_system_Ł_incorrect_for_ℱ_ℂ.
Print Assumptions claim1_false.
Print Assumptions claim1_false_at_0_1.
Print Assumptions claim1_holds_in_ℱ_ℂ.
Print Assumptions anti_DNS1_Ł_incorrect_for_ℱ_ℂ.
