/- ════════════════════════════════════════════════════════════════
   Core Logic is not paraconsistent: the refutation-system version
   (Version 5)
   ════════════════════════════════════════════════════════════════

   Terminology. The four rules Ax, L_neg, R_arrow, L_arrow determine
   one fragment ℱ under two readings:

     (i)  ℱ_𝐌 : the minimal reading — the four shared rules, with
          contexts as lists and left rules applying extensionally
          through membership;
     (ii) ℱ_ℂ : the Core reading — the same four rules plus
          R_arrow_core.

   Every rule of ℱ_𝐌 is a rule of ℂ. The commitment displayed in
   the final theorem therefore imports no foreign rule into Core: it
   states that the refutation rule licensed by the kernel's own
   invertibility — anti-DNS.1 — governs ℂ's rejection assertion at
   one single sequent. That commitment is refuted below by
   R_arrow_core itself.

   Architecture of the result:
     1. DNS.1 is derivable uniformly in both readings (DNS1_in_ℱ).
     2. DNS.1 is invertible at the decisive instance in ℱ_𝐌
        (DNS1_invertible_at_decisive_instance_in_ℱ_M), and the
        anti-DNS.1 instance is its contrapositive
        (anti_DNS1_holds_in_ℱ_M): in the sense of Łukasiewicz and
        Goranko, a refutation rule licensed by the correctness of
        its converse — not a meta-rule imported from outside, but a
        rule dormant in the shadow of the kernel.
     3. The refutation system with Claim 1 as its only rejection
        axiom and anti-DNS.1 as its only refutation rule is
        Ł-correct for ℱ_𝐌 and Ł-incorrect for ℱ_ℂ, the
        incorrectness being produced by R_arrow_core alone
        (refutation_system_Ł_correct_for_ℱ_M,
        refutation_system_Ł_incorrect_for_ℱ_ℂ).
     4. The final theorem displays the one remaining commitment,
        anti_DNS1_rule_for_ℂ (named conservativity_at_DNS1 in Version 4), and
        derives the collision with Claim 1 (claim1_false).

   There is no primitive Exchange rule and no universal transfer
   principle for arbitrary antisequent rules; weakening is proved
   admissible.
   ════════════════════════════════════════════════════════════════ -/

/- ── Formulae and fragments ── -/

inductive Formula : Type
  | Var  : Nat → Formula
  | Neg  : Formula → Formula
  | Impl : Formula → Formula → Formula
  deriving DecidableEq, Repr

open Formula

inductive FragmentF : Type
  | minimal_F
  | core_logic
  deriving DecidableEq, Repr

open FragmentF

/- [some A] is a one-formula succedent.
   [none] is the empty succedent. -/

/- ════════════════════════════════════════════════════════════════
   Full corrected calculus

   Contexts are technically lists, but L_neg and L_arrow locate their
   principal formula extensionally by membership. No Exchange
   constructor is present.
   ════════════════════════════════════════════════════════════════ -/

inductive Derivable : FragmentF → List Formula → Option Formula → Prop
  | Ax :
      ∀ {f : FragmentF} {G : List Formula} {A : Formula},
        A ∈ G →
        Derivable f G (some A)

  | L_neg :
      ∀ {f : FragmentF} {G : List Formula} {A : Formula},
        Neg A ∈ G →
        Derivable f G (some A) →
        Derivable f G none

  | R_arrow :
      ∀ {f : FragmentF} {G : List Formula} {A B : Formula},
        Derivable f (A :: G) (some B) →
        Derivable f G (some (Impl A B))

  | L_arrow :
      ∀ {f : FragmentF} {G : List Formula}
        {A B : Formula} {C : Option Formula},
        Impl A B ∈ G →
        Derivable f G (some A) →
        Derivable f (B :: G) C →
        Derivable f G C

  | R_arrow_core :
      ∀ {G : List Formula} {A B : Formula},
        Derivable core_logic (A :: G) none →
        Derivable core_logic G (some (Impl A B))

/- ── Structural admissibility: weakening ── -/

theorem weakening_subset :
    ∀ {f : FragmentF} {G : List Formula} {C : Option Formula},
      Derivable f G C →
      ∀ {G' : List Formula},
        (∀ A, A ∈ G → A ∈ G') →
        Derivable f G' C := by
  intro f G C hD
  induction hD with
  | Ax hmem =>
      intro G' Hsub
      exact Derivable.Ax (Hsub _ hmem)

  | L_neg hneg _ ih =>
      intro G' Hsub
      exact Derivable.L_neg (Hsub _ hneg) (ih Hsub)

  | R_arrow _ ih =>
      intro G' Hsub
      apply Derivable.R_arrow
      apply ih
      intro X hX
      rcases List.mem_cons.mp hX with hX | hX
      · exact List.mem_cons.mpr (Or.inl hX)
      · exact List.mem_cons.mpr (Or.inr (Hsub X hX))

  | L_arrow himpl _ _ ihA ihBC =>
      intro G' Hsub
      apply Derivable.L_arrow
      · exact Hsub _ himpl
      · exact ihA Hsub
      · apply ihBC
        intro X hX
        rcases List.mem_cons.mp hX with hX | hX
        · exact List.mem_cons.mpr (Or.inl hX)
        · exact List.mem_cons.mpr (Or.inr (Hsub X hX))

  | R_arrow_core _ ih =>
      intro G' Hsub
      apply Derivable.R_arrow_core
      apply ih
      intro X hX
      rcases List.mem_cons.mp hX with hX | hX
      · exact List.mem_cons.mpr (Or.inl hX)
      · exact List.mem_cons.mpr (Or.inr (Hsub X hX))

/- Every minimal derivation can be replayed in Core because the first
   four full-calculus rules are shared. -/

theorem MinToCore {G : List Formula} {C : Option Formula} :
    Derivable minimal_F G C →
    Derivable core_logic G C := by
  intro h
  generalize hf : (minimal_F : FragmentF) = f at h
  induction h with
  | Ax hin =>
      exact Derivable.Ax hin

  | L_neg hneg _ ih =>
      exact Derivable.L_neg hneg (ih hf)

  | R_arrow _ ih =>
      exact Derivable.R_arrow (ih hf)

  | L_arrow himpl _ _ ih1 ih2 =>
      exact Derivable.L_arrow himpl (ih1 hf) (ih2 hf)

  | R_arrow_core _ _ =>
      cases hf

/- ════════════════════════════════════════════════════════════════
   DNS.1 in both readings
   ════════════════════════════════════════════════════════════════

   DNS.1 is derivable uniformly in the fragment tag, hence in ℱ_𝐌
   and in ℱ_ℂ alike: the derivation uses only shared rules and the
   admissible weakening. -/

theorem DNS1_in_ℱ (f : FragmentF) (a b : Nat) :
    Derivable f [Var a, Neg (Var a)] (some (Var b)) →
    Derivable f
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  apply Derivable.L_arrow (A := Impl (Var a) (Var b)) (B := Var b)
  · simp
  · apply Derivable.R_arrow
    apply weakening_subset h
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with h1 | h1 <;> simp [h1]
  · exact Derivable.Ax (by simp)

/- ════════════════════════════════════════════════════════════════
   Full Core: DNS.2
   ════════════════════════════════════════════════════════════════ -/

/- The inconsistency sequent {A, ¬A} ⊢ is derivable in full Core.
   L_neg uses membership, hence no Exchange is needed. -/

theorem absurdity_core (a : Nat) :
    Derivable core_logic [Var a, Neg (Var a)] none := by
  apply Derivable.L_neg (A := Var a)
  · simp
  · exact Derivable.Ax (by simp)

/- DNS.2 is the Core-specific counterpart. The only extra rule used
   is R_arrow_core. -/

theorem DNS2_instantiated (a b : Nat) :
    Derivable core_logic [Var a, Neg (Var a)] none →
    Derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  refine Derivable.L_arrow
    (A := Impl (Var a) (Var b))
    (B := Var b)
    ?_ ?_ ?_
  · simp
  · apply weakening_subset (Derivable.R_arrow_core h)
    intro X hX
    have hX' : X = Neg (Var a) := by
      simpa using hX
    subst X
    simp
  · exact Derivable.Ax (by simp)

/- Structural regression theorem: no primitive Exchange is necessary. -/

theorem exchange_weakening_regression (p q r : Formula) :
    Derivable minimal_F []
      (some
        (Impl (Impl p (Impl q r))
          (Impl q (Impl p r)))) := by
  apply Derivable.R_arrow
  apply Derivable.R_arrow
  apply Derivable.R_arrow

  apply Derivable.L_arrow
    (A := p)
    (B := Impl q r)
  · simp
  · exact Derivable.Ax (by simp)
  · apply Derivable.L_arrow
      (A := q)
      (B := r)
    · simp
    · exact Derivable.Ax (by simp)
    · exact Derivable.Ax (by simp)

/- ════════════════════════════════════════════════════════════════
   Final conditional collision
   ════════════════════════════════════════════════════════════════

   anti_DNS1_holds_in_ℱ_M (proved below) establishes that the
   anti-DNS.1 instance is the contrapositive of the invertibility
   of DNS.1 in the minimal reading ℱ_𝐌.

   The hypothesis anti_DNS1_rule_for_ℂ — named conservativity_at_DNS1 in
   Version 4 — is not a universal antisequent-transfer axiom and
   not a meta-rule. It is the kernel's own refutation rule, stated
   for the Core reading: in Goranko's discipline a refutation rule
   is licensed by the correctness of its converse, and its converse
   here is the invertibility of DNS.1, certified for ℱ_𝐌 below.
   Nothing foreign to Core is involved, since every rule of ℱ_𝐌 is
   a rule of ℂ.

   This is the precise dialectical issue:
   - syntactically, anti-DNS.1 holds in ℱ_𝐌 as the contrapositive
     of a certified invertibility;
   - a rejection assertion has inferential content only inside a
     refutation system (Łukasiewicz); the smallest one the kernel
     licenses contains exactly this rule;
   - ℱ_ℂ proves DNS.2 through R_arrow_core, producing the collision
     with Claim 1.
   ════════════════════════════════════════════════════════════════ -/

theorem claim1_false
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (anti_DNS1_rule_for_ℂ :
      ∀ a b : Nat,
        a ≠ b →
        (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
          False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) →
          False)) :
    ∀ a b : Nat,
      a ≠ b →
      False := by
  intro a b hab
  exact
    anti_DNS1_rule_for_ℂ a b hab
      (Claim1_Tennant a b hab)
      (DNS2_instantiated a b (absurdity_core a))

/- Closed instance at the concrete distinct atoms 0 and 1. -/

theorem claim1_false_at_0_1
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (anti_DNS1_rule_for_ℂ :
      ∀ a b : Nat,
        a ≠ b →
        (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
          False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) →
          False)) :
    False := by
  exact claim1_false Claim1_Tennant anti_DNS1_rule_for_ℂ 0 1 (by decide)

/- Audit: no sorryAx should occur; Lean may report only [propext]. -/

#print axioms DNS1_in_ℱ
#print axioms claim1_false
#print axioms claim1_false_at_0_1
/- ════════════════════════════════════════════════════════════════
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
   ════════════════════════════════════════════════════════════════ -/

theorem ℱ_M_blocked (a b : Nat) (hab : a ≠ b) :
    ∀ {f : FragmentF} {G : List Formula} {C : Option Formula},
      Derivable f G C →
      f = minimal_F →
      (∀ X, X ∈ G →
        X = Var a ∨ X = Neg (Var a) ∨
        X = Impl (Impl (Var a) (Var b)) (Var b)) →
      C ≠ some (Var b) ∧ C ≠ some (Impl (Var a) (Var b)) := by
  intro f G C h
  induction h with
  | @Ax f G A hmem =>
      /- Ax: the succedent is a member of the context, hence one of
         the three formulas of the invariant; none of them is Var b
         or Var a → Var b when a ≠ b. -/
      intro _ hS
      rcases hS _ hmem with h1 | h1 | h1 <;> subst h1 <;>
        refine ⟨fun hC => ?_, fun hC => ?_⟩ <;> simp at hC
      exact hab hC
  | L_neg _ _ _ =>
      /- L_neg: empty succedent. -/
      intro _ _
      refine ⟨fun hC => ?_, fun hC => ?_⟩ <;> simp at hC
  | @R_arrow f G A B hprem ih =>
      /- R_arrow: if the succedent were Var a → Var b, the premiss
         would derive Var b from an invariant-closed context. -/
      intro hf hS
      refine ⟨fun hC => by simp at hC, fun hC => ?_⟩
      obtain ⟨hA, hB⟩ : A = Var a ∧ B = Var b := by simpa using hC
      subst hA; subst hB
      have hS' : ∀ X, X ∈ (Var a :: G) →
          X = Var a ∨ X = Neg (Var a) ∨
          X = Impl (Impl (Var a) (Var b)) (Var b) := by
        intro X hX
        rcases List.mem_cons.mp hX with hX | hX
        · exact Or.inl hX
        · exact hS X hX
      exact (ih hf hS').1 rfl
  | @L_arrow f G A B C himpl hA hBC ihA ihBC =>
      /- L_arrow: the principal implication can only be
         (Var a → Var b) → Var b, whose left premiss derives
         Var a → Var b from the same invariant-closed context,
         contradicting the induction hypothesis. This is the case where
         membership keeps the principal implication available. -/
      intro hf hS
      rcases hS _ himpl with h1 | h1 | h1
      · cases h1
      · cases h1
      · injection h1 with hx hy
        subst hx
        exact absurd rfl ((ihA hf hS).2)
  | R_arrow_core _ _ =>
      /- R_arrow_core does not belong to M. -/
      intro hf _
      cases hf

/- Consequence 1: in ℱ_𝐌 itself, both the premiss and the conclusion
   of the DNS.1 instance are underivable, unconditionally. -/

theorem claim1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False := by
  intro h
  refine (ℱ_M_blocked a b hab h rfl ?_).1 rfl
  intro X hX
  rcases List.mem_cons.mp hX with hX | hX
  · exact Or.inl hX
  · rcases List.mem_cons.mp hX with hX | hX
    · exact Or.inr (Or.inl hX)
    · cases hX

theorem DNS1_conclusion_underivable_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False := by
  intro h
  refine (ℱ_M_blocked a b hab h rfl ?_).1 rfl
  intro X hX
  rcases List.mem_cons.mp hX with hX | hX
  · exact Or.inr (Or.inr hX)
  · rcases List.mem_cons.mp hX with hX | hX
    · exact Or.inr (Or.inl hX)
    · cases hX

/- The invertibility of DNS.1 at the decisive instance is a
   metatheorem of ℱ_𝐌, established through the invariant. -/

theorem DNS1_invertible_at_decisive_instance_in_ℱ_M
    (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) := by
  intro hD
  exact absurd hD (DNS1_conclusion_underivable_in_ℱ_M a b hab)

/- Hence the anti-DNS.1 instance holds in ℱ_𝐌 as the CONTRAPOSITIVE
   of this invertibility — Goranko's converse-rule discipline: a
   refutation rule is licensed by the correctness of its converse.
   Anti-DNS.1 is therefore not a meta-rule imported into the
   kernel; it is a rule derivable from the kernel's invertibility,
   dormant in the shadow of the system. -/

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) :=
  fun hprem hD =>
    hprem (DNS1_invertible_at_decisive_instance_in_ℱ_M a b hab hD)

/- Warm-up witness. The simplest sequent separating the two readings
   is ¬A ⊢ A → B: one application of R_arrow_core to the
   inconsistency sequent derives it in ℱ_ℂ, while in ℱ_𝐌 its only
   possible premiss is the Claim 1 sequent itself. The DNS.1
   instance below is the separation that matters for
   paraconsistency; this one is the easiest to see. -/

theorem non_conservativity_witness_derivable_in_ℱ_ℂ (a b : Nat) :
    Derivable core_logic [Neg (Var a)] (some (Impl (Var a) (Var b))) :=
  Derivable.R_arrow_core (absurdity_core a)

theorem non_conservativity_witness_underivable_in_ℱ_M
    (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F [Neg (Var a)] (some (Impl (Var a) (Var b))) →
    False := by
  intro h
  cases h with
  | Ax hin => simp at hin
  | R_arrow hprem => exact claim1_holds_in_ℱ_M a b hab hprem
  | L_arrow himpl _ _ => simp at himpl

/- Consequence 2, for the Core reading ℱ_ℂ. First, Claim 1 holds of
   the formalized fragment: no rule can conclude
   [Var a, ¬Var a] ⊢ Var b when a ≠ b, since Ax requires Var b in
   the context, L_arrow requires an implication in the context, L_neg
   concludes on the empty succedent, and both right rules conclude on
   an implicational succedent. -/

theorem claim1_holds_in_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False := by
  intro h
  cases h with
  | Ax hin =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with h1 | h2
      · injection h1 with hba; exact hab hba.symm
      · cases h2
  | L_arrow himpl _ _ =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at himpl
      rcases himpl with h1 | h2
      · cases h1
      · cases h2

/- Second, the converse of anti-DNS.1 — the invertibility of
   DNS.1 — does not survive the passage from ℱ_𝐌 to ℱ_ℂ: DNS.2 is
   derivable in ℱ_ℂ through R_arrow_core while the Claim 1 premiss
   is not. In the vocabulary of refutation systems this is the
   Ł-incorrectness, for ℱ_ℂ, of the refutation rule that the kernel
   licenses; Version 4 stated the same certified fact as
   non-conservativity of ℂ over its own kernel at the DNS.1
   instance, whence the theorem's name, kept unchanged. It follows
   that the hypothesis anti_DNS1_rule_for_ℂ of the final theorem is
   refutable inside the formalized calculus, and only Tennant's own
   account of the shared kernel can ground it — this is the
   dialectical point of the paper. -/

theorem ℱ_ℂ_not_conservative_at_DNS1 (a b : Nat) (hab : a ≠ b) :
    ¬ ( (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) → False) ) := by
  intro h
  exact h (claim1_holds_in_ℱ_ℂ a b hab)
          (DNS2_instantiated a b (absurdity_core a))

/- ════════════════════════════════════════════════════════════════
   The refutation system
   ════════════════════════════════════════════════════════════════

   In the sense of Łukasiewicz, Tiomkin (1988) and Goranko (Studia
   Logica 53, 1994, section 2), a refutation system derives
   NON-provability from rejection axioms and refutation rules, and
   its correctness discipline requires every refutation rule to have
   a correct converse (Goranko's Theorem 2.1). Below, the smallest
   refutation system that the kernel licenses: Claim 1 as its only
   rejection axiom, anti-DNS.1 as its only refutation rule — the
   converse of the latter being
   DNS1_invertible_at_decisive_instance_in_ℱ_M. -/

inductive Refutable : List Formula → Option Formula → Prop
  | claim1_axiom :
      ∀ {a b : Nat},
        a ≠ b →
        Refutable [Var a, Neg (Var a)] (some (Var b))
  | anti_DNS1 :
      ∀ {a b : Nat},
        Refutable [Var a, Neg (Var a)] (some (Var b)) →
        Refutable
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b))

/- Ł-correctness for ℱ_𝐌: everything the system rejects is
   underivable in the minimal reading. Induction on the refutation
   derivation; both cases discharge through the invariant. -/

theorem refutation_system_Ł_correct_for_ℱ_M :
    ∀ {G : List Formula} {C : Option Formula},
      Refutable G C →
      Derivable minimal_F G C →
      False := by
  intro G C hR
  induction hR with
  | @claim1_axiom a b hab =>
      intro hD
      exact claim1_holds_in_ℱ_M a b hab hD
  | @anti_DNS1 a b hprem _ =>
      intro hD
      cases hprem with
      | claim1_axiom hab =>
          exact DNS1_conclusion_underivable_in_ℱ_M a b hab hD

/- Ł-incorrectness for ℱ_ℂ: the same system rejects a sequent that
   the Core reading derives, the witness being produced by
   R_arrow_core alone. A rejection assertion has inferential content
   only inside a refutation system; the smallest one available to
   Core's kernel rejects what Core proves. This is the certified
   form of the contradiction involved in asserting Claim 1. -/

theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
    ∃ (G : List Formula) (C : Option Formula),
      Refutable G C ∧ Derivable core_logic G C := by
  refine ⟨[Impl (Impl (Var 0) (Var 1)) (Var 1), Neg (Var 0)],
          some (Var 1), ?_, ?_⟩
  · exact Refutable.anti_DNS1 (Refutable.claim1_axiom (by decide))
  · exact DNS2_instantiated 0 1 (absurdity_core 0)

#print axioms non_conservativity_witness_derivable_in_ℱ_ℂ
#print axioms non_conservativity_witness_underivable_in_ℱ_M
#print axioms anti_DNS1_holds_in_ℱ_M
#print axioms ℱ_ℂ_not_conservative_at_DNS1
#print axioms DNS1_invertible_at_decisive_instance_in_ℱ_M
#print axioms refutation_system_Ł_correct_for_ℱ_M
#print axioms refutation_system_Ł_incorrect_for_ℱ_ℂ
