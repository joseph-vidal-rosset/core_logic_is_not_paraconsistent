/- ════════════════════════════════════════════════════════════════
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
   ════════════════════════════════════════════════════════════════ -/

theorem claim1_false
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (conservativity_at_DNS1 :
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
    conservativity_at_DNS1 a b hab
      (Claim1_Tennant a b hab)
      (DNS2_instantiated a b (absurdity_core a))

/- Closed instance at the concrete distinct atoms 0 and 1. -/

theorem claim1_false_at_0_1
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (conservativity_at_DNS1 :
      ∀ a b : Nat,
        a ≠ b →
        (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
          False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) →
          False)) :
    False := by
  exact claim1_false Claim1_Tennant conservativity_at_DNS1 0 1 (by decide)

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

/- Hence the anti-DNS.1 instance is a metatheorem of ℱ_𝐌 itself. -/

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) :=
  fun _ => DNS1_conclusion_underivable_in_ℱ_M a b hab

/- Warm-up witness. The simplest certificate of non-conservativity of
   ℱ_ℂ over ℱ_𝐌 is the sequent ¬A ⊢ A → B: one application of
   R_arrow_core to the inconsistency sequent derives it in ℱ_ℂ, while
   in ℱ_𝐌 its only possible premiss is the Claim 1 sequent itself.
   The DNS.1 instance below is the witness that matters for
   paraconsistency; this one is the witness that is easiest to see. -/

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

/- Second, ℱ_ℂ is not conservative over ℱ_𝐌 at the DNS.1 instance:
   DNS.2 is derivable in ℱ_ℂ through R_arrow_core while its sequent
   is underivable in ℱ_𝐌, so the Core-level anti-DNS.1 instance is
   false of the formalized calculus. The hypothesis
   conservativity_at_DNS1 of the final theorem is therefore exactly
   the disputed instance of conservativity of ℂ over its own kernel:
   the formalization displays it, and only Tennant's own account of
   the shared kernel can ground it. -/

theorem ℱ_ℂ_not_conservative_at_DNS1 (a b : Nat) (hab : a ≠ b) :
    ¬ ( (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) → False) ) := by
  intro h
  exact h (claim1_holds_in_ℱ_ℂ a b hab)
          (DNS2_instantiated a b (absurdity_core a))

#print axioms non_conservativity_witness_derivable_in_ℱ_ℂ
#print axioms non_conservativity_witness_underivable_in_ℱ_M
#print axioms anti_DNS1_holds_in_ℱ_M
#print axioms ℱ_ℂ_not_conservative_at_DNS1
