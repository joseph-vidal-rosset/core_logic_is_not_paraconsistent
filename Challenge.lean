/- ════════════════════════════════════════════════════════════════
   CHALLENGE — Core Logic is not paraconsistent: refutation-system
   version (Version 6, the arXiv/AJL appendix file)
   ════════════════════════════════════════════════════════════════

   Trusted statements for the Lean Comparator.

   The trusted base consists of:
   - the language and the calculus [Derivable]: one fragment ℱ
     (rules Ax, L_neg, R_arrow, L_arrow) under two readings,
     minimal_F (ℱ_𝐌) and core_logic (ℱ_ℂ, adding R_arrow_core);
     contexts are lists, the left rules locate their principal
     formula extensionally by membership, no structural rule is
     primitive, and R_arrow_core is restricted by typing to the
     Core reading;
   - the refutation system [Refutable], in the sense of
     Łukasiewicz, Tiomkin (1988) and Goranko (Studia Logica 53,
     1994): Claim 1 as its only rejection axiom, the anti-DNS.1
     instance as its only refutation rule.

   Twelve results are to be certified, matching the four steps of
   the paper and the status of its second commitment:

   Step 1 (derivability):
     (1) DNS1_in_ℱ — DNS.1 is derivable uniformly in both readings;
     (2) DNS2_instantiated — DNS.2 is derivable in the Core reading
         through R_arrow_core.
   Step 2 (invertibility):
     (3) DNS1_invertible_at_decisive_instance_in_ℱ_M;
     (4) claim1_holds_in_ℱ_M — the premiss of the instance is
         underivable in ℱ_𝐌;
     (5) DNS1_conclusion_underivable_in_ℱ_M — so is its conclusion.
   Step 3 (the refutation rule and the refutation system):
     (6) anti_DNS1_holds_in_ℱ_M — anti-DNS.1, contrapositive of the
         invertibility, is a metatheorem of ℱ_𝐌;
     (7) refutation_system_Ł_correct_for_ℱ_M — the refutation
         system is Ł-correct for the minimal reading.
   Step 4 (the contradiction):
     (8) refutation_system_Ł_incorrect_for_ℱ_ℂ — the same system
         rejects a sequent that the Core reading derives;
     (9) claim1_false — the conditional collision: Tennant's
         Claim 1 (restricted to distinct atoms) and the kernel's
         refutation rule stated for ℂ (anti_DNS1_rule_for_ℂ, named
         conservativity_at_DNS1 in Version 4) jointly entail False;
    (10) claim1_false_at_0_1 — the closed instance at atoms 0, 1.
   Status of the second commitment:
    (11) claim1_holds_in_ℱ_ℂ — the fragment verifies Claim 1;
    (12) anti_DNS1_Ł_incorrect_for_ℱ_ℂ — and refutes the
         commitment through R_arrow_core (named
         ℱ_ℂ_not_conservative_at_DNS1 in Versions 4 and 5).

   A passing candidate must prove these statements without sorry,
   admit, or non-Lean axioms; #print axioms may report [propext]
   only.
   ════════════════════════════════════════════════════════════════ -/


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

/- ════════════════════════════════════════════════════════════════
   Trusted statements
   ════════════════════════════════════════════════════════════════ -/

theorem DNS1_in_ℱ (f : FragmentF) (a b : Nat) :
    Derivable f [Var a, Neg (Var a)] (some (Var b)) →
    Derivable f
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := sorry

theorem DNS2_instantiated (a b : Nat) :
    Derivable core_logic [Var a, Neg (Var a)] none →
    Derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := sorry

theorem DNS1_invertible_at_decisive_instance_in_ℱ_M
    (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) := sorry

theorem claim1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False := sorry

theorem DNS1_conclusion_underivable_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False := sorry

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) := sorry

theorem refutation_system_Ł_correct_for_ℱ_M :
    ∀ {G : List Formula} {C : Option Formula},
      Refutable G C →
      Derivable minimal_F G C →
      False := sorry

theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
    ∃ (G : List Formula) (C : Option Formula),
      Refutable G C ∧ Derivable core_logic G C := sorry

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
      False := sorry

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
    False := sorry

theorem claim1_holds_in_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False := sorry

theorem anti_DNS1_Ł_incorrect_for_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    ¬ ( (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) → False) ) := sorry
