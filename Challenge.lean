/- ════════════════════════════════════════════════════════════════
   CHALLENGE — Core Logic is not paraconsistent: conservativity
   version (Version 4)
   ════════════════════════════════════════════════════════════════

   Trusted statements for the Lean Comparator.

   Terminology. The four rules Ax, L_neg, R_arrow, L_arrow determine
   one fragment ℱ under two readings: ℱ_𝐌, its minimal reading, and
   ℱ_ℂ, its Core reading, which adds R_arrow_core. Every rule of ℱ_𝐌
   is a rule of ℂ; conservativity is a relation of ℂ to its own
   kernel, so nothing foreign to Core is involved anywhere below.

   The trusted base consists of the corrected full calculus:
   - contexts are represented by lists;
   - left rules apply extensionally through membership;
   - there is no primitive Exchange rule;
   - R_arrow_core is available only in the Core reading.

   Four results are to be certified.

   (1) anti_DNS1_holds_in_ℱ_M: the anti-DNS.1 instance is a
       metatheorem of the minimal reading ℱ_𝐌 itself — both the
       premiss and the conclusion of the DNS.1 instance are
       underivable in ℱ_𝐌 for distinct atoms.

   (2) ℱ_ℂ_not_conservative_at_DNS1: the Core reading is not
       conservative over ℱ_𝐌 at the DNS.1 instance — DNS.2 is
       derivable in ℱ_ℂ through R_arrow_core while Claim 1 holds of
       the formalized fragment.

   (3) claim1_false: the conditional collision — Tennant's Claim 1
       (restricted to distinct atoms) and the conservativity
       commitment at the DNS.1 instance jointly entail False.

   (4) claim1_false_at_0_1: the closed instance at atoms 0 and 1.

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

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) := sorry

theorem ℱ_ℂ_not_conservative_at_DNS1 (a b : Nat) (hab : a ≠ b) :
    ¬ ( (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) → False) ) := sorry

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
      False := sorry

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
    False := sorry
