/- ════════════════════════════════════════════════════════════════
   CHALLENGE — Core Logic is not paraconsistent: refutation-system
   version (Version 5)
   ════════════════════════════════════════════════════════════════

   Trusted statements for the Lean Comparator.

   Terminology. The four rules Ax, L_neg, R_arrow, L_arrow determine
   one fragment ℱ under two readings: ℱ_𝐌, its minimal reading, and
   ℱ_ℂ, its Core reading, which adds R_arrow_core. Every rule of ℱ_𝐌
   is a rule of ℂ, so nothing foreign to Core is involved anywhere
   below.

   The trusted base consists of:
   - the corrected full calculus [Derivable]: contexts are lists,
     left rules apply extensionally through membership, there is no
     primitive Exchange rule, R_arrow_core is available only in the
     Core reading;
   - the refutation system [Refutable], in the sense of Łukasiewicz,
     Tiomkin (1988) and Goranko (Studia Logica 53, 1994): Claim 1 as
     its only rejection axiom, the anti-DNS.1 instance as its only
     refutation rule — the converse of the latter being the
     invertibility of DNS.1, certified below for ℱ_𝐌.

   Seven results are to be certified.

   (1) DNS1_invertible_at_decisive_instance_in_ℱ_M: DNS.1 is
       invertible at the decisive instance in the minimal reading.

   (2) anti_DNS1_holds_in_ℱ_M: the anti-DNS.1 instance holds in
       ℱ_𝐌 — the contrapositive of (1).

   (3) ℱ_ℂ_not_conservative_at_DNS1: the converse of anti-DNS.1
       does not survive the passage from ℱ_𝐌 to ℱ_ℂ — DNS.2 is
       derivable in ℱ_ℂ through R_arrow_core while Claim 1 holds of
       the formalized fragment. (Version 4 name kept.)

   (4) refutation_system_Ł_correct_for_ℱ_M: everything the
       refutation system rejects is underivable in ℱ_𝐌.

   (5) refutation_system_Ł_incorrect_for_ℱ_ℂ: the same refutation
       system rejects a sequent that ℱ_ℂ derives.

   (6) claim1_false: the conditional collision — Tennant's Claim 1
       (restricted to distinct atoms) and the kernel's refutation
       rule stated for ℂ (anti_DNS1_rule_for_ℂ, named
       conservativity_at_DNS1 in Version 4) jointly entail False.

   (7) claim1_false_at_0_1: the closed instance at atoms 0 and 1.

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

/- ════════════════════════════════════════════════════════════════
   The refutation system

   Claim 1 as the only rejection axiom, the anti-DNS.1 instance as
   the only refutation rule. Its correctness discipline follows
   Goranko's Theorem 2.1: a refutation rule is licensed by the
   correctness of its converse, certified in statement (1).
   ════════════════════════════════════════════════════════════════ -/

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

theorem DNS1_invertible_at_decisive_instance_in_ℱ_M
    (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) := sorry

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
