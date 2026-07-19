/-
  Solution to MinimalChallenge.lean: the collision in three lines.
  `true_fact` is the anonymous correspondent's proof term — word for
  word the conclusion of `DNS2_instantiated` in Version 6, i.e. the
  decisive instance (a→b)→b, ¬a ⊢ b, derivable in ℱ_ℂ through
  R→ℂ alone. Given Tennant's two commitments as hypotheses, False
  follows by two applications of modus ponens. The skeleton is thin
  by design: the content of the refutation lies in the twelve
  theorems of the full Challenge, which certify that the hypotheses
  are Core Logic's own commitments.
-/

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

/-- The anonymous correspondent's derivation of the decisive
    instance in ℱ_ℂ, through R→ℂ alone. -/
theorem true_fact (a b : Nat) :
    Derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) :=
  Derivable.L_arrow (A := Impl (Var a) (Var b)) (B := Var b)
    List.mem_cons_self
    (Derivable.R_arrow_core
      (Derivable.L_neg (A := Var a)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivable.Ax List.mem_cons_self)))
    (Derivable.Ax List.mem_cons_self)

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
      False :=
  fun a b hab =>
    anti_DNS1_rule_for_ℂ a b hab (Claim1_Tennant a b hab) (true_fact a b)

#print axioms claim1_false
