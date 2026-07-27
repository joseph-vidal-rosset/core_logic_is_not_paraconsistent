/-!
# Challenge — ℱ, multiplicative presentation with set-like contexts

The vocabulary, then the fifteen statements, each left as `sorry`.
A candidate solution must re-declare this vocabulary verbatim and
prove theorems of exactly these names and types.

No import: core Lean 4 only, no Mathlib, no Batteries.
-/

namespace F

inductive formula : Type
  | Var  : Nat → formula
  | Neg  : formula → formula
  | Impl : formula → formula → formula

inductive fragment_F : Type
  | minimal_F
  | core_logic

open formula fragment_F

inductive der : fragment_F → List formula → Option formula → Prop
  | Ax : ∀ f A,
      der f [A] (some A)
  | Set_eq : ∀ f G G' C,
      (∀ X, X ∈ G ↔ X ∈ G') →
      der f G C →
      der f G' C
  | L_neg : ∀ f G A,
      der f G (some A) →
      der f (Neg A :: G) none
  | R_arrow : ∀ f G A B,
      der f (A :: G) (some B) →
      der f G (some (Impl A B))
  | L_arrow : ∀ f G D A B C,
      der f G (some A) →
      der f (B :: D) C →
      der f (Impl A B :: G ++ D) C
  | R_arrow_core : ∀ G A B,
      der core_logic (A :: G) none →
      der core_logic G (some (Impl A B))

def inv_ctx (a b : Nat) (X : formula) : Prop :=
  X = Var a ∨ X = Neg (Var a) ∨ X = Impl (Impl (Var a) (Var b)) (Var b)

inductive refutable : List formula → Option formula → Prop
  | claim1_axiom : ∀ a b,
      a ≠ b →
      refutable [Var a, Neg (Var a)] (some (Var b))
  | anti_DNS1 : ∀ a b,
      refutable [Var a, Neg (Var a)] (some (Var b)) →
      refutable [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b))

/-! ## The twelve statements of the paper -/

theorem DNS1_in_ℱ (f : fragment_F) (a b : Nat) :
    der f [Var a, Neg (Var a)] (some (Var b)) →
    der f [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)] (some (Var b)) :=
  sorry

theorem DNS2_instantiated (a b : Nat) :
    der core_logic [Var a, Neg (Var a)] none →
    der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) :=
  sorry

theorem DNS1_invertible_at_decisive_instance_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    der minimal_F [Var a, Neg (Var a)] (some (Var b)) :=
  sorry

theorem claim1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Var a, Neg (Var a)] (some (Var b)) → False :=
  sorry

theorem DNS1_conclusion_underivable_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    False :=
  sorry

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (der minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) :=
  sorry

theorem refutation_system_Ł_correct_for_ℱ_M :
    ∀ G C, refutable G C → der minimal_F G C → False :=
  sorry

theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
    ∃ G C, refutable G C ∧ der core_logic G C :=
  sorry

theorem claim1_false
    (Claim1_Tennant : ∀ a b : Nat, a ≠ b →
      der core_logic [Var a, Neg (Var a)] (some (Var b)) → False)
    (anti_DNS1_rule_for_ℂ : ∀ a b : Nat, a ≠ b →
      (der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
      (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b)) → False)) :
    ∀ a b : Nat, a ≠ b → False :=
  sorry

theorem claim1_false_at_0_1
    (Claim1_Tennant : ∀ a b : Nat, a ≠ b →
      der core_logic [Var a, Neg (Var a)] (some (Var b)) → False)
    (anti_DNS1_rule_for_ℂ : ∀ a b : Nat, a ≠ b →
      (der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
      (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b)) → False)) :
    False :=
  sorry

theorem claim1_holds_in_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    der core_logic [Var a, Neg (Var a)] (some (Var b)) → False :=
  sorry

theorem anti_DNS1_Ł_incorrect_for_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    ¬ ((der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
       (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
         (some (Var b)) → False)) :=
  sorry

/-! ## The three additional checks -/

theorem absurdity_core (a : Nat) :
    der core_logic [Var a, Neg (Var a)] none :=
  sorry

theorem DNS1_inversion_lemma (a b : Nat) (hab : a ≠ b) :
    ∀ (f : fragment_F) (G : List formula) (C : Option formula), der f G C →
      f = minimal_F →
      (∀ X, X ∈ G → inv_ctx a b X) →
      C ≠ some (Var b) ∧ C ≠ some (Impl (Var a) (Var b)) :=
  sorry

theorem no_dilution : ¬ der minimal_F [Var 1, Var 2] (some (Var 1)) :=
  sorry

end F
