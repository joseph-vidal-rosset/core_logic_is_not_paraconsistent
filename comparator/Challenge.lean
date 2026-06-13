/- ════════════════════════════════════════════════════════════════
   CHALLENGE — Core Logic is not Paraconsistent
   ════════════════════════════════════════════════════════════════

   Trusted statement for the Lean Comparator.

   The challenge fixes: the language ℱ, the derivability predicate
   with its six rules (five shared between minimal logic 𝐌 and Core
   logic ℂ, plus the Core-specific R→ℂ), and the conditional theorem
   to be proved:

     IF  Tennant's Claim 1 holds in ℂ  (¬A, A ⊬ B)
     AND antisequent rules established on the fragment shared by
         𝐌 and ℂ transfer from 𝐌 to ℂ
     THEN False.

   The statement is a pure conditional: a passing solution proves it
   using no axiom beyond Lean's built-ins. The two hypotheses are
   part of the trusted statement below, in the signature of
   `claim1_false`.
   ════════════════════════════════════════════════════════════════ -/

inductive Formula : Type
  | Var  : Nat → Formula
  | Neg  : Formula → Formula
  | Impl : Formula → Formula → Formula
  deriving DecidableEq, Repr

open Formula

inductive FragmentF : Type
  | minimal_F  : FragmentF
  | core_logic : FragmentF
  deriving DecidableEq, Repr

open FragmentF

inductive Derivable : FragmentF → List Formula → Option Formula → Prop
  | Ax           : ∀ {f : FragmentF} {G : List Formula} {A : Formula},
                     A ∈ G →
                     Derivable f G (some A)
  | L_neg        : ∀ {f : FragmentF} {G : List Formula} {A : Formula},
                     Derivable f G (some A) →
                     Derivable f (Neg A :: G) none
  | R_arrow      : ∀ {f : FragmentF} {G : List Formula} {A B : Formula},
                     Derivable f (A :: G) (some B) →
                     Derivable f G (some (Impl A B))
  | L_arrow      : ∀ {f : FragmentF} {G : List Formula} {A B : Formula}
                     {C : Option Formula},
                     Derivable f G (some A) →
                     Derivable f (B :: G) C →
                     Derivable f (Impl A B :: G) C
  | Exchange     : ∀ {f : FragmentF} {x y : Formula} {C : Option Formula},
                     Derivable f [x, y] C →
                     Derivable f [y, x] C
  | R_arrow_core : ∀ {G : List Formula} {A B : Formula},
                     Derivable core_logic (A :: G) none →
                     Derivable core_logic G (some (Impl A B))

/- The statement to prove: Tennant's two commitments, taken as
   hypotheses, jointly entail absurdity. -/

theorem claim1_false
    (Claim1_Tennant :
      ∀ (a b : Nat),
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False)
    (min_antisequent_rule_to_core :
      ∀ (G G' : List Formula) (C C' : Option Formula),
        ((Derivable minimal_F G C → False) →
         (Derivable minimal_F G' C' → False)) →
        ((Derivable core_logic G C → False) →
         (Derivable core_logic G' C' → False))) :
    ∀ (a b : Nat), False := sorry
