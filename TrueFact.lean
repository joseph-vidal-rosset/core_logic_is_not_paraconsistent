/-
  Independent re-certification of the decisive instance:
  the sequent (a→b)→b, ¬a ⊢ b is derivable in ℱ_ℂ through R→ℂ alone.
  `true_fact` is, word for word, the conclusion of `DNS2_instantiated`
  in core_logic_is_not_paraconsistent.lean (Version 6).

  Author: an anonymous correspondent (blog comment, July 2026).
  Published here with the moderator's thanks; content unchanged.
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

theorem true_fact (a b : Nat) : Derivable core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)] (some (Var b)) :=
    Derivable.L_arrow (A := Impl (Var a) (Var b)) (B := Var b)
      List.mem_cons_self
      (Derivable.R_arrow_core
        (Derivable.L_neg (A := Var a)
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (Derivable.Ax List.mem_cons_self)))
      (Derivable.Ax List.mem_cons_self)

#print axioms true_fact
