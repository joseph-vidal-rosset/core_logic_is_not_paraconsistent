/- ════════════════════════════════════════════════════════════════
   Core Logic: shared-kernel DNS.1 inversion and conditional result
   ════════════════════════════════════════════════════════════════

   Version 3 distinguishes explicitly:

     (i)  F*  : the focused shared kernel of Minimal and Core;
     (ii) M   : the corrected membership-based minimal reading;
     (iii) C  : the corrected membership-based Core reading,
                obtained from the shared rules plus R_arrow_core.

   In F*, DNS.1 is derivable and invertible. Its contraposition
   yields the corresponding anti-DNS.1 rule in F*.

   Full Core proves DNS.2 by R_arrow_core. Consequently, the final
   collision requires one narrowly stated interpretive commitment:
   that Tennant's account of the shared kernel commits Core to the
   particular Core-level anti-DNS.1 instance at issue.

   There is no primitive Exchange rule and no universal transfer
   principle for arbitrary antisequent rules.
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
   F*: focused shared kernel

   This calculus has exactly the rules shared by M and Core, but no
   R_arrow_core. Its L_arrow rule is written in focused form, with
   the principal implication at the head of the context.

   This is not an Exchange rule: no permutation constructor is
   postulated. It is a focused presentation used to state and prove
   DNS.1 inversion directly.

   The embedding [star_to_minimal] proves that every F* derivation is
   also derivable in the corrected membership-based minimal calculus.
   ════════════════════════════════════════════════════════════════ -/

inductive DerivableStar : List Formula → Option Formula → Prop
  | Ax_star :
      ∀ {G : List Formula} {A : Formula},
        A ∈ G →
        DerivableStar G (some A)

  | L_neg_star :
      ∀ {G : List Formula} {A : Formula},
        Neg A ∈ G →
        DerivableStar G (some A) →
        DerivableStar G none

  | R_arrow_star :
      ∀ {G : List Formula} {A B : Formula},
        DerivableStar (A :: G) (some B) →
        DerivableStar G (some (Impl A B))

  | L_arrow_star :
      ∀ {G : List Formula} {A B : Formula} {C : Option Formula},
        DerivableStar G (some A) →
        DerivableStar (B :: G) C →
        DerivableStar (Impl A B :: G) C

/- Every F* derivation is derivable in the corrected membership-based
   minimal calculus. The focused premises are lifted by weakening to
   the larger contexts required by full L_arrow. -/

theorem star_to_minimal {G : List Formula} {C : Option Formula} :
    DerivableStar G C →
    Derivable minimal_F G C := by
  intro h
  induction h with
  | Ax_star hmem =>
      exact Derivable.Ax hmem

  | L_neg_star hneg _ ih =>
      exact Derivable.L_neg hneg ih

  | R_arrow_star _ ih =>
      exact Derivable.R_arrow ih

  | @L_arrow_star G A B C _ _ ih1 ih2 =>
      refine @Derivable.L_arrow minimal_F (Impl A B :: G) A B C ?_ ?_ ?_

      · simp

      · /- Lift G ⊢ A to (A → B), G ⊢ A. -/
        apply weakening_subset ih1
        intro X hX
        exact List.mem_cons.mpr (Or.inr hX)

      · /- Lift B, G ⊢ C to B, (A → B), G ⊢ C. -/
        apply weakening_subset ih2
        intro X hX
        rcases List.mem_cons.mp hX with hXB | hXG
        · exact List.mem_cons.mpr (Or.inl hXB)
        · exact
            List.mem_cons.mpr
              (Or.inr
                (List.mem_cons.mpr
                  (Or.inr hXG)))

/- Consequently, F* is also contained in Core. -/

theorem star_to_core {G : List Formula} {C : Option Formula} :
    DerivableStar G C →
    Derivable core_logic G C := by
  intro h
  exact MinToCore (star_to_minimal h)

/- ════════════════════════════════════════════════════════════════
   DNS.1 inside F*
   ════════════════════════════════════════════════════════════════ -/

theorem DNS1_star_instantiated (a b : Nat) :
    DerivableStar [Var a, Neg (Var a)] (some (Var b)) →
    DerivableStar
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  apply DerivableStar.L_arrow_star
  · apply DerivableStar.R_arrow_star
    exact h
  · exact DerivableStar.Ax_star (by simp)

/- The same F* DNS.1 derivation is therefore available in both M and
   Core, since F* embeds into both readings. -/

theorem DNS1_star_in_minimal (a b : Nat) :
    DerivableStar [Var a, Neg (Var a)] (some (Var b)) →
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  apply star_to_minimal
  exact DNS1_star_instantiated a b h

theorem DNS1_star_in_core (a b : Nat) :
    DerivableStar [Var a, Neg (Var a)] (some (Var b)) →
    Derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) := by
  intro h
  apply star_to_core
  exact DNS1_star_instantiated a b h

/- ════════════════════════════════════════════════════════════════
   Invertibility of DNS.1 inside F*
   ════════════════════════════════════════════════════════════════ -/

/- Since F* has no R_arrow_core constructor, an implication derivable
   from [¬A] can only arise here through ordinary R_arrow_star. -/

theorem R_arrow_inv_NegA_star (a b : Nat) :
    DerivableStar [Neg (Var a)] (some (Impl (Var a) (Var b))) →
    DerivableStar [Var a, Neg (Var a)] (some (Var b)) := by
  intro h
  cases h with
  | Ax_star hmem =>
      simp at hmem
  | R_arrow_star hpremiss =>
      exact hpremiss

/- Invert the relevant F* instance of DNS.1. The index of the context
   forces the final applicable constructor to be L_arrow_star, whose
   left premise is [¬A] ⊢ A → B. -/

theorem DNS1_inv_star_instantiated (a b : Nat) :
    DerivableStar
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    DerivableStar [Var a, Neg (Var a)] (some (Var b)) := by
  intro h
  cases h with
  | Ax_star hmem =>
      simp at hmem
  | L_arrow_star hleft _ =>
      exact R_arrow_inv_NegA_star a b hleft

/- Contraposition of F*-DNS.1 inversion: anti-DNS.1 is a derived rule
   of the shared kernel F*. -/

theorem DNS1_anti_star_instantiated (a b : Nat) :
    (DerivableStar [Var a, Neg (Var a)] (some (Var b)) → False) →
    (DerivableStar
       [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
       (some (Var b)) →
     False) := by
  intro hPremiss hConclusion
  exact hPremiss (DNS1_inv_star_instantiated a b hConclusion)

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

   DNS1_anti_star_instantiated proves anti-DNS.1 in F*.

   The following narrowly scoped hypothesis is not a universal
   antisequent-transfer axiom. It states only the disputed
   preservation/commitment needed for this atom-instance when one
   passes from the F* anti-rule to full Core antisequents.

   This is the precise dialectical issue:
   - syntactically, F* proves the anti-rule;
   - textually/philosophically, one argues that Tennant's account of
     the shared kernel commits Core to this instance;
   - Core's R_arrow_core proves DNS.2, producing the collision with
     Claim 1.
   ════════════════════════════════════════════════════════════════ -/

theorem claim1_false
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (anti_DNS1_shared :
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
    anti_DNS1_shared a b hab
      (Claim1_Tennant a b hab)
      (DNS2_instantiated a b (absurdity_core a))

/- Closed instance at the concrete distinct atoms 0 and 1. -/

theorem claim1_false_at_0_1
    (Claim1_Tennant :
      ∀ a b : Nat,
        a ≠ b →
        Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
        False)
    (anti_DNS1_shared :
      ∀ a b : Nat,
        a ≠ b →
        (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) →
          False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) →
          False)) :
    False := by
  exact claim1_false Claim1_Tennant anti_DNS1_shared 0 1 (by decide)

/- Audit: no sorryAx should occur; Lean may report only [propext]. -/

#print axioms DNS1_anti_star_instantiated
#print axioms claim1_false
#print axioms claim1_false_at_0_1
/- ════════════════════════════════════════════════════════════════
   Metatheoretic supplement
   ════════════════════════════════════════════════════════════════

   The embedding star_to_minimal proves F* ⊆ M only. Since
   underivability travels downwards along an inclusion, the
   anti-DNS.1 rule proved inside F* does not by itself yield the
   corresponding rule for M. The following invariant closes this
   adequacy gap: it establishes the underivability facts directly in
   the membership-based minimal reading M, covering in particular the
   case that F* excludes by construction, namely L_arrow firing on
   (A → B) → B with the principal implication kept in the context.

   Invariant: for distinct atoms a and b, no context included in
   {Var a, ¬Var a, (Var a → Var b) → Var b} derives Var b or
   Var a → Var b in M.
   ════════════════════════════════════════════════════════════════ -/

theorem M_blocked (a b : Nat) (hab : a ≠ b) :
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
         contradicting the induction hypothesis. This is exactly the
         case excluded in F* by consuming the principal formula. -/
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

/- Consequence 1: in M itself, both the premiss and the conclusion of
   the DNS.1 instance are underivable, unconditionally. -/

theorem claim1_holds_in_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False := by
  intro h
  refine (M_blocked a b hab h rfl ?_).1 rfl
  intro X hX
  rcases List.mem_cons.mp hX with hX | hX
  · exact Or.inl hX
  · rcases List.mem_cons.mp hX with hX | hX
    · exact Or.inr (Or.inl hX)
    · cases hX

theorem DNS1_conclusion_underivable_in_M (a b : Nat) (hab : a ≠ b) :
    Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False := by
  intro h
  refine (M_blocked a b hab h rfl ?_).1 rfl
  intro X hX
  rcases List.mem_cons.mp hX with hX | hX
  · exact Or.inr (Or.inr hX)
  · rcases List.mem_cons.mp hX with hX | hX
    · exact Or.inr (Or.inl hX)
    · cases hX

/- Hence the anti-DNS.1 instance is a metatheorem of M itself, with
   no detour through F*. The adequacy gap left by the one-directional
   embedding star_to_minimal is thereby closed for this instance. -/

theorem anti_DNS1_holds_in_M (a b : Nat) (hab : a ≠ b) :
    (Derivable minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (Derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) :=
  fun _ => DNS1_conclusion_underivable_in_M a b hab

/- Consequence 2, for full Core C. First, Claim 1 holds of the
   formalized fragment: no rule can conclude
   [Var a, ¬Var a] ⊢ Var b when a ≠ b, since Ax requires Var b in
   the context, L_arrow requires an implication in the context, L_neg
   concludes on the empty succedent, and both right rules conclude on
   an implicational succedent. -/

theorem claim1_holds_in_C (a b : Nat) (hab : a ≠ b) :
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

/- Second, C refutes the transfer of the anti-DNS.1 instance from M
   to C: since DNS.2 is derivable in C through R_arrow_core while
   Claim 1 holds of the fragment, the Core-level anti-DNS.1 instance
   is false of the formalized calculus. The hypothesis
   anti_DNS1_shared of the final theorem is therefore exactly the
   disputed M-to-C antisequent transfer for this instance: the
   formalization displays it, and only Tennant's own account of the
   shared kernel can ground it. -/

theorem anti_DNS1_refuted_in_C (a b : Nat) (hab : a ≠ b) :
    ¬ ( (Derivable core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
        (Derivable core_logic
          [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
          (some (Var b)) → False) ) := by
  intro h
  exact h (claim1_holds_in_C a b hab)
          (DNS2_instantiated a b (absurdity_core a))

#print axioms anti_DNS1_holds_in_M
#print axioms anti_DNS1_refuted_in_C
