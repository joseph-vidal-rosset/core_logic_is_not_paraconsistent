/-!
════════════════════════════════════════════════════════════════
ℱ — MULTIPLICATIVE presentation with SET-LIKE contexts.

Complete reconstruction of the twelve statements of
`core_logic_is_not_paraconsistent.v` without any monotonicity.

Structural choices:
- Reflexivity at the singleton `[A] ⊢ A`: no diluted `Ax`.
- Left rules with split contexts: the principal formula is
  consumed, the contexts of the premisses being pieces of the
  context of the conclusion.
- Contexts = `List formula`, and SET-LIKE identity is stated by
  the rule `Set_eq`, a membership EQUIVALENCE (double
  implication) and not a monotonicity rule.  It makes Exchange
  and Contraction pointless, in accordance with Tennant's
  sequents, and yields no weakening whatsoever: see
  `no_dilution` at the end of the file.

No monotonicity lemma is declared or used.
No dependency beyond `List`: this is the transposition of the
Coq file, `In` having become `List.Mem`.
No import at all: core Lean 4 only, no Mathlib, no Batteries.
Lean 4.32.1
════════════════════════════════════════════════════════════════
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

/-! ══ Membership toolkit — the two facts about `List.Mem` used below ══ -/

/-- Membership in a two-element list, read off the constructors. -/
theorem mem_pair {Z X Y : formula} (h : Z ∈ [X, Y]) : Z = X ∨ Z = Y := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h =>
      cases h with
      | head => exact Or.inr rfl
      | tail _ h => cases h

/-- The left half of a split context is part of the whole. -/
theorem mem_app_left {X : formula} {G D : List formula} (h : X ∈ G) :
    X ∈ G ++ D := by
  induction G with
  | nil => cases h
  | cons _ _ ih =>
      cases h with
      | head => exact .head _
      | tail _ h => exact .tail _ (ih h)

/-- Exchange of two formulas: a consequence of `Set_eq` alone. -/
theorem set_eq_2 (f : fragment_F) (X Y : formula) (C : Option formula) :
    der f [X, Y] C → der f [Y, X] C := by
  intro h
  refine der.Set_eq f [X, Y] [Y, X] C ?_ h
  intro Z
  constructor
  · intro hz
    cases mem_pair hz with
    | inl e => exact e ▸ .tail _ (.head _)
    | inr e => exact e ▸ .head _
  · intro hz
    cases mem_pair hz with
    | inl e => exact e ▸ .tail _ (.head _)
    | inr e => exact e ▸ .head _

/-! ══ Block A — the two derivabilities ══════════════════════════════ -/

theorem absurdity_core (a : Nat) :
    der core_logic [Var a, Neg (Var a)] none := by
  apply set_eq_2
  exact der.L_neg core_logic [Var a] (Var a) (der.Ax core_logic (Var a))

/-- DNS.1, uniformly in the fragment indicator. -/
theorem DNS1_in_ℱ (f : fragment_F) (a b : Nat) :
    der f [Var a, Neg (Var a)] (some (Var b)) →
    der f [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)] (some (Var b)) :=
  fun h =>
    der.L_arrow f [Neg (Var a)] [] (Impl (Var a) (Var b)) (Var b) (some (Var b))
      (der.R_arrow f [Neg (Var a)] (Var a) (Var b) h)
      (der.Ax f (Var b))

/-- DNS.2, on the Core reading, by `R→ℂ`. -/
theorem DNS2_instantiated (a b : Nat) :
    der core_logic [Var a, Neg (Var a)] none →
    der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) :=
  fun hd =>
    der.L_arrow core_logic [Neg (Var a)] [] (Impl (Var a) (Var b)) (Var b)
      (some (Var b))
      (der.R_arrow_core [Neg (Var a)] (Var a) (Var b) hd)
      (der.Ax core_logic (Var b))

/-! ══ Block B — Claim 1, in BOTH fragments ══════════════════════════

No sequent whose context is included in {A, ¬A} concludes an atom
distinct from A — whether or not `R→ℂ` is available. -/

theorem claim1_general (a b : Nat) (hab : a ≠ b) :
    ∀ (f : fragment_F) (G : List formula) (C : Option formula), der f G C →
      (∀ X, X ∈ G → X = Var a ∨ X = Neg (Var a)) →
      C ≠ some (Var b) := by
  intro f G C hd
  induction hd with
  | Ax f A =>
      -- Ax
      intro hs
      cases hs A (.head _) with
      | inl e => subst e; intro hc; injection hc with hc; injection hc with hc
                 exact hab hc
      | inr e => subst e; intro hc; injection hc with hc; injection hc
  | Set_eq f G G' C hmem _ ih =>
      -- Set_eq
      intro hs
      exact ih (fun X hx => hs X ((hmem X).mp hx))
  | L_neg =>
      -- L¬
      intro _ hc; injection hc
  | R_arrow =>
      -- R→
      intro _ hc; injection hc with hc; injection hc
  | L_arrow f G D A B C _ _ _ _ =>
      -- L→: the principal formula is an implication, outside the invariant.
      intro hs
      cases hs (Impl A B) (.head _) with
      | inl e => injection e
      | inr e => injection e
  | R_arrow_core =>
      -- R→ℂ
      intro _ hc; injection hc with hc; injection hc

theorem ctx_prem (a : Nat) (X : formula) :
    X ∈ [Var a, Neg (Var a)] → X = Var a ∨ X = Neg (Var a) :=
  fun h => mem_pair h

theorem claim1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Var a, Neg (Var a)] (some (Var b)) → False :=
  fun hd => claim1_general a b hab _ _ _ hd (ctx_prem a) rfl

theorem claim1_holds_in_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    der core_logic [Var a, Neg (Var a)] (some (Var b)) → False :=
  fun hd => claim1_general a b hab _ _ _ hd (ctx_prem a) rfl

/-! ══ Block C — the inversion lemma, in ℱ_M ═════════════════════════ -/

def inv_ctx (a b : Nat) (X : formula) : Prop :=
  X = Var a ∨ X = Neg (Var a) ∨ X = Impl (Impl (Var a) (Var b)) (Var b)

theorem DNS1_inversion_lemma (a b : Nat) (hab : a ≠ b) :
    ∀ (f : fragment_F) (G : List formula) (C : Option formula), der f G C →
      f = minimal_F →
      (∀ X, X ∈ G → inv_ctx a b X) →
      C ≠ some (Var b) ∧ C ≠ some (Impl (Var a) (Var b)) := by
  intro f G C hd
  induction hd with
  | Ax f A =>
      -- Ax
      intro _ hs
      rcases hs A (.head _) with e | e | e <;> subst e
      · exact ⟨fun hc => by injection hc with hc; injection hc with hc; exact hab hc,
               fun hc => by injection hc with hc; injection hc⟩
      · exact ⟨fun hc => by injection hc with hc; injection hc,
               fun hc => by injection hc with hc; injection hc⟩
      · exact ⟨fun hc => by injection hc with hc; injection hc,
               fun hc => by injection hc with hc; injection hc with h1 _; injection h1⟩
  | Set_eq f G G' C hmem _ ih =>
      -- Set_eq
      intro hf hs
      exact ih hf (fun X hx => hs X ((hmem X).mp hx))
  | L_neg =>
      -- L¬
      intro _ _
      exact ⟨fun hc => by injection hc, fun hc => by injection hc⟩
  | R_arrow f G A B _ ih =>
      -- R→
      intro hf hs
      refine ⟨fun hc => by injection hc with hc; injection hc, ?_⟩
      intro hc
      injection hc with hc
      injection hc with hA hB
      subst hA; subst hB
      have hs' : ∀ X, X ∈ Var a :: G → inv_ctx a b X := by
        intro X hx
        cases hx with
        | head => exact Or.inl rfl
        | tail _ hx => exact hs X hx
      exact (ih hf hs').1 rfl
  | L_arrow f G D A B C _ _ ih1 _ =>
      -- L→: the principal formula is read off the conclusion; the
      -- invariant descends to the subcontext G.
      intro hf hs
      rcases hs (Impl A B) (.head _) with e | e | e
      · injection e
      · injection e
      · injection e with hA hB
        subst hA; subst hB
        have hsG : ∀ X, X ∈ G → inv_ctx a b X :=
          fun X hx => hs X (.tail _ (mem_app_left hx))
        exact absurd rfl (ih1 hf hsG).2
  | R_arrow_core =>
      -- R→ℂ does not belong to ℱ_M.
      intro hf _; injection hf

theorem ctx_concl (a b : Nat) (X : formula) :
    X ∈ [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)] → inv_ctx a b X := by
  intro h
  cases mem_pair h with
  | inl e => exact Or.inr (Or.inr e)
  | inr e => exact Or.inr (Or.inl e)

theorem DNS1_invertible_at_decisive_instance_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    der minimal_F [Var a, Neg (Var a)] (some (Var b)) :=
  fun hd =>
    absurd rfl (DNS1_inversion_lemma a b hab _ _ _ hd rfl (ctx_concl a b)).1

theorem DNS1_conclusion_underivable_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) →
    False :=
  fun hd => (DNS1_inversion_lemma a b hab _ _ _ hd rfl (ctx_concl a b)).1 rfl

/-! ══ Block D — anti-DNS.1 and the refutation system ════════════════ -/

theorem anti_DNS1_holds_in_ℱ_M (a b : Nat) (hab : a ≠ b) :
    (der minimal_F [Var a, Neg (Var a)] (some (Var b)) → False) →
    (der minimal_F [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
      (some (Var b)) → False) :=
  fun hprem hd =>
    hprem (DNS1_invertible_at_decisive_instance_in_ℱ_M a b hab hd)

inductive refutable : List formula → Option formula → Prop
  | claim1_axiom : ∀ a b,
      a ≠ b →
      refutable [Var a, Neg (Var a)] (some (Var b))
  | anti_DNS1 : ∀ a b,
      refutable [Var a, Neg (Var a)] (some (Var b)) →
      refutable [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b))

theorem refutation_system_Ł_correct_for_ℱ_M :
    ∀ G C, refutable G C → der minimal_F G C → False := by
  intro G C hr
  induction hr with
  | claim1_axiom a b hab => exact fun hd => claim1_holds_in_ℱ_M a b hab hd
  | anti_DNS1 a b hr' _ =>
      intro hd
      cases hr' with
      | claim1_axiom _ _ hab => exact DNS1_conclusion_underivable_in_ℱ_M a b hab hd

/-! ══ Block E — the contradiction ═══════════════════════════════════ -/

theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
    ∃ G C, refutable G C ∧ der core_logic G C :=
  ⟨[Impl (Impl (Var 0) (Var 1)) (Var 1), Neg (Var 0)], some (Var 1),
    refutable.anti_DNS1 0 1 (refutable.claim1_axiom 0 1 (by decide)),
    DNS2_instantiated 0 1 (absurdity_core 0)⟩

theorem claim1_false
    (Claim1_Tennant : ∀ a b : Nat, a ≠ b →
      der core_logic [Var a, Neg (Var a)] (some (Var b)) → False)
    (anti_DNS1_rule_for_ℂ : ∀ a b : Nat, a ≠ b →
      (der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
      (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b)) → False)) :
    ∀ a b : Nat, a ≠ b → False :=
  fun a b hab =>
    anti_DNS1_rule_for_ℂ a b hab (Claim1_Tennant a b hab)
      (DNS2_instantiated a b (absurdity_core a))

theorem claim1_false_at_0_1
    (Claim1_Tennant : ∀ a b : Nat, a ≠ b →
      der core_logic [Var a, Neg (Var a)] (some (Var b)) → False)
    (anti_DNS1_rule_for_ℂ : ∀ a b : Nat, a ≠ b →
      (der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
      (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
        (some (Var b)) → False)) :
    False :=
  claim1_false Claim1_Tennant anti_DNS1_rule_for_ℂ 0 1 (by decide)

/-! ══ Block F — status of the second commitment ═════════════════════ -/

theorem anti_DNS1_Ł_incorrect_for_ℱ_ℂ (a b : Nat) (hab : a ≠ b) :
    ¬ ((der core_logic [Var a, Neg (Var a)] (some (Var b)) → False) →
       (der core_logic [Impl (Impl (Var a) (Var b)) (Var b), Neg (Var a)]
         (some (Var b)) → False)) :=
  fun h =>
    h (claim1_holds_in_ℱ_ℂ a b hab) (DNS2_instantiated a b (absurdity_core a))

/-! ══ Structural check — this system does not dilute ════════════════

Certified atomic relevance: if the whole context is atomic and the
conclusion is atomic, then the whole context IS the conclusion.  No
weakening is therefore available. -/

theorem atomic_relevance :
    ∀ (f : fragment_F) (G : List formula) (C : Option formula), der f G C →
      ∀ n, C = some (Var n) →
      (∀ X, X ∈ G → ∃ m, X = Var m) →
      ∀ X, X ∈ G → X = Var n := by
  intro f G C hd
  induction hd with
  | Ax f A =>
      -- Ax
      intro n hc _ X hx
      injection hc with hc; subst hc
      cases hx with
      | head => rfl
      | tail _ hx => cases hx
  | Set_eq f G G' C hmem _ ih =>
      -- Set_eq
      intro n hc hat X hx
      exact ih n hc (fun Y hy => hat Y ((hmem Y).mp hy)) X ((hmem X).mpr hx)
  | L_neg => intro _ hc; injection hc
  | R_arrow => intro _ hc; injection hc with hc; injection hc
  | L_arrow f G D A B C _ _ _ _ =>
      -- L→: the principal formula is not atomic.
      intro _ _ hat _ _
      have ⟨_, e⟩ := hat (Impl A B) (.head _)
      injection e
  | R_arrow_core => intro _ hc; injection hc with hc; injection hc

theorem no_dilution : ¬ der minimal_F [Var 1, Var 2] (some (Var 1)) := by
  intro h
  have e : Var 2 = Var 1 := by
    refine atomic_relevance _ _ _ h 1 rfl ?_ (Var 2) (.tail _ (.head _))
    intro X hx
    cases mem_pair hx with
    | inl e => exact ⟨1, e⟩
    | inr e => exact ⟨2, e⟩
  injection e with e
  exact absurd e (by decide)

end F
