(** ════════════════════════════════════════════════════════════════
    ℱ — MULTIPLICATIVE presentation with SET-LIKE contexts.
    Complete reconstruction of the twelve statements of
    core_logic_is_not_paraconsistent.v without any monotonicity.

    Structural choices:
    - Reflexivity at the singleton [A] ⊢ A: no diluted Ax.
    - Left rules with split contexts: the principal formula is
      consumed, the contexts of the premisses being pieces of
      the context of the conclusion.
    - Contexts = [list formula], and SET-LIKE identity is stated
      by the rule [Set_eq], a membership EQUIVALENCE (double
      implication) and not a monotonicity rule. It makes Exchange
      and Contraction pointless, in accordance with Tennant's
      sequents, and yields no weakening whatsoever: see
      [no_dilution] at the end of the file.

    No monotonicity lemma is declared or used.
    No occurrence of [exfalso].
    No dependency beyond [List]: the file transposes directly to
    Lean 4, [In] becoming [List.Mem].
    Coq 8.18.0
    ════════════════════════════════════════════════════════════════ *)

From Coq Require Import List.
Import ListNotations.

Inductive formula : Type :=
| Var : nat -> formula
| Neg : formula -> formula
| Impl : formula -> formula -> formula.

Inductive fragment_F : Type := minimal_F | core_logic.

Inductive der : fragment_F -> list formula -> option formula -> Prop :=

| Ax : forall f A,
    der f [A] (Some A)

| Set_eq : forall f G G' C,
    (forall X, In X G <-> In X G') ->
    der f G C ->
    der f G' C

| L_neg : forall f G A,
    der f G (Some A) ->
    der f (Neg A :: G) None

| R_arrow : forall f G A B,
    der f (A :: G) (Some B) ->
    der f G (Some (Impl A B))

| L_arrow : forall f G D A B C,
    der f G (Some A) ->
    der f (B :: D) C ->
    der f (Impl A B :: G ++ D) C

| R_arrow_core : forall G A B,
    der core_logic (A :: G) None ->
    der core_logic G (Some (Impl A B)).

(* Exchange of two formulas: a consequence of [Set_eq] alone. *)

Lemma set_eq_2 :
  forall f X Y C, der f [X; Y] C -> der f [Y; X] C.
Proof.
  intros f X Y C H.
  apply Set_eq with (G := [X; Y]); [ | exact H ].
  intro Z; simpl; tauto.
Qed.

(* ══ Block A — the two derivabilities ═════════════════════════════ *)

Lemma absurdity_core :
  forall a : nat,
    der core_logic [Var a; Neg (Var a)] None.
Proof.
  intro a. apply set_eq_2.
  apply L_neg with (A := Var a). apply Ax.
Qed.

(* DNS.1, uniformly in the fragment indicator. *)

Theorem DNS1_in_ℱ :
  forall (f : fragment_F) (a b : nat),
    der f [Var a; Neg (Var a)] (Some (Var b)) ->
    der f [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
         (Some (Var b)).
Proof.
  intros f a b H.
  apply L_arrow with (A := Impl (Var a) (Var b)) (B := Var b)
                     (G := [Neg (Var a)]) (D := @nil formula).
  - apply R_arrow. exact H.
  - apply Ax.
Qed.

(* DNS.2, on the Core reading, by R→ℂ. *)

Theorem DNS2_instantiated :
  forall a b : nat,
    der core_logic [Var a; Neg (Var a)] None ->
    der core_logic
        [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
        (Some (Var b)).
Proof.
  intros a b HD.
  apply L_arrow with (A := Impl (Var a) (Var b)) (B := Var b)
                     (G := [Neg (Var a)]) (D := @nil formula).
  - apply R_arrow_core. exact HD.
  - apply Ax.
Qed.

(* ══ Block B — Claim 1, in BOTH fragments ═════════════════════════ *)

(* No sequent whose context is included in {A, ¬A} concludes an atom
   distinct from A — whether or not R→ℂ is available. *)

Lemma claim1_general :
  forall a b : nat,
    a <> b ->
    forall f G C,
      der f G C ->
      (forall X, In X G -> X = Var a \/ X = Neg (Var a)) ->
      C <> Some (Var b).
Proof.
  intros a b Hab f G C HD.
  induction HD; intro HS.

  - (* Ax *)
    destruct (HS A (or_introl eq_refl)) as [E | E]; subst A;
      intro HC; congruence.

  - (* Set_eq *)
    apply IHHD. intros X HX. apply HS. apply H. exact HX.

  - (* L¬ *)
    intro HC; discriminate.

  - (* R→ *)
    intro HC; discriminate.

  - (* L→ : the principal formula is an implication, outside the
       invariant. *)
    destruct (HS (Impl A B) (or_introl eq_refl)) as [E | E]; discriminate E.

  - (* R→ℂ *)
    intro HC; discriminate.
Qed.

Lemma ctx_prem :
  forall a X, In X [Var a; Neg (Var a)] ->
              X = Var a \/ X = Neg (Var a).
Proof. intros a X [E | [E | []]]; subst X; auto. Qed.

Theorem claim1_holds_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    der minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  exact (claim1_general a b Hab _ _ _ HD (ctx_prem a) eq_refl).
Qed.

Theorem claim1_holds_in_ℱ_ℂ :
  forall a b : nat,
    a <> b ->
    der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  exact (claim1_general a b Hab _ _ _ HD (ctx_prem a) eq_refl).
Qed.

(* ══ Block C — the inversion lemma, in ℱ_𝐌 ════════════════════════ *)

Definition inv_ctx (a b : nat) (X : formula) : Prop :=
  X = Var a \/ X = Neg (Var a) \/
  X = Impl (Impl (Var a) (Var b)) (Var b).

Lemma DNS1_inversion_lemma :
  forall a b : nat,
    a <> b ->
    forall f G C,
      der f G C ->
      f = minimal_F ->
      (forall X, In X G -> inv_ctx a b X) ->
      C <> Some (Var b) /\ C <> Some (Impl (Var a) (Var b)).
Proof.
  intros a b Hab f G C HD.
  induction HD; intros Hf HS.

  - (* Ax *)
    destruct (HS A (or_introl eq_refl)) as [E | [E | E]]; subst A;
      split; intro HC; congruence.

  - (* Set_eq *)
    apply IHHD; [ exact Hf | ].
    intros X HX. apply HS. apply H. exact HX.

  - (* L¬ *)
    split; intro HC; discriminate.

  - (* R→ *)
    split; intro HC.
    + discriminate.
    + injection HC as HA HB. subst A B.
      assert (HS' : forall X, In X (Var a :: G) -> inv_ctx a b X).
      { intros X [HX | HX].
        - left. symmetry. exact HX.
        - apply HS. exact HX. }
      destruct (IHHD Hf HS') as [Hcontr _].
      apply Hcontr. reflexivity.

  - (* L→ : the principal formula is read off the conclusion; the
       invariant descends to the subcontext G. *)
    destruct (HS (Impl A B) (or_introl eq_refl)) as [E | [E | E]];
      try discriminate.
    injection E as HA HB. subst A B.
    assert (HSG : forall X, In X G -> inv_ctx a b X).
    { intros X HX. apply HS. right. apply in_or_app. left. exact HX. }
    destruct (proj2 (IHHD1 Hf HSG) eq_refl).

  - (* R→ℂ does not belong to ℱ_𝐌. *)
    discriminate Hf.
Qed.

Lemma ctx_concl :
  forall a b X,
    In X [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)] ->
    inv_ctx a b X.
Proof.
  intros a b X [E | [E | []]]; subst X.
  - right. right. reflexivity.
  - right. left. reflexivity.
Qed.

Theorem DNS1_invertible_at_decisive_instance_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    der minimal_F
        [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
        (Some (Var b)) ->
    der minimal_F [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b Hab HD.
  destruct (proj1 (DNS1_inversion_lemma a b Hab _ _ _ HD eq_refl
                     (ctx_concl a b)) eq_refl).
Qed.

Theorem DNS1_conclusion_underivable_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    der minimal_F
        [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
        (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  exact (proj1 (DNS1_inversion_lemma a b Hab _ _ _ HD eq_refl
                  (ctx_concl a b)) eq_refl).
Qed.

(* ══ Block D — anti-DNS.1 and the refutation system ═══════════════ *)

Theorem anti_DNS1_holds_in_ℱ_M :
  forall a b : nat,
    a <> b ->
    (der minimal_F [Var a; Neg (Var a)] (Some (Var b)) -> False) ->
    (der minimal_F
         [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
         (Some (Var b)) -> False).
Proof.
  intros a b Hab Hprem HD.
  apply Hprem.
  apply (DNS1_invertible_at_decisive_instance_in_ℱ_M a b Hab).
  exact HD.
Qed.

Inductive refutable : list formula -> option formula -> Prop :=

| claim1_axiom :
    forall a b,
      a <> b ->
      refutable [Var a; Neg (Var a)] (Some (Var b))

| anti_DNS1 :
    forall a b,
      refutable [Var a; Neg (Var a)] (Some (Var b)) ->
      refutable
        [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
        (Some (Var b)).

Theorem refutation_system_Ł_correct_for_ℱ_M :
  forall G C,
    refutable G C ->
    der minimal_F G C ->
    False.
Proof.
  intros G C HR.
  induction HR; intro HD.
  - exact (claim1_holds_in_ℱ_M a b H HD).
  - inversion HR; subst;
      match goal with
      | Hab : a <> b |- _ =>
          exact (DNS1_conclusion_underivable_in_ℱ_M a b Hab HD)
      end.
Qed.

(* ══ Block E — the contradiction ══════════════════════════════════ *)

Theorem refutation_system_Ł_incorrect_for_ℱ_ℂ :
  exists G C,
    refutable G C /\ der core_logic G C.
Proof.
  exists [Impl (Impl (Var 0) (Var 1)) (Var 1); Neg (Var 0)].
  exists (Some (Var 1)).
  split.
  - apply anti_DNS1. apply claim1_axiom. discriminate.
  - apply DNS2_instantiated. apply absurdity_core.
Qed.

Theorem claim1_false :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_rule_for_ℂ :
      forall a b : nat,
        a <> b ->
        (der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (der core_logic
             [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
             (Some (Var b)) ->
         False)),

    forall a b : nat,
      a <> b ->
      False.
Proof.
  intros Claim1_Tennant anti_DNS1_rule_for_ℂ a b Hab.
  apply (anti_DNS1_rule_for_ℂ a b Hab).
  - apply (Claim1_Tennant a b Hab).
  - apply DNS2_instantiated. apply absurdity_core.
Qed.

Corollary claim1_false_at_0_1 :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_rule_for_ℂ :
      forall a b : nat,
        a <> b ->
        (der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (der core_logic
             [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
             (Some (Var b)) ->
         False)),

    False.
Proof.
  intros Claim1_Tennant anti_DNS1_rule_for_ℂ.
  apply (claim1_false Claim1_Tennant anti_DNS1_rule_for_ℂ 0 1).
  discriminate.
Qed.

(* ══ Block F — status of the second commitment ════════════════════ *)

Theorem anti_DNS1_Ł_incorrect_for_ℱ_ℂ :
  forall a b : nat,
    a <> b ->
    ~ ( (der core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (der core_logic
             [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
             (Some (Var b)) ->
         False) ).
Proof.
  intros a b Hab H.
  apply (H (claim1_holds_in_ℱ_ℂ a b Hab)).
  apply DNS2_instantiated. apply absurdity_core.
Qed.

(* ══ Structural check — this system does not dilute ═══════════════ *)

(* Certified atomic relevance: if the whole context is atomic and the
   conclusion is atomic, then the whole context IS the conclusion.
   No weakening is therefore available. *)

Lemma atomic_relevance :
  forall f G C,
    der f G C ->
    forall n, C = Some (Var n) ->
              (forall X, In X G -> exists m, X = Var m) ->
              forall X, In X G -> X = Var n.
Proof.
  intros f G C HD. induction HD; intros n HC Hat X HX.

  - (* Ax *)
    injection HC as E. subst A.
    destruct HX as [E' | []]. symmetry. exact E'.

  - (* Set_eq *)
    apply (IHHD n HC).
    + intros Y HY. apply Hat. apply H. exact HY.
    + apply H. exact HX.

  - (* L¬ *) discriminate.
  - (* R→ *) discriminate.

  - (* L→ : the principal formula is not atomic. *)
    destruct (Hat (Impl A B) (or_introl eq_refl)) as [m E]. discriminate E.

  - (* R→ℂ *) discriminate.
Qed.

Theorem no_dilution :
  ~ der minimal_F [Var 1; Var 2] (Some (Var 1)).
Proof.
  intro H.
  assert (E : Var 2 = Var 1).
  { apply (atomic_relevance _ _ _ H 1 eq_refl).
    - intros X [E | [E | []]]; subst X; eauto.
    - right. left. reflexivity. }
  discriminate.
Qed.

(* ══ Verification — the twelve statements ═════════════════════════ *)

Print Assumptions DNS1_in_ℱ.
Print Assumptions DNS2_instantiated.
Print Assumptions DNS1_invertible_at_decisive_instance_in_ℱ_M.
Print Assumptions claim1_holds_in_ℱ_M.
Print Assumptions DNS1_conclusion_underivable_in_ℱ_M.
Print Assumptions anti_DNS1_holds_in_ℱ_M.
Print Assumptions refutation_system_Ł_correct_for_ℱ_M.
Print Assumptions refutation_system_Ł_incorrect_for_ℱ_ℂ.
Print Assumptions claim1_false.
Print Assumptions claim1_false_at_0_1.
Print Assumptions claim1_holds_in_ℱ_ℂ.
Print Assumptions anti_DNS1_Ł_incorrect_for_ℱ_ℂ.

(* Additional checks *)
Print Assumptions absurdity_core.
Print Assumptions DNS1_inversion_lemma.
Print Assumptions no_dilution.
