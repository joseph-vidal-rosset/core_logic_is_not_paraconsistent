(** ════════════════════════════════════════════════════════════════
    ADDENDUM to core_logic_F_multiplicative.v — self-contained.

    The multiplicative presentation is a STRICT subsystem of ℱ_ℂ:
    the sequent A ⊢ B → A, a theorem of 𝐌 and of ℂ (Tennant 2017,
    p. 35), is underivable in it whenever A and B are distinct
    atoms. With the axiom no longer diluted, the discharge in R→
    is obligatory, and no other route is open.

    The side condition is not decorative: the diagonal instance
    A ⊢ A → A IS derivable, contraction remaining available since
    contexts are sets. It is derived at the end of the file.

    Sections 1 and 2 repeat, verbatim, the definitions and the
    lemma [atomic_relevance] of core_logic_F_multiplicative.v,
    so that this file stands alone.
    Coq 8.18.0 — no axiom, no [exfalso], no dependency beyond [List].
    ════════════════════════════════════════════════════════════════ *)

(* ══ 1. The fragment ℱ, multiplicative reading ════════════════════ *)

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

(* ══ 2. Atomic relevance (verbatim from the certified file) ══════ *)

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

(* ══ 3. No refutation from an atomic context ═════════════════════ *)

(* Only [L¬] concludes [None], and it requires a negated head: only [L¬] concludes [None],
   and it requires a negated head. *)

Lemma atomic_no_refutation :
  forall f G C,
    der f G C ->
    C = None ->
    (forall X, In X G -> exists m, X = Var m) ->
    False.
Proof.
  intros f G C HD. induction HD; intros HC Hat.
  - (* Ax *) discriminate.
  - (* Set_eq *)
    apply (IHHD HC). intros Y HY. apply Hat. apply H. exact HY.
  - (* L¬ *)
    destruct (Hat (Neg A) (or_introl eq_refl)) as [m E]. discriminate E.
  - (* R→ *) discriminate.
  - (* L→ *)
    destruct (Hat (Impl A B) (or_introl eq_refl)) as [m E]. discriminate E.
  - (* R→ℂ *) discriminate.
Qed.

(* ══ 4. The strictness theorem ══════════════════════════════════ *)

(* From an atomic context, an implication between atoms is derivable
   only when the two atoms coincide. *)

Lemma atomic_ctx_arrow :
  forall f G C,
    der f G C ->
    (forall X, In X G -> exists m, X = Var m) ->
    forall b c, C = Some (Impl (Var b) (Var c)) -> b = c.
Proof.
  intros f G C HD. induction HD; intros Hat b c HC.

  - (* Ax: the context would have to hold the implication itself. *)
    injection HC as E. subst A.
    destruct (Hat _ (or_introl eq_refl)) as [m E]. discriminate E.

  - (* Set_eq *)
    apply (IHHD (fun Y HY => Hat Y (proj1 (H Y) HY)) b c HC).

  - (* L¬ *) discriminate.

  - (* R→: the discharge is obligatory, so [atomic_relevance] applies
       to the premiss and forces the two atoms to coincide. *)
    injection HC as EA EB. subst A B.
    assert (Hat' : forall X, In X (Var b :: G) -> exists m, X = Var m).
    { intros X [E' | HX].
      - subst X. exists b. reflexivity.
      - apply Hat. exact HX. }
    assert (E2 : Var b = Var c).
    { apply (atomic_relevance _ _ _ HD c eq_refl Hat'). left. reflexivity. }
    injection E2 as E3. exact E3.

  - (* L→ *)
    destruct (Hat (Impl A B) (or_introl eq_refl)) as [m E]. discriminate E.

  - (* R→ℂ: the remaining route, closed by [atomic_no_refutation]. *)
    injection HC as EA EB. subst A.
    assert (Hat' : forall X, In X (Var b :: G) -> exists m, X = Var m).
    { intros X [E' | HX].
      - subst X. exists b. reflexivity.
      - apply Hat. exact HX. }
    destruct (atomic_no_refutation _ _ _ HD eq_refl Hat').
Qed.

(* The sequent A ⊢ B → A, a theorem of 𝐌 and of ℂ, is underivable
   here — in either fragment. The lower bound is therefore strict. *)

Theorem K_underivable :
  forall f a b, a <> b -> ~ der f [Var a] (Some (Impl (Var b) (Var a))).
Proof.
  intros f a b Hab H.
  apply Hab. symmetry.
  apply (atomic_ctx_arrow _ _ _ H) with (b := b) (c := a).
  - intros X [E | []]. subst X. exists a. reflexivity.
  - reflexivity.
Qed.

Print Assumptions atomic_no_refutation.
Print Assumptions atomic_ctx_arrow.
Print Assumptions K_underivable.

(* ══ 5. Why the side condition is needed ═════════════════════════ *)

(* The diagonal instance is derivable: R→ discharges A against the
   context [A; A], which Set_eq identifies with [A]. Contraction,
   unlike weakening, survives set-like contexts. *)

Example K_diagonal_derivable :
  forall f a, der f [Var a] (Some (Impl (Var a) (Var a))).
Proof.
  intros f a. apply R_arrow.
  apply Set_eq with (G := [Var a]).
  - intro X; simpl; tauto.
  - apply Ax.
Qed.

Print Assumptions K_diagonal_derivable.
