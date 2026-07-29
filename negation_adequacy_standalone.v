(* ════════════════════════════════════════════════════════════════
   NEGATION ADEQUACY — self-contained browser edition.

   Part I certifies that the encoding of negation is faithful to
   Tennant's Table 1. Parts II to IV then test that encoding by
   perturbing it: each part adds to the calculus the negation rule
   the objector would want, and reports what becomes of Part I.

   The prelude below (imports, language, fragment, the five rules,
   absurdity_core) is copied VERBATIM from
   core_logic_is_not_paraconsistent.v, SHA256 18fec76a8aaaec0bb738
   c5394eec4f9faf6effa984a88f89422c1e12e7b14b74 — lines 35-36,
   38-83 and 143-151 of that file, unmodified. Part I proves exactly
   the three theorems of negation_adequacy_supplement.v, SHA256
   936f17b6af704be505e742bd160ad8769bd9c0f2a0297328bd8050eade951239,
   which are the certified artefacts; this file exists so that all of
   it can be replayed in a browser without recompiling the appendix.

   Everything below is checked: no axiom, no admitted proof. Coq 8.18.
   ════════════════════════════════════════════════════════════════ *)

From Coq Require Import List ListSet.
Import ListNotations.
Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.

Inductive fragment_F : Type :=
  | minimal_F
  | core_logic.

(* [Some A] is a one-formula succedent.
   [None] is the empty succedent.
   Contexts are technically lists, but the left rules locate their
   principal formula extensionally, by membership: no structural
   rule is primitive. An antisequent Γ ⊬ C is rendered directly as
   the type [derivable f G C -> False]. *)

Inductive derivable :
  fragment_F -> set formula -> option formula -> Prop :=

  | Ax :
      forall f G A,
        In A G ->
        derivable f G (Some A)

  | L_neg :
      forall f G A,
        In (Neg A) G ->
        derivable f G (Some A) ->
        derivable f G None

  | R_arrow :
      forall f G A B,
        derivable f (A :: G) (Some B) ->
        derivable f G (Some (Impl A B))

  | L_arrow :
      forall f G A B C,
        In (Impl A B) G ->
        derivable f G (Some A) ->
        derivable f (B :: G) C ->
        derivable f G C

  | R_arrow_core :
      forall G A B,
        derivable core_logic (A :: G) None ->
        derivable core_logic G (Some (Impl A B)).
Lemma absurdity_core :
  forall a : nat,
    derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intro a.
  apply L_neg with (A := Var a).
  - simpl. right. left. reflexivity.
  - apply Ax. simpl. left. reflexivity.
Qed.


(* ════════════════════════════════════════════════════════════════
   PART I — THE ENCODING OF NEGATION IS FAITHFUL.

   Tennant's Table 1 gives no right-introduction rule for negation:
   negation is governed on the left only (L¬), whose discharge leads
   to the empty succedent, never to a negated conclusion. The
   encoding transcribes this with L_neg and no R_neg, and with Neg a
   primitive constructor — there is no ⊥ in the object language and
   no definition ¬A := A → ⊥.

   Such an encoding could misrepresent ℂ in two ways only: by proving
   too much about negation, or too little. The three theorems below
   close both.
   ════════════════════════════════════════════════════════════════ *)

(* The sequent an inadequacy objection would have to derive: from the
   contradiction ¬A, A ⊢ (which IS derivable — absurdity_core), reach
   the arbitrary negative conclusion ¬A, A ⊢ ¬B for a fresh atom.
   It cannot. There is no right rule for negation, so a Some (Neg _)
   succedent can arise only by Ax (¬B already in the context) or by
   L_arrow (an implication in the context); the inconsistent context
   affords neither for b <> a. *)

Theorem no_explosion_to_neg :
  forall a b : nat,
    a <> b ->
    derivable core_logic [Var a; Neg (Var a)] (Some (Neg (Var b))) ->
    False.
Proof.
  intros a b Hab HD.
  inversion HD; subst;
    match goal with
    | Hm : In _ [Var a; Neg (Var a)] |- _ =>
        simpl in Hm; destruct Hm as [Hm | [Hm | []]]; congruence
    end.
Qed.

(* Control 1: the empty-succedent contradiction IS derivable, so the
   objection's premise is genuinely available and the theorem above
   is not vacuously true. *)

Theorem contradiction_is_derivable :
  forall a : nat, derivable core_logic [Var a; Neg (Var a)] None.
Proof. intro a. apply absurdity_core. Qed.

(* Control 2: the only negative conclusion reachable is the trivial
   reflexive one, ¬A already present, by Ax — b = a, never a fresh b.
   No explosion, only membership. *)

Theorem reflexive_neg_only :
  forall a : nat,
    derivable core_logic [Var a; Neg (Var a)] (Some (Neg (Var a))).
Proof. intro a. apply Ax. simpl. right. left. reflexivity. Qed.

Print Assumptions no_explosion_to_neg.
Print Assumptions contradiction_is_derivable.
Print Assumptions reflexive_neg_only.

(* ════════════════════════════════════════════════════════════════
   PART II — WHAT IF ℂ HAD A RIGHT RULE FOR NEGATION?

   The objection Part I answers is that ℱ misrepresents ℂ by giving
   negation no right-introduction rule. Suppose it did, and suppose
   it were shaped exactly like R→ℂ — same premiss, same permission to
   discharge vacuously. The calculus below is ℱ with that one rule
   added, under primed constructor names.

   Result: no_explosion_to_neg does not merely fail, it is REFUTABLE.
   The contradiction reaches every negated conclusion.
   ════════════════════════════════════════════════════════════════ *)

Inductive der' : fragment_F -> set formula -> option formula -> Prop :=
  | Ax' : forall f G A,
      In A G -> der' f G (Some A)
  | L_neg' : forall f G A,
      In (Neg A) G -> der' f G (Some A) -> der' f G None
  | R_arrow' : forall f G A B,
      der' f (A :: G) (Some B) -> der' f G (Some (Impl A B))
  | L_arrow' : forall f G A B C,
      In (Impl A B) G -> der' f G (Some A) ->
      der' f (B :: G) C -> der' f G C
  | R_arrow_core' : forall G A B,
      der' core_logic (A :: G) None -> der' core_logic G (Some (Impl A B))
  | R_neg_core' : forall G A,          (* the added rule *)
      der' core_logic (A :: G) None -> der' core_logic G (Some (Neg A)).

Theorem explosion_to_neg :
  forall a b : nat,
    der' core_logic [Var a; Neg (Var a)] (Some (Neg (Var b))).
Proof.
  intros a b.
  apply R_neg_core'.
  apply L_neg' with (A := Var a).
  - simpl. right. right. left. reflexivity.
  - apply Ax'. simpl. right. left. reflexivity.
Qed.

Theorem part_I_would_be_false :
  ~ (forall a b : nat, a <> b ->
       der' core_logic [Var a; Neg (Var a)] (Some (Neg (Var b))) -> False).
Proof.
  intro H. exact (H 0 1 ltac:(discriminate) (explosion_to_neg 0 1)).
Qed.

(* ════════════════════════════════════════════════════════════════
   PART III — THE OBLIGATORY DISCHARGE IS NOT A RULE.

   Tennant blocks Part II by requiring the discharge in R¬ to be
   non-vacuous: one may conclude ¬A only if assuming A is what
   produced the contradiction. Rendered by its natural side
   condition — the contradiction must not already be available
   without A — the clause reads:

       | R_neg_oblig : forall G A,
           der core_logic (A :: G) None ->
           (der core_logic G None -> False) ->
           der core_logic G (Some (Neg A))

   Coq rejects this definition outright:

       Error: Non strictly positive occurrence of "der" in
       "forall (G : list formula) (A : formula),
         der core_logic (A :: G) None ->
         (der core_logic G None -> False) ->
         der core_logic G (Some (Neg A))".

   The constraint makes derivability occur negatively in its own
   defining clause. It therefore cannot belong to the inductive
   definition of a calculus at all: it is not a rule but a filter on
   derivations already built. To use it one must STRATIFY — close the
   calculus first, then impose the condition from outside, which is
   what Part IV does.

   This is not a limitation of Coq. Positivity is what makes an
   inductive definition well-founded; a clause that consults the
   non-derivability of what it is defining has no least fixed point
   to denote.
   ════════════════════════════════════════════════════════════════ *)

(* ════════════════════════════════════════════════════════════════
   PART IV — STRATIFIED, THE CONSTRAINT WORKS.

   [der_plus] lifts every derivation of ℱ and adds R¬ with the
   obligatory-discharge condition, the condition being evaluated in
   the already-closed relation [derivable]. This is accepted, and
   Part I survives: the contradiction A, ¬A blocks the rule, since
   the empty succedent is reachable without discharging anything.

   The price is exactly what Part III diagnosed. The constraint is
   metatheoretic. It also has a name: consuming the discharged
   assumption is automatic in a MULTIPLICATIVE presentation, where
   contexts are split rather than shared — there it would be a rule,
   not a filter. Tennant thus imposes a multiplicative discipline on
   negation while granting himself an additive licence on
   implication, whose vacuous discharge (his ◇ notation) is what
   R_arrow_core encodes. That asymmetry is the subject of the paper.
   ════════════════════════════════════════════════════════════════ *)

Inductive der_plus : fragment_F -> set formula -> option formula -> Prop :=
  | lift : forall f G C,
      derivable f G C -> der_plus f G C
  | R_neg_oblig : forall G A,
      der_plus core_logic (A :: G) None ->
      (derivable core_logic G None -> False) ->
      der_plus core_logic G (Some (Neg A)).

Theorem no_explosion_survives_obligatory_discharge :
  forall a b : nat, a <> b ->
    der_plus core_logic [Var a; Neg (Var a)] (Some (Neg (Var b))) -> False.
Proof.
  intros a b Hab HD.
  inversion HD; subst.
  - (* lifted from ℱ, which has no right rule for negation *)
    match goal with
    | H : derivable _ _ _ |- _ =>
        inversion H; subst;
        match goal with
        | Hm : In _ [Var a; Neg (Var a)] |- _ =>
            simpl in Hm; destruct Hm as [Hm | [Hm | []]]; congruence
        end
    end.
  - (* the obligatory-discharge condition is violated *)
    match goal with
    | H : derivable core_logic _ None -> False |- _ =>
        exact (H (absurdity_core a))
    end.
Qed.

(* ════════════════════════════════════════════════════════════════
   PART V — AND IF NEGATION WERE DEFINED RATHER THAN PRIMITIVE?

   The reading Tennant refuses: ¬B as B → ⊥. Take ⊥ to be an atom
   like any other — uninterpreted, with no rule of its own, which is
   the only honest way to add it to a calculus that has none.

   No new rule is needed here: the five rules of ℱ suffice, and not
   even the Core one. The sequent ¬A, A ⊢ ¬B is derivable in ℱ_𝐌,
   the MINIMAL reading, by L→, Ax and R→ alone.

   So the whole weight of Part I rests on negation being primitive.
   Read ¬ as an implication towards an uninterpreted atom and the
   result collapses into minimal logic — which is where Tennant does
   not want it, and which no stipulation about ⊥ can prevent without
   being ad hoc.
   ════════════════════════════════════════════════════════════════ *)

Notation Bot := (Var 0).

Theorem defined_negation_explodes_in_minimal :
  forall a b : nat,
    derivable minimal_F
      [Impl (Var a) Bot; Var a]        (* ¬A, A  read as  A → ⊥, A *)
      (Some (Impl (Var b) Bot)).       (*    ⊢ ¬B  read as  ⊢ B → ⊥ *)
Proof.
  intros a b.
  eapply L_arrow.
  - simpl. left. reflexivity.
  - apply Ax. simpl. right. left. reflexivity.
  - apply R_arrow. apply Ax. simpl. right. left. reflexivity.
Qed.

Print Assumptions explosion_to_neg.
Print Assumptions part_I_would_be_false.
Print Assumptions no_explosion_survives_obligatory_discharge.
Print Assumptions defined_negation_explodes_in_minimal.
