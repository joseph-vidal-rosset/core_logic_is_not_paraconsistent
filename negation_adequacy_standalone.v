(* ════════════════════════════════════════════════════════════════
   Negation-adequacy supplement — SELF-CONTAINED BROWSER EDITION.

   The prelude below (imports, language, fragment, the five rules,
   absurdity_core) is copied VERBATIM from
   core_logic_is_not_paraconsistent.v, SHA256 18fec76a8aaaec0bb738
   c5394eec4f9faf6effa984a88f89422c1e12e7b14b74 — lines 35-36,
   38-83 and 143-151 of that file, unmodified. Nothing is proved
   here that the appendix does not prove; this page exists only so
   that the three theorems below can be replayed in a browser
   without recompiling the whole appendix. The certified artefacts
   remain core_logic_is_not_paraconsistent.v and
   negation_adequacy_supplement.v, checked separately with coqc.
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
