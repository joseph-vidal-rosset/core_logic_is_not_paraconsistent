(* ════════════════════════════════════════════════════════════════
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
   ════════════════════════════════════════════════════════════════ *)

From Coq Require Import List ListSet.
Import ListNotations.

(* ── Formulae and fragments ── *)

Inductive formula : Type :=
  | Var  : nat -> formula
  | Neg  : formula -> formula
  | Impl : formula -> formula -> formula.

Inductive fragment_F : Type :=
  | minimal_F
  | core_logic.

(* [Some A] is a one-formula succedent.
   [None] is the empty succedent. *)

(* ════════════════════════════════════════════════════════════════
   Full corrected calculus

   Contexts are technically lists, but L_neg and L_arrow locate their
   principal formula extensionally by membership. No Exchange
   constructor is present.
   ════════════════════════════════════════════════════════════════ *)

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

(* ── Structural admissibility: weakening ── *)

Lemma weakening_subset :
  forall f G G' C,
    derivable f G C ->
    (forall A, In A G -> In A G') ->
    derivable f G' C.
Proof.
  intros f G G' C HD.
  revert G'.
  induction HD; intros G' Hsub.
  - apply Ax.
    apply Hsub.
    exact H.

  - apply L_neg with (A := A).
    + apply Hsub.
      exact H.
    + apply IHHD.
      exact Hsub.

  - apply R_arrow.
    apply IHHD.
    intros X HX.
    simpl in HX |- *.
    destruct HX as [HX | HX].
    + left.
      exact HX.
    + right.
      apply Hsub.
      exact HX.

  - apply L_arrow with (A := A) (B := B).
    + apply Hsub.
      exact H.
    + apply IHHD1.
      exact Hsub.
    + apply IHHD2.
      intros X HX.
      simpl in HX |- *.
      destruct HX as [HX | HX].
      * left.
        exact HX.
      * right.
        apply Hsub.
        exact HX.

  - apply R_arrow_core.
    apply IHHD.
    intros X HX.
    simpl in HX |- *.
    destruct HX as [HX | HX].
    + left.
      exact HX.
    + right.
      apply Hsub.
      exact HX.
Qed.

(* Every minimal derivation can be replayed in Core because the first
   four full-calculus rules are shared. *)

Lemma MinToCore :
  forall G C,
    derivable minimal_F G C ->
    derivable core_logic G C.
Proof.
  intros G C HD.
  remember minimal_F as f eqn:Hf.
  induction HD.
  - apply Ax.
    exact H.

  - apply L_neg with (A := A).
    + exact H.
    + apply IHHD.
      exact Hf.

  - apply R_arrow.
    apply IHHD.
    exact Hf.

  - apply L_arrow with (A := A) (B := B).
    + exact H.
    + apply IHHD1.
      exact Hf.
    + apply IHHD2.
      exact Hf.

  - discriminate Hf.
Qed.

(* ════════════════════════════════════════════════════════════════
   F*: focused shared kernel

   This calculus has exactly the rules shared by M and Core, but no
   R_arrow_core. Its L_arrow rule is written in focused form, with
   the principal implication at the head of the context.

   This is not an Exchange rule: no permutation constructor is
   postulated. It is a focused presentation used to state and prove
   DNS.1 inversion directly.

   The embedding [star_to_minimal] proves that every F* derivation is
   also derivable in the corrected membership-based minimal calculus.
   ════════════════════════════════════════════════════════════════ *)

Inductive derivable_star :
  set formula -> option formula -> Prop :=

  | Ax_star :
      forall G A,
        In A G ->
        derivable_star G (Some A)

  | L_neg_star :
      forall G A,
        In (Neg A) G ->
        derivable_star G (Some A) ->
        derivable_star G None

  | R_arrow_star :
      forall G A B,
        derivable_star (A :: G) (Some B) ->
        derivable_star G (Some (Impl A B))

  | L_arrow_star :
      forall G A B C,
        derivable_star G (Some A) ->
        derivable_star (B :: G) C ->
        derivable_star (Impl A B :: G) C.

(* F* is contained in the corrected minimal calculus. *)

Lemma star_to_minimal :
  forall G C,
    derivable_star G C ->
    derivable minimal_F G C.
Proof.
  intros G C HD.
  induction HD.
  - apply Ax.
    exact H.

  - apply L_neg with (A := A).
    + exact H.
    + exact IHHD.

  - apply R_arrow.
    exact IHHD.

  - apply L_arrow with (A := A) (B := B).
    + simpl.
      left.
      reflexivity.

    + (* G |- A  entails  (A -> B), G |- A. *)
      refine
        (weakening_subset minimal_F G (Impl A B :: G) (Some A)
           IHHD1 _).
      intros X HX.
      simpl.
      right.
      exact HX.

    + (* B, G |- C  entails  B, (A -> B), G |- C. *)
      refine
        (weakening_subset minimal_F (B :: G)
           (B :: Impl A B :: G) C IHHD2 _).
      intros X HX.
      simpl in HX |- *.
      destruct HX as [HB | HG].
      * left.
        exact HB.
      * right.
        right.
        exact HG.
Qed.


(* Consequently, F* is also contained in Core. *)

Lemma star_to_core :
  forall G C,
    derivable_star G C ->
    derivable core_logic G C.
Proof.
  intros G C HD.
  apply MinToCore.
  apply star_to_minimal.
  exact HD.
Qed.

(* ════════════════════════════════════════════════════════════════
   DNS.1 inside F*
   ════════════════════════════════════════════════════════════════ *)

Theorem DNS1_star_instantiated :
  forall a b : nat,
    derivable_star [Var a; Neg (Var a)] (Some (Var b)) ->
    derivable_star
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros a b HD.
  apply (L_arrow_star [Neg (Var a)]
           (Impl (Var a) (Var b)) (Var b) (Some (Var b))).
  - apply R_arrow_star.
    exact HD.
  - apply Ax_star.
    simpl.
    left.
    reflexivity.
Qed.

(* The same F* DNS.1 derivation is therefore available in both M and
   Core, since F* embeds into both readings. *)

Corollary DNS1_star_in_minimal :
  forall a b : nat,
    derivable_star [Var a; Neg (Var a)] (Some (Var b)) ->
    derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros a b HD.
  apply star_to_minimal.
  apply DNS1_star_instantiated.
  exact HD.
Qed.

Corollary DNS1_star_in_core :
  forall a b : nat,
    derivable_star [Var a; Neg (Var a)] (Some (Var b)) ->
    derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros a b HD.
  apply star_to_core.
  apply DNS1_star_instantiated.
  exact HD.
Qed.

(* ════════════════════════════════════════════════════════════════
   Invertibility of DNS.1 inside F*
   ════════════════════════════════════════════════════════════════ *)

(* First invert R_arrow over the singleton context [¬A]. Since F*
   has no R_arrow_core constructor, the only possible final rule for
   a derivation of an implication in this situation is ordinary
   R_arrow_star. *)

Lemma R_arrow_inv_NegA_star :
  forall a b : nat,
    derivable_star [Neg (Var a)] (Some (Impl (Var a) (Var b))) ->
    derivable_star [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b HD.
  remember [Neg (Var a)] as G eqn:HG.
  remember (Some (Impl (Var a) (Var b))) as C eqn:HC.
  revert HG HC.
  induction HD; intros HG HC.
  - subst.
    injection HC as HC'.
    subst.
    simpl in H.
    destruct H as [Heq | []].
    discriminate Heq.

  - discriminate HC.

  - injection HC as HA HB.
    subst.
    assumption.

  - injection HG as Hhead Htail.
    discriminate Hhead.
Qed.

(* Now invert DNS.1 itself. The only L_arrow_star case compatible
   with the target context has outer implication
   ((Var a -> Var b) -> Var b) as principal formula. Its left
   premiss is [¬Var a] |- Var a -> Var b, which the preceding lemma
   inverts to [Var a, ¬Var a] |- Var b. *)

Theorem DNS1_inv_star_instantiated :
  forall a b : nat,
    derivable_star
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)) ->
    derivable_star [Var a; Neg (Var a)] (Some (Var b)).
Proof.
  intros a b HD.
  assert
    (Hgen :
      forall G C,
        derivable_star G C ->
        G =
          [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)] ->
        C = Some (Var b) ->
        derivable_star [Var a; Neg (Var a)] (Some (Var b))).
  {
    clear HD.
    intros G C Hder.
    induction Hder; intros HG HC.
    - injection HC as HC'.
      subst.
      subst.
      simpl in H.
      destruct H as [Heq | [Heq | []]];
        discriminate Heq.

    - discriminate HC.

    - discriminate HC.

    - injection HG as HA HB HG0.
      subst.
      apply R_arrow_inv_NegA_star.
      assumption.
  }
  apply (Hgen _ _ HD).
  - reflexivity.
  - reflexivity.
Qed.

(* Contraposition of F*-DNS.1 inversion: anti-DNS.1 is a derived rule
   of the shared kernel F*. *)

Theorem DNS1_anti_star_instantiated :
  forall a b : nat,
    (derivable_star [Var a; Neg (Var a)] (Some (Var b)) -> False) ->
    (derivable_star
       [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
       (Some (Var b)) -> False).
Proof.
  intros a b Hpremiss Hconclusion.
  apply Hpremiss.
  apply DNS1_inv_star_instantiated.
  exact Hconclusion.
Qed.

(* ════════════════════════════════════════════════════════════════
   Full Core: DNS.2
   ════════════════════════════════════════════════════════════════ *)

(* The inconsistency sequent {A, ¬A} |- is derivable in full Core.
   L_neg uses membership, hence no Exchange is needed. *)

Lemma absurdity_core :
  forall a : nat,
    derivable core_logic [Var a; Neg (Var a)] None.
Proof.
  intro a.
  apply L_neg with (A := Var a).
  - simpl.
    right.
    left.
    reflexivity.
  - apply Ax.
    simpl.
    left.
    reflexivity.
Qed.

(* DNS.2 is the Core-specific counterpart. The only extra rule used
   is R_arrow_core. *)

Theorem DNS2_instantiated :
  forall a b : nat,
    derivable core_logic [Var a; Neg (Var a)] None ->
    derivable core_logic
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)).
Proof.
  intros a b HD.
  apply L_arrow with
    (A := Impl (Var a) (Var b))
    (B := Var b).

  - simpl.
    left.
    reflexivity.

  - eapply weakening_subset.
    + apply R_arrow_core.
      exact HD.
    + intros X HX.
      simpl in HX |- *.
      destruct HX as [HX | []].
      right.
      left.
      exact HX.

  - apply Ax.
    simpl.
    left.
    reflexivity.
Qed.

(* Regression: no primitive Exchange is needed to derive
   (p -> q -> r) -> q -> p -> r in the corrected minimal calculus. *)

Theorem exchange_weakening_regression :
  forall p q r : formula,
    derivable minimal_F []
      (Some
        (Impl (Impl p (Impl q r))
          (Impl q (Impl p r)))).
Proof.
  intros p q r.
  apply R_arrow.
  apply R_arrow.
  apply R_arrow.

  apply L_arrow with
    (A := p)
    (B := Impl q r).

  - simpl.
    right.
    right.
    left.
    reflexivity.

  - apply Ax.
    simpl.
    left.
    reflexivity.

  - apply L_arrow with
      (A := q)
      (B := r).

    + simpl.
      left.
      reflexivity.

    + apply Ax.
      simpl.
      right.
      right.
      left.
      reflexivity.

    + apply Ax.
      simpl.
      left.
      reflexivity.
Qed.

(* ════════════════════════════════════════════════════════════════
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
   ════════════════════════════════════════════════════════════════ *)

Theorem claim1_false :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_shared :
      forall a b : nat,
        a <> b ->
        (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False)),

    forall a b : nat,
      a <> b ->
      False.
Proof.
  intros Claim1_Tennant anti_DNS1_shared a b Hab.
  apply (anti_DNS1_shared a b Hab).
  - apply (Claim1_Tennant a b Hab).
  - apply DNS2_instantiated.
    apply absurdity_core.
Qed.

(* Closed instance at distinct atoms 0 and 1. *)

Corollary claim1_false_at_0_1 :
  forall
    (Claim1_Tennant :
      forall a b : nat,
        a <> b ->
        derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
        False)

    (anti_DNS1_shared :
      forall a b : nat,
        a <> b ->
        (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False)),

    False.
Proof.
  intros Claim1_Tennant anti_DNS1_shared.
  apply
    (claim1_false Claim1_Tennant anti_DNS1_shared 0 1).
  discriminate.
Qed.

(* The first theorem must be assumption-free. The final two results
   must depend only on their explicit theorem parameters. *)

Print Assumptions DNS1_anti_star_instantiated.
Print Assumptions claim1_false.
Print Assumptions claim1_false_at_0_1.

(* ════════════════════════════════════════════════════════════════
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
   ════════════════════════════════════════════════════════════════ *)

Lemma M_blocked :
  forall a b : nat,
    a <> b ->
    forall f G C,
      derivable f G C ->
      f = minimal_F ->
      (forall X, In X G ->
        X = Var a \/ X = Neg (Var a) \/
        X = Impl (Impl (Var a) (Var b)) (Var b)) ->
      C <> Some (Var b) /\ C <> Some (Impl (Var a) (Var b)).
Proof.
  intros a b Hab f G C HD.
  induction HD; intros Hf HS.

  - (* Ax: the succedent is a member of the context, hence one of the
       three formulas of the invariant; none of them is Var b or
       Var a -> Var b when a <> b. *)
    destruct (HS A H) as [H1 | [H1 | H1]]; subst A;
      split; intro HC; congruence.

  - (* L_neg: empty succedent. *)
    split; intro HC; discriminate.

  - (* R_arrow: if the succedent were Var a -> Var b, the premiss
       would derive Var b from an invariant-closed context. *)
    split; intro HC.
    + discriminate.
    + injection HC as HA HB.
      subst A B.
      assert (HS' : forall X, In X (Var a :: G) ->
        X = Var a \/ X = Neg (Var a) \/
        X = Impl (Impl (Var a) (Var b)) (Var b)).
      { intros X [HX | HX].
        - left. symmetry. exact HX.
        - apply HS. exact HX. }
      destruct (IHHD Hf HS') as [Hcontr _].
      apply Hcontr.
      reflexivity.

  - (* L_arrow: the principal implication can only be
       (Var a -> Var b) -> Var b, whose left premiss derives
       Var a -> Var b from the same invariant-closed context,
       contradicting the induction hypothesis. This is exactly the
       case excluded in F* by consuming the principal formula. *)
    destruct (HS _ H) as [H1 | [H1 | H1]]; try discriminate.
    injection H1 as HA HB.
    subst A B.
    exfalso.
    apply (proj2 (IHHD1 Hf HS)).
    reflexivity.

  - (* R_arrow_core does not belong to M. *)
    discriminate Hf.
Qed.

(* Consequence 1: in M itself, both the premiss and the conclusion of
   the DNS.1 instance are underivable, unconditionally. *)

Theorem claim1_holds_in_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (M_blocked a b Hab _ _ _ HD eq_refl _) eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - left. reflexivity.
  - right. left. reflexivity.
Qed.

Theorem DNS1_conclusion_underivable_in_M :
  forall a b : nat,
    a <> b ->
    derivable minimal_F
      [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
      (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  refine (proj1 (M_blocked a b Hab _ _ _ HD eq_refl _) eq_refl).
  intros X HX.
  simpl in HX.
  destruct HX as [HX | [HX | []]]; subst X.
  - right. right. reflexivity.
  - right. left. reflexivity.
Qed.

(* Hence the anti-DNS.1 instance is a metatheorem of M itself, with
   no detour through F*. The adequacy gap left by the one-directional
   embedding star_to_minimal is thereby closed for this instance. *)

Theorem anti_DNS1_holds_in_M :
  forall a b : nat,
    a <> b ->
    (derivable minimal_F [Var a; Neg (Var a)] (Some (Var b)) ->
     False) ->
    (derivable minimal_F
       [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
       (Some (Var b)) ->
     False).
Proof.
  intros a b Hab _ HD.
  exact (DNS1_conclusion_underivable_in_M a b Hab HD).
Qed.

(* Consequence 2, for full Core C. First, Claim 1 holds of the
   formalized fragment: no rule can conclude
   [Var a; ¬Var a] ⊢ Var b when a <> b, since Ax requires Var b in
   the context, L_arrow requires an implication in the context, L_neg
   concludes on the empty succedent, and both right rules conclude on
   an implicational succedent. *)

Theorem claim1_holds_in_C :
  forall a b : nat,
    a <> b ->
    derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
    False.
Proof.
  intros a b Hab HD.
  inversion HD; subst; simpl in *;
    repeat (match goal with
            | Hyp : _ \/ _ |- _ => destruct Hyp as [Hyp | Hyp]
            | Hyp : False |- _ => destruct Hyp
            end);
    congruence.
Qed.

(* Second, C refutes the transfer of the anti-DNS.1 instance from M
   to C: since DNS.2 is derivable in C through R_arrow_core while
   Claim 1 holds of the fragment, the Core-level anti-DNS.1 instance
   is false of the formalized calculus. The hypothesis
   anti_DNS1_shared of the final theorem is therefore exactly the
   disputed M-to-C antisequent transfer for this instance: the
   formalization displays it, and only Tennant's own account of the
   shared kernel can ground it. *)

Theorem anti_DNS1_refuted_in_C :
  forall a b : nat,
    a <> b ->
    ~ ( (derivable core_logic [Var a; Neg (Var a)] (Some (Var b)) ->
         False) ->
        (derivable core_logic
           [Impl (Impl (Var a) (Var b)) (Var b); Neg (Var a)]
           (Some (Var b)) ->
         False) ).
Proof.
  intros a b Hab H.
  apply (H (claim1_holds_in_C a b Hab)).
  apply DNS2_instantiated.
  apply absurdity_core.
Qed.

Print Assumptions anti_DNS1_holds_in_M.
Print Assumptions anti_DNS1_refuted_in_C.
