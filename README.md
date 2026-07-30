# Core Logic is not paraconsistent — Version 6

Machine-checked companion to the note *Core Logic is not
paraconsistent: one proof, six certifications*
([arXiv:2606.05953](https://arxiv.org/abs/2606.05953)).

**The argument, in one paragraph.** DNS.1 is a derivable rule of the
fragment ℱ under both of its readings, and it is *invertible* at the
decisive instance in the minimal reading ℱ_𝐌: both the premiss sequent
`A, ¬A ⇒ B` and the conclusion sequent `(A→B)→B, ¬A ⇒ B` are
underivable there. Hence the refutation system with Claim 1 as its
only rejection axiom and anti-DNS.1 as its only refutation rule — in
the sense of Łukasiewicz, Tiomkin (1988) and Goranko (*Studia Logica*
53, 1994) — is Ł-correct for ℱ_𝐌. But that same refutation system is
Ł-*incorrect* for the Core reading ℱ_ℂ: the decisive instance at the
atoms 0, 1 is rejected by the system, yet derivable in ℱ_ℂ through
R→ℂ. Jointly, then, the two commitments of Core Logic — Claim 1, and
the refutation rule its paraconsistency argument requires — refute
themselves: `claim1_false`, closed at the atoms 0 and 1 in
`claim1_false_at_0_1` with no remaining hypothesis. Finally, Claim 1
is in fact *true* of ℱ_ℂ (`claim1_holds_in_ℱ_ℂ`) — and precisely for
that reason anti-DNS.1 is Ł-incorrect for ℱ_ℂ
(`anti_DNS1_Ł_incorrect_for_ℱ_ℂ`): one cannot both keep Claim 1 and
use the refutation rule the paraconsistency argument needs.

## The six certifications

The same twelve theorems, under the same names and the same block
structure (A–F), are certified in three proof languages with distinct
foundations, and under both structural readings of the fragment.
Every link below runs the file in the browser, with nothing to
install.

|  | **additive reading** of `Ax` and `L→` | **multiplicative reading** |
|---|---|---|
| **Coq 8.18** | `core_logic_is_not_paraconsistent.v` — [run](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_logic_is_not_paraconsistent.html) | `core_logic_F_multiplicative.v` — [run](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_logic_F_multiplicative.html) |
| **Lean 4** | `core_logic_is_not_paraconsistent.lean` = `Solution.lean` — [Comparator](https://comparator.live.lean-lang.org) | `core_logic_F_multiplicative.lean` — [Comparator](https://comparator.live.lean-lang.org) |
| **Athena** | `core_logic_is_not_paraconsistent.ath` — [run](https://athena.vidal-rosset.net/?file=core_logic_is_not_paraconsistent.ath) | `core_logic_F_multiplicative.ath` — [run](https://athena.vidal-rosset.net/?file=core_logic_F_multiplicative.ath) |

Coq and Lean 4 are two kernels of one family: both implement a
calculus of inductive constructions, so a proof passing both has been
checked twice against a single foundation. Athena is not of that
family — it is a polymorphic multi-sorted first-order framework with
an assumption-base semantics in the LCF tradition (Arkoudas & Musser,
*Fundamental Proof Methods in Computer Science*, MIT Press, 2017),
with no dependent types, no inductive definitions and no proof terms.
A proof surviving verbatim translation into it lives in the inductive
structure of the calculus, not in the idiosyncrasies of one assistant.

`core_logic_is_not_paraconsistent.pl` corroborates the same results
computationally in a fourth system: it *searches* for derivations,
builds explicit proof trees and renders them in LaTeX (bussproofs),
one user command per section. It runs locally (`swipl
core_logic_is_not_paraconsistent.pl`) or on
[SWI-Tinker](https://swi-prolog.org/wasm/tinker). Its status is stated
in its header: corroboration, not certification — search exhibits
witnesses, the six certifications check proofs.

In every certification *nothing is asserted for the argument*. The
only axioms are definitional: the inductive definitions of the
language, the derivations and the refutation system. The two
commitments of Core Logic occur exclusively as antecedents of the
final theorems, and every `Print Assumptions` reports `Closed under
the global context`.

## What the two readings decide

Table 1 of the note fixes five rules, and a formal encoding must
settle two things their notation leaves open: whether an initial
sequent may carry side formulæ, and whether `L→` shares one context or
splits it. Exactly two clauses therefore differ between the columns
above. `L¬`, `R→` and `R→ℂ` are letter for letter the same in both.

| Table 1 | additive files | multiplicative files |
|---|---|---|
| *Ax.* `A ⊢ A` | `In A Γ → Γ ⊢ A` — reflexivity on contexts | `[A] ⊢ A` — the context forced to the singleton |
| `L→`, contexts split | one shared context, `context_monotonicity` proved as a lemma | `Impl A B :: G ++ D`, the premiss contexts disjoint pieces of the conclusion's |

**The two additive deviations are not independent.** The diluted axiom
is what restores, in the textbook form of `R_arrow`, the *optional*
discharge that Table 1 writes `Δ \ {A}`: from `B, A ⊢ A` by `Ax`,
`A ⊢ B → A` follows by `R_arrow` — Tennant's own theorem (*Core
Logic*, p. 35), and the reason Weakening on the left, though not a
*rule* of ℂ, must be *admissible* in it on consistent contexts. The
additive reading is thus an upper bound: ℱ_ℂ ⊆ additive.

**The multiplicative reading lies strictly below ℂ, and certifies that
it does.** It takes Table 1's two clauses literally and declares no
monotonicity lemma anywhere. With the axiom no longer diluted the
discharge in `R_arrow` becomes obligatory, and `A ⊢ B → A` is
underivable there — see *Strictness of the lower bound* below. Hence
multiplicative ⊊ ℱ_ℂ.

**Each half of the proof is certified at the bound that carries it.**

- The *derivable* half — `absurdity_core`, `DNS1_in_ℱ`,
  `DNS2_instantiated`, hence the sequent that collides — is certified
  at the **lower** bound. What a subsystem derives, ℂ derives *a
  fortiori*.
- The *underivable* half — `claim1_holds_in_ℱ_ℂ`,
  `DNS1_conclusion_underivable_in_ℱ_M`, and with them
  `refutation_system_Ł_correct_for_ℱ_M` — is certified at the
  **upper** bound. What a system with *more* derivations still refuses
  to derive, ℂ refuses *a fortiori*.
- `claim1_false` and `claim1_false_at_0_1` need neither concession:
  they receive Claim 1 from Tennant as a hypothesis rather than
  proving it, and consume only the derivable half. They are certified
  at both bounds — which is why the theorem is carried, on its own, by
  either column.

No structural reading of ℱ lying between the two bounds can therefore
be what produces the contradiction. Two remarks complete the picture.
In both DNS derivations the multiplicative `L→` is applied with its
*right* context empty (`D = []` in the files, `Γ = ∅` in Table 1), the
right premiss being the axiom `B ⊢ B`; the split does no work there,
and the additive version reaches the same sequent by its single
`context_monotonicity` step — two derivations of one sequent, not two
logics. And the bracketing itself is an argument about encodings, not
a certified statement: the three systems check the two bounds, and de
Bruijn's criterion forbids more, on pain of regress. What the two
bounds achieve is the removal of any reading in which the doubt could
still lodge.

## Strictness of the lower bound

`addendum_K_underivable.v` — self-contained, 190 lines, Coq 8.18.0.
[Run it in the browser](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/addendum_K_underivable.html).

The claim that the multiplicative presentation is a *strict* subsystem
of ℱ_ℂ used to rest on inspection. It is now certified:

- `atomic_no_refutation` — from a purely atomic context, `None` is
  never derivable. Only `L¬` concludes `None`, and it requires a
  negated head; `Set_eq` preserves atomicity.
- `atomic_ctx_arrow` — from an atomic context, an implication between
  atoms is derivable only if the two atoms coincide. The `R→` case
  falls to `atomic_relevance`, because the discharge is obligatory;
  the `R→ℂ` case falls to the lemma above.
- `K_underivable` — `∀ f a b, a ≠ b → ¬ der f [Var a] (Some (Impl (Var b) (Var a)))`.
  Quantified over `f`, hence holding in `minimal_F` and in
  `core_logic` alike.

The side condition `a ≠ b` is not decorative, and the file ends by
showing why: `K_diagonal_derivable` derives `A ⊢ A → A` — `R→`
discharging `A` against `[A; A]`, which `Set_eq` identifies with
`[A]`. Contraction, unlike Weakening, survives set-like contexts.

Sections 1 and 2 of the file repeat, verbatim, the definitions and the
lemma `atomic_relevance` of `core_logic_F_multiplicative.v`, so that
it stands alone and a reader can `diff` them to check that no
definition moved.

## The Athena certifications

`core_logic_is_not_paraconsistent.ath` — single file, pure ASCII,
faithful block by block (A–F) to the Coq source and to
`Solution.lean`. Seventeen theorems: the twelve of the note under the
same names (transliterated `ℱ_𝐌` → `F-M`, `ℱ_ℂ` → `F-C`, `Ł` → `L`),
plus the five auxiliary lemmas of the Coq file (`absurdity-core`,
`context-monotonicity`, `DNS1-inversion-lemma`, `refut-inversion`,
`L-correct-aux`).

`core_logic_F_multiplicative.ath` — 1796 lines, its multiplicative
twin. Because Athena has no inductive-type kernel, everything Coq gets
from `Inductive` is built by hand, and the multiplicative reading
makes that visible in three places. List append is *declared and
axiomatised, not imported*: `++` is introduced with two defining
equations, `(nil ++ D) = D` and `((A :: G) ++ D) = (A :: (G ++ D))`,
before the `Deriv` datatype, since the split-context clause needs it
in scope — what Coq takes from `List` is here part of the assumption
base, and visible in it. The split itself is stated in the
well-formedness clause: `wf-l-arrow` reads
`G' = ((Impl A B) :: (G ++ D))` with premisses
`(well-formed d1 f G (some-succ A))` and
`(well-formed d2 f (B :: D) Sc)`, so the conclusion's context is the
join of two disjoint pieces and nothing relates them. And set-like
identity is a membership equivalence inlined in `wf-set-eq` as
`(forall ?X . (mem ?X G) <==> (mem ?X G'))`, with no auxiliary
predicate: it is not a monotonicity rule, and no monotonicity lemma is
declared or used anywhere in the file.

Two structural lemmas are specific to it and have no counterpart in
the additive `.ath`: `mem-app-left` (membership transports from a
piece `G` into the join `G ++ D`) and `app-nil-right` (right identity
of `++`, needed wherever `G ++ []` must simplify back to `G` — that
is, at both DNS derivations). The method `mem-swap-pair!` is the
counterpart of Coq's `set_eq_2`. Twenty-three statements are
established at top level: eighteen `conclude` blocks and five by
top-level `by-induction` or `datatype-cases` (`mem-app-left`,
`app-nil-right`, `refut-inversion`, `L-correct-aux`,
`atomic-relevance`).

Common to both files:

- **Zero axioms for the argument.** Every `assert` is definitional:
  datatype free-generation axioms and the defining biconditionals of
  `mem`, `++`, `well-formed`, `refut-wf`, `refutable` — the exact
  counterparts of Coq's `Inductive` declarations. The two commitments
  occur only as antecedents of `claim1-false` and
  `claim1-false-at-zero-one`.
- **Atoms are Peano naturals** (`datatype Atom := zero | succ`),
  mirroring `Var : nat -> formula`: the closed instances need
  *provably* distinct atoms, and `(zero =/= succ zero)` is a
  free-generation axiom of the datatype — the counterpart of Coq's
  `discriminate`.
- **No Exchange rule.** Left rules locate their principal formula by
  membership (`mem`), as `In _ Γ` does in Coq. The additive file uses
  `context-monotonicity`, proved by structural induction on reified
  derivations — not Weakening, not Cut; the multiplicative file uses
  no structural fact of the kind at all.
- **Fully deterministic.** No call to automated provers: every step is
  a kernel step (`uspec`, `mp`, directed `chain` rewriting), so
  verification succeeds or fails independently of any resource limit.

Both are validated on two independently built runtimes of the same
kernel sources: the MLton native binary (v1.6.1, the one serving
[athena.vidal-rosset.net](https://athena.vidal-rosset.net)) and an
SML/NJ heap image.

## Adequacy: negation

The structural objection has a companion — that the treatment of
negation is not Tennant's. The full discussion is in the note; what
this repository adds is the mechanised part.

The first half of the objection dissolves once the provenance of the
refutation rule is seen. anti-DNS.1 is never derived inside ℂ. Under
the minimal reading it is *proved* (`anti_DNS1_holds_in_ℱ_M`, with
`refutation_system_Ł_correct_for_ℱ_M`), the contraposition performed
there being ordinary reasoning about underivability, which is what
Ł-correctness consists in. Under the Core reading it is *assumed*:
`anti_DNS1_rule_for_ℂ` is an antecedent of `claim1_false`. Nothing
whatever is asserted of ℂ.

Negation enters the argument at exactly one point, and through the one
rule Table 1 supplies for it. In `absurdity_core`, the axiom `A ⊢ A`
becomes `¬A, A ⊢` by `L_neg`, which introduces the negation on the
left and empties the succedent — the sequent without which
`R_arrow_core` would have nothing to discharge. Everything after
that is implicational: `DNS2_instantiated` reaches the decisive
sequent by `L_arrow`, `R_arrow_core` and `Ax`, with `Neg (Var a)`
crossing it in the context, transported unchanged, never a principal
formula. (`DNS1_in_ℱ`, the uniform version of the rule, plays no part
here: its antecedent `A, ¬A ⊢ B` is exactly what Claim 1 denies, and
it is invoked nowhere in the file. The Core route to the decisive
sequent runs through the empty succedent instead.) So the chain turns
on the implication rules, `R→ℂ` above all, and on the single left rule
for negation — and there is no right rule for negation to tighten, to
weaken, or to accuse.

The second half is answered by two files.
`negation_adequacy_supplement.v` imports the frozen appendix as a
module without modifying it, and pins the encoded negation between an
upper and a lower bound: `no_explosion_to_neg` (from `A, ¬A` the
sequent `A, ¬A ⊢ ¬B` is *not* derivable for a fresh `B`),
`contradiction_is_derivable` (so the theorem is not vacuously true),
and `reflexive_neg_only` (the one reachable negative conclusion is the
trivial reflexive one, by membership).

`negation_adequacy_standalone.v` —
[run it](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/negation_adequacy_standalone.html)
— goes further and *perturbs* the encoding, adding the negation rule
an objector would want and reporting what becomes of the result. Give
ℂ a right rule for negation with the vacuous discharge R→ℂ enjoys, and
the result is not weakened but refuted (`explosion_to_neg`). Impose
Tennant's non-vacuity side condition as a rule, and Coq rejects the
definition — *non strictly positive occurrence*: the clause consults
the non-derivability of the very relation it defines, so it has no
least fixed point. Stratify it instead, closing the calculus first and
imposing the condition from outside, and the result survives
(`no_explosion_survives_obligatory_discharge`), at the stated price
that the constraint is metatheoretic. Read `¬B` as `B → ⊥` with `⊥` an
uninterpreted atom, and `¬A, A ⊢ ¬B` becomes derivable by `L→`, `Ax`
and `R→` alone, in ℱ_𝐌 without any Core rule
(`defined_negation_explodes_in_minimal`).

What this yields is not a defence but a diagnosis: the constraint
Tennant needs on negation is *multiplicative*, while the licence he
grants himself on implication — the vacuous discharge written ◇ — is
*additive*. He is relevantist about ¬ and permissive about →, and the
note exploits that asymmetry.

**What this does not settle.** All of the above holds relative to ℱ. A
reader may still ask whether, in ℂ taken whole, the premiss sequent
might become derivable, which would touch the invertibility. That
question is legitimate and no supplement here closes it. It is,
however, a question about the choice of fragment rather than about
negation; it bears equally on both readings; and a fragment is all
that an inconsistency needs.

## Checking it

**Coq.** No external library, no pinned version. The Coq files have
been compiled under 8.18.0 and 8.20.1, every `Print Assumptions`
reporting `Closed under the global context` under both, with no
deprecation warning under either.

```
coqc core_logic_is_not_paraconsistent.v
coqc core_logic_F_multiplicative.v
coqc addendum_K_underivable.v
coqc negation_adequacy_supplement.v     # after the first, which it imports
```

If the supplement is invoked from elsewhere, bind the load path:
`coqc -Q <dir> "" <dir>/negation_adequacy_supplement.v`.

A word on `ListSet` in the reference source, since a reader may
suspect it smuggles something in. It does not: it is used for the type
notation alone, in the signatures of `derivable` and `refutable`, and
`set A` is by definition `list A`. No function of the module —
`set_add`, `set_mem`, `set_union` — occurs anywhere in the file, and
none of its decidability requirements is ever discharged; two `grep`
commands establish this. The set-like reading of contexts is therefore
*nominal*, never operational: no normalisation happens behind the
notation, hence no hidden Contraction. The multiplicative file reaches
the same point by the other route, stating set-like identity as a
membership equivalence rather than as a data structure.

**Athena.** Build from the [official
sources](https://github.com/AthenaFoundation/Athena), as the MLton
native binary or as an SML/NJ heap image
(`sml scripts/make_smlnj_binary.sml`), then:

```
athena core_logic_is_not_paraconsistent.ath     # 17 Theorem reports
athena core_logic_F_multiplicative.ath          # 23, no evaluation error
```

**Lean 4, in the browser.** Open
[comparator.live.lean-lang.org](https://comparator.live.lean-lang.org)
and paste `Challenge.lean` as the challenge and
`core_logic_is_not_paraconsistent.lean` as the solution; likewise
`Challenge_multiplicative.lean` with
`core_logic_F_multiplicative.lean`.

**Lean 4, at the gold standard.** The additive proof is also checked
against a *trusted challenge* and replayed through two independently
implemented kernels — Lean's own and nanoda — as prescribed by the
Lean reference manual, [*Validating a Lean
Proof*](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
`Challenge.lean` is the entire trusted base: the language, the rules
of ℱ under both readings, the refutation system, and the twelve
theorems with proofs left as `sorry`. `Solution.lean` is the
candidate, byte-identical to `core_logic_is_not_paraconsistent.lean`.
`config.json` lists the twelve theorem names, the permitted axioms
`propext, Quot.sound, Classical.choice`, and enables the nanoda
kernel; `lean-toolchain` pins Lean `v4.31.0-rc2`. Prerequisites: a
toolchain via [elan](https://elan.lean-lang.org), the
[comparator](https://github.com/leanprover/comparator) built with
`lake build lean4export comparator`,
[landrun](https://github.com/zouuup/landrun) as the build sandbox
(reachable via `PATH` or `COMPARATOR_LANDRUN`), and
[nanoda](https://github.com/ammkrn/nanoda_lib) built with
`cargo build --release` (via `COMPARATOR_NANODA`).

The multiplicative pair has *not* been run through the local
two-kernel procedure, and this repository ships no `config.json` for
it. The distinction is deliberate: what is claimed here is what has
been checked, and nothing more.

## Integrity

Every certified file, with the hash of the version cited:

| File | SHA256 |
|---|---|
| `core_logic_is_not_paraconsistent.v` | `18fec76a8aaaec0bb738c5394eec4f9faf6effa984a88f89422c1e12e7b14b74` |
| `core_logic_F_multiplicative.v` | `14c0aeca079cbceca344be0623e6fa3a97fa7316619e2983f2a437c61908005b` |
| `addendum_K_underivable.v` | `f64fe6f3aa939aaab8f0987223a9d2ea7e5575d04974b2497a314a09af967730` |
| `negation_adequacy_supplement.v` | `936f17b6af704be505e742bd160ad8769bd9c0f2a0297328bd8050eade951239` |
| `core_logic_F_multiplicative.lean` | `1922f494af6a1e7ad12d229d9d4a0055d8756378b70b4381ec23bace3e78fff3` |
| `Solution.lean` = `core_logic_is_not_paraconsistent.lean` | `acddd04c222a9958aca2a998849e24b0b94b17c876e7ff3da832f6ac437701e1` |
| `Challenge.lean` | `6147a4234a2420a420d2c67eb145ace7b3d9ec14fc1e2dc368c35010e54804cc` |
| `Challenge_multiplicative.lean` | `c59f827350ecc5bbff859d5b2d408608aa98fb5de2fff70cc6b60c17de01d9ee` |
| `core_logic_F_multiplicative.ath` | `1daf4018319393ce8e5f26dfec338d6313b36801f8c6242bc5f201b2778c800e` |

To check that the file you compile is the file cited:

```
sha256sum core_logic_is_not_paraconsistent.v core_logic_F_multiplicative.v \
          addendum_K_underivable.v negation_adequacy_supplement.v \
          core_logic_F_multiplicative.lean Solution.lean \
          Challenge.lean Challenge_multiplicative.lean \
          core_logic_F_multiplicative.ath
```

## Interactive verification in the browser

Every Coq file is also served as a self-contained waCoq page: the
source is embedded inline, the proof runs in the browser (`Alt+↓` and
`Alt+↑` to step, `Alt+Enter` to run to the cursor, `F8` for the goal
panel), and nothing needs to be installed. Nine pages, cross-linked by
a common navigation bar:

| Page | What it runs |
|---|---|
| [Additive certification](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_logic_is_not_paraconsistent.html) | the reference source, twelve theorems |
| [Multiplicative certification](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_logic_F_multiplicative.html) | the weakening-free reconstruction, closing on `no_dilution` |
| [Strictness of the lower bound](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/addendum_K_underivable.html) | `A ⊢ B → A` is underivable for distinct atoms |
| [Negation adequacy](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/negation_adequacy_standalone.html) | Part I plus the four adequacy experiments |
| [Fragment F](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_step1_fragment_F.html) | the language and the five rules |
| [DNS.1 and DNS.2](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_step2_dns1_dns2.html) | step 1: both rules are derivable in ℱ |
| [Invertibility](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_step3_invertibility.html) | step 2: DNS.1 is invertible at the decisive instance |
| [anti-DNS.1](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_step4_antidns.html) | step 3: the refutation rule and its Ł-correctness |
| [Contradiction](https://vidal-rosset.net/wacoq/node_modules/wacoq/examples/core_step5_contradiction.html) | step 4: `claim1_false` |

`wacoq-pages.sh` generates them. It is run from the directory holding
the `.v` files and takes one `file::label` pair per page. All pages
must be listed in a single call, since each navigation bar is built
from the argument list:

```
./wacoq-pages.sh \
  "core_logic_is_not_paraconsistent.v::Additive certification" \
  "core_logic_F_multiplicative.v::Multiplicative certification" \
  "addendum_K_underivable.v::Strictness of the lower bound" \
  "negation_adequacy_standalone.v::Negation adequacy" \
  "core_step1_fragment_F.v::Fragment F" \
  "core_step2_dns1_dns2.v::DNS.1 and DNS.2" \
  "core_step3_invertibility.v::Invertibility" \
  "core_step4_antidns.v::anti-DNS.1" \
  "core_step5_contradiction.v::Contradiction"
```

Each page carries the source inlined in a `<textarea>` and a fixed
`backend: 'wa'`; it deliberately omits `file_dialog` and
`data-filename`, because the earlier `?fn=` mechanism raced against
the scratchpad's `localStorage` restoration and could open on an empty
editor. Legacy `?fn=X.v` URLs are redirected `301` to the
corresponding `X.html`.

These pages are generated from the `.v` files and are not the
certified artefacts: if a source changes, the page must be regenerated
or it will silently fall behind. The waCoq installation is
intentionally frozen at 0.16.0 (Coq 8.16) — the pages are meant to
still run, unchanged, years from now.
