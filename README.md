# Core Logic is not paraconsistent — Version 6

Machine-checked companion to the paper *A Proof in Coq that Core Logic
is not Paraconsistent* (arXiv:2606.05953, under review at the
Australasian Journal of Logic). Refutation-system version.

The argument, in one paragraph. DNS.1 is a derivable rule of the
fragment ℱ under both of its readings, and it is *invertible* at the
decisive instance in the minimal reading ℱ_𝐌: both the premiss sequent
`A, ¬A ⇒ B` and the conclusion sequent `(A→B)→B, ¬A ⇒ B` are
underivable there. Hence the refutation system with Claim 1 as its
only rejection axiom and anti-DNS.1 as its only refutation rule — in
the sense of Łukasiewicz, Tiomkin (1988) and Goranko (Studia Logica
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

## The certifications

The same twelve theorems, under the same names and the same block
structure (A–F), are certified in three proof languages with distinct
foundations, and corroborated computationally in a fourth:

| File | System | Foundation | Status |
|---|---|---|---|
| `core_logic_is_not_paraconsistent.v` | Coq | CIC | certification (reference source) |
| `core_logic_is_not_paraconsistent.lean` = `Solution.lean` | Lean 4 | CIC | certification (Comparator gold standard, dual kernel) |
| `core_logic_is_not_paraconsistent.ath` | Athena | polymorphic multi-sorted FOL, assumption-base semantics (LCF tradition) | certification |
| `core_logic_is_not_paraconsistent.pl` | SWI-Prolog | executable proof search | corroboration |

A proof that survives verbatim translation across foundationally
distinct proof languages is evidence that it lives in the inductive
structure of the calculus itself, not in the idiosyncrasies of one
assistant.

In every certification, *nothing is asserted for the argument*: the
only axioms are definitional (the inductive definitions of the
language, the derivations, and the refutation system). The two
commitments of Core Logic occur exclusively as hypotheses — as
antecedents of the final theorems.

## Coq (reference source)

`core_logic_is_not_paraconsistent.v` — Version 6, 560 lines. Depends
only on the standard library (`List`, `ListSet`). To check:

```
coqc core_logic_is_not_paraconsistent.v
```

The file ends with one `Print Assumptions` per theorem: each must
report `Closed under the global context` (the two final theorems
`claim1_false` and `claim1_false_at_0_1` are implications whose
antecedents are the two commitments, so nothing is assumed).

SHA256:
`18fec76a8aaaec0bb738c5394eec4f9faf6effa984a88f89422c1e12e7b14b74`

A word on `ListSet`, since a reader may suspect that it smuggles
something in. It does not: it is used for the type notation alone,
in the signatures of `derivable` and `refutable`, and `set A` is by
definition `list A`. No function of the module — `set_add`, `set_mem`,
`set_union` and the rest — occurs anywhere in the file, and none of
its decidability requirements is ever discharged. Two `grep` commands
establish this. The set-like reading of contexts is therefore
*nominal* here, never operational: no normalisation of contexts takes
place behind the notation, hence no hidden Contraction. The
multiplicative file reaches the same point by the other route, stating
set-like identity as a membership equivalence (`Set_eq`) rather than
as a data structure.

## Adequacy: the multiplicative certifications

The certification above reads the left implication rule L→ *additively*
(shared context). A referee may reasonably ask whether that reading is
what makes the result go through — that is, whether the encoding is
faithful to Core Logic ℂ rather than to a convenient neighbour of it.
It is not, and the question is settled mechanically rather than
argumentatively: the same statements are reconstructed under the
*multiplicative* reading of L→, with set-like contexts and no
monotonicity lemma whatsoever.

| File | System | SHA256 |
|---|---|---|
| `core_logic_F_multiplicative.v` | Coq 8.18, `List` only | `14c0aeca079cbceca344be0623e6fa3a97fa7316619e2983f2a437c61908005b` |
| `core_logic_F_multiplicative.lean` | Lean 4, no import at all | `1922f494af6a1e7ad12d229d9d4a0055d8756378b70b4381ec23bace3e78fff3` |
| `Challenge_multiplicative.lean` | Lean 4, fifteen statements left as `sorry` | `c59f827350ecc5bbff859d5b2d408608aa98fb5de2fff70cc6b60c17de01d9ee` |

To check that the file you compile is the file cited:

```
sha256sum core_logic_F_multiplicative.v \
          core_logic_F_multiplicative.lean \
          Challenge_multiplicative.lean
```

The structural choices are stated in the header of each file:
reflexivity at the singleton `[A] ⊢ A`, so no diluted `Ax`; left rules
with split contexts, the principal formula being consumed and the
premiss contexts being pieces of the conclusion's; and set-like
identity of contexts given by a membership *equivalence* (`Set_eq`),
not by a monotonicity rule — which makes Exchange and Contraction
pointless, in accordance with Tennant's own sequents. As in the
additive file, each theorem ends with `Print Assumptions` reporting
`Closed under the global context`, and no `exfalso` occurs.

### How to check the multiplicative pair

For Coq:

```
coqc core_logic_F_multiplicative.v
```

For Lean, in the browser, with nothing to install: open
[comparator.live.lean-lang.org](https://comparator.live.lean-lang.org),
paste `Challenge_multiplicative.lean` as the challenge and
`core_logic_F_multiplicative.lean` as the solution. The additive pair
is checked the same way, with `Challenge.lean` and
`core_logic_is_not_paraconsistent.lean`.

Unlike the additive pair, the multiplicative one has not been run
through the local two-kernel procedure described in the next section,
and this repository therefore ships no `config.json` for it. The
distinction is deliberate: what is claimed here is what has been
checked, and nothing more.

Three points make the two readings converge on the result:

1. **L→ is neutral here.** The multiplicative and additive readings
   coincide at every point at which the proof uses the rule: in both
   DNS cases the context is empty (Γ = ∅), so no split arises.
2. **R→ requires the additive reading, and Tennant requires it too.**
   Fidelity to ℂ demands vacuous discharge — Tennant's own diamond
   notation ◇ (*Core Logic*, 2017, pp. 159–163). This is not a
   concession to the encoding but a feature of ℂ.
3. **Nothing is smuggled in through the contexts.** The additive file
   uses `context_monotonicity` for bookkeeping only — to relocate a
   formula in a context, never as Weakening or Cut. The multiplicative
   file dispenses with it entirely, and closes with the theorem
   `no_dilution`: in that presentation weakening is not merely unused,
   it is unavailable.

Taken together, the two presentations bracket the fragment:
`multiplicative ⊆ ℱ_ℂ ⊆ additive`. The result holds at both bounds,
hence at every reading in between. No choice of structural convention
can be what produces `claim1_false`.

## Lean 4 — Comparator certification (gold standard)

This repository lets anyone re-verify the Lean proof that Core Logic is
not paraconsistent (refutation-system version, the arXiv/AJL appendix
file) with the Lean **Comparator**, at the "gold standard" of the Lean
reference manual: the candidate solution is checked against a
*trusted challenge* and replayed through two independently implemented
kernels — Lean's own and nanoda.

### Files

- `Challenge.lean` — the trusted statement: the language, the rules of
  the fragment `F` under its two readings, the refutation system
  `Refutable` (Claim 1 as the only rejection axiom, anti-DNS.1 as the
  only refutation rule, in the sense of Łukasiewicz, Tiomkin 1988 and
  Goranko, Studia Logica 53, 1994), and twelve theorems with their
  proofs left as `sorry`, matching the four steps of the paper:
  `DNS1_in_ℱ`, `DNS2_instantiated`,
  `DNS1_invertible_at_decisive_instance_in_ℱ_M`,
  `claim1_holds_in_ℱ_M`, `DNS1_conclusion_underivable_in_ℱ_M`,
  `anti_DNS1_holds_in_ℱ_M`, `refutation_system_Ł_correct_for_ℱ_M`,
  `refutation_system_Ł_incorrect_for_ℱ_ℂ`, `claim1_false`,
  `claim1_false_at_0_1`, `claim1_holds_in_ℱ_ℂ`,
  `anti_DNS1_Ł_incorrect_for_ℱ_ℂ`. This file is the *entire* trusted
  base of the check.
- `Solution.lean` — the candidate proof. Byte-identical to
  `core_logic_is_not_paraconsistent.lean` (Version 6).
- `lakefile.toml` — declares the two Lean libraries `Challenge` and
  `Solution`.
- `lean-toolchain` — pins Lean `v4.31.0-rc2`.
- `config.json` — comparator configuration: the twelve theorem names
  above, permitted axioms `propext, Quot.sound, Classical.choice`,
  nanoda kernel enabled.

Challenge SHA256:
`6147a4234a2420a420d2c67eb145ace7b3d9ec14fc1e2dc368c35010e54804cc`

Solution SHA256 (identical to `core_logic_is_not_paraconsistent.lean`):
`acddd04c222a9958aca2a998849e24b0b94b17c876e7ff3da832f6ac437701e1`

### Prerequisites

1. A Lean toolchain via [elan](https://elan.lean-lang.org).
2. The [comparator](https://github.com/leanprover/comparator) tool,
   built from a fresh checkout with `lake build lean4export comparator`.
3. [landrun](https://github.com/zouuup/landrun) (the build sandbox),
   compiled from source and reachable via `PATH` or `COMPARATOR_LANDRUN`.
4. [nanoda](https://github.com/ammkrn/nanoda_lib) (the second, Rust
   kernel), built with `cargo build --release`, reachable via
   `COMPARATOR_NANODA`.

The rationale for this procedure is given in the Lean reference manual,
*Validating a Lean Proof*:
https://lean-lang.org/doc/reference/latest/ValidatingProofs/

## Athena

`core_logic_is_not_paraconsistent.ath` — single file, pure ASCII,
faithful block by block (A–F) to the Coq source and to
`Solution.lean`. Unlike Coq and Lean, Athena is not based on type
theory: it is a polymorphic multi-sorted first-order framework with an
assumption-base semantics, in the LCF tradition (Arkoudas & Musser,
*Fundamental Proof Methods in Computer Science*, MIT Press, 2017).
Seventeen theorems: the twelve of the paper under the same names
(transliterated: `ℱ_𝐌` → `F-M`, `ℱ_ℂ` → `F-C`, `Ł` → `L`), plus the
same five auxiliary lemmas as in Coq (`absurdity-core`,
`context-monotonicity`, `DNS1-inversion-lemma`, `refut-inversion`,
`L-correct-aux`).

Design notes:

- **Zero axioms for the argument.** Every `assert` is definitional:
  datatype (free-generation) axioms and the defining biconditionals of
  `mem`, `well-formed`, `derivable`, `refut-wf`, `refutable` — the
  exact Athena counterparts of the Coq `Inductive` declarations. The
  two commitments (`Claim1-Tennant-hyp`, `anti-DNS1-rule-for-C-hyp`)
  are never asserted: they occur only as antecedents of `claim1-false`
  and `claim1-false-at-zero-one`.
- **Atoms are Peano naturals** (`datatype Atom := zero | succ`),
  mirroring `Var : nat -> formula` in the Coq source: the closed
  instance needs two *provably* distinct atoms, and
  `(zero =/= succ zero)` is a free-generation axiom of the datatype —
  the Athena counterpart of Coq's `discriminate`.
- **No Exchange rule.** The left rules locate their principal formula
  by membership (`mem`), exactly as `In _ Γ` does in Coq; the only
  structural fact used is `context-monotonicity`, proved by structural
  induction on reified derivations — not Weakening, not Cut.
- **Fully deterministic.** No call to automated provers: every step is
  a kernel step (`uspec`, `mp`, directed `chain` rewriting).
  Verification succeeds or fails independently of any resource limit,
  and loads in seconds.

To check: build Athena from the official sources
([github.com/AthenaFoundation/Athena](https://github.com/AthenaFoundation/Athena)),
either as the MLton native binary or as an SML/NJ heap image
(`sml scripts/make_smlnj_binary.sml`), then load the file:

```
athena core_logic_is_not_paraconsistent.ath
```

Expected output: seventeen `Theorem` reports, no evaluation error. The
file has been cross-validated on two independently built runtimes of
the same kernel sources: the MLton native binary (v1.6.1, the one
serving [athena.vidal-rosset.net](https://athena.vidal-rosset.net))
and an SML/NJ heap image.

## SWI-Prolog (computational corroboration)

`core_logic_is_not_paraconsistent.pl` — a self-contained, executable
model of fragment ℱ: it *searches* for derivations, constructs
explicit proof trees, and renders them in LaTeX (bussproofs) for every
result of the paper, one user command per section. It runs with a
local SWI-Prolog (`swipl core_logic_is_not_paraconsistent.pl`) or
without any installation on
[SWI-Tinker](https://swi-prolog.org/wasm/tinker). Its epistemic status
is stated in its header: corroboration, not certification — proof
*search* exhibits witnesses; the three certifications above check
proofs.

## Interactive verification in the browser

Every Coq file in this repository is also served as a self-contained
waCoq page on [coq.vidal-rosset.net](https://coq.vidal-rosset.net):
the source is embedded inline in the page, the proof runs in the
browser (`Alt+↓` to step forward), and no installation is required.

`wacoq-pages.sh` — the shell script that generates and updates those
pages — is included here for reproducibility. From a directory
containing the `.v` files:

```
bash wacoq-pages.sh
```

It produces one standalone `.html` per `.v` file, each with the Coq
source inlined in a `<textarea>`, a fixed `backend: 'wa'`, and a
navigation bar cross-linking the whole set (current page in bold). It
deliberately omits `file_dialog` and `data-filename`: the earlier
`?fn=` mechanism raced against the scratchpad's `localStorage`
restoration and could open on an empty editor. Legacy `?fn=X.v` URLs
are redirected `301` to the corresponding `X.html`.

The waCoq installation is intentionally frozen at 0.16.0 (Coq 8.16).
These pages are certification artefacts, not a playground: their value
is that they will still run, unchanged, years from now.
