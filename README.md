# Comparator certification (gold standard) — Version 6

This directory lets anyone re-verify the Lean proof that Core Logic is
not paraconsistent (refutation-system version, the arXiv/AJL appendix
file) with the Lean **Comparator**, at the "gold standard" of the Lean
reference manual: the candidate solution is checked against a
*trusted challenge* and replayed through two independently implemented
kernels — Lean's own and nanoda.

## Files

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
  `../core_logic_is_not_paraconsistent.lean` (Version 6).
- `lakefile.toml` — declares the two Lean libraries `Challenge` and
  `Solution`.
- `lean-toolchain` — pins Lean `v4.31.0-rc2`.
- `config.json` — comparator configuration: the twelve theorem names
  above, permitted axioms `propext, Quot.sound, Classical.choice`,
  nanoda kernel enabled.

Challenge SHA256:
`6147a4234a2420a420d2c67eb145ace7b3d9ec14fc1e2dc368c35010e54804cc`

## Prerequisites

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
