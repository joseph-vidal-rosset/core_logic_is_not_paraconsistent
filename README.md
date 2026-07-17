# Comparator certification (gold standard) — Version 5

This directory lets anyone re-verify the Lean proof that Core Logic is
not paraconsistent (refutation-system version) with the Lean
**Comparator**, at the "gold standard" of the Lean reference manual:
the candidate solution is checked against a *trusted challenge* and
replayed through two independently implemented kernels — Lean's own
and nanoda.

## Files

- `Challenge.lean` — the trusted statement: the language, the rules of
  the fragment `F` under its two readings, the refutation system
  `Refutable` (Claim 1 as the only rejection axiom, anti-DNS.1 as the
  only refutation rule, in the sense of Łukasiewicz, Tiomkin 1988 and
  Goranko, Studia Logica 53, 1994), and seven theorems with their
  proofs left as `sorry`:
  `DNS1_invertible_at_decisive_instance_in_ℱ_M`,
  `anti_DNS1_holds_in_ℱ_M`, `ℱ_ℂ_not_conservative_at_DNS1`,
  `refutation_system_Ł_correct_for_ℱ_M`,
  `refutation_system_Ł_incorrect_for_ℱ_ℂ`, `claim1_false`,
  `claim1_false_at_0_1`. This file is the *entire* trusted base of
  the check.
- `Solution.lean` — the candidate proof. Byte-identical to
  `../core_logic_is_not_paraconsistent.lean` (Version 5).
- `lakefile.toml` — declares the two Lean libraries `Challenge` and
  `Solution`.
- `lean-toolchain` — pins Lean `v4.31.0-rc2`.
- `config.json` — comparator configuration: the seven theorem names
  above, permitted axioms `propext, Quot.sound, Classical.choice`,
  nanoda kernel enabled.

Challenge SHA256:
`37f4edd7b9ba5fbea333e9df3d9a18a737d59e651c36609cc5112556f8947636`

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
