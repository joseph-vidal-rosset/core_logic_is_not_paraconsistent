# Comparator certification (gold standard)

This directory lets anyone re-verify the Lean proof that Core Logic is
not paraconsistent with the Lean **Comparator**, at the "gold standard"
of the Lean reference manual: the candidate solution is checked against
a *trusted challenge* and replayed through two independently
implemented kernels — Lean's own and nanoda.

## Files

- `Challenge.lean` — the trusted statement: the language, the rules of
  the fragment `F`, and the conditional theorem `claim1_false`, with its
  proof left as `sorry`. This file is the *entire* trusted base of the
  check.
- `Solution.lean` — the candidate proof. Byte-identical to
  `../core_logic_is_not_paraconsistent.lean`.
- `lakefile.toml` — declares the two Lean libraries `Challenge` and
  `Solution`.
- `lean-toolchain` — pins Lean `v4.31.0-rc2`.
- `config.json` — comparator configuration: theorem `claim1_false`,
  permitted axioms `propext, Quot.sound, Classical.choice`, nanoda
  kernel enabled.

Challenge SHA256:
`f3b8542d785b97688e56d8d617b4bf69dbfab7ef6678fb35dbe4d9cfa6cbd222`

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

## Running

From this directory, as an unprivileged user, in a fresh checkout that
has never compiled `Solution.lean`:

```sh
export COMPARATOR_LANDRUN=/path/to/landrun
export COMPARATOR_LEAN4EXPORT=/path/to/lean4export
export COMPARATOR_NANODA=/path/to/nanoda_bin
COMP=/path/to/comparator

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" -E HOME="$HOME" \
  -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
  -E COMPARATOR_NANODA="$COMPARATOR_NANODA" \
  --working-directory "$(pwd)" \
  -- bash -c "lake env $COMP config.json"
```

## Expected result

```
'claim1_false' depends on axioms: [propext]
Nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

`claim1_false` depends on the single axiom `propext` (propositional
extensionality). In particular it uses **neither** `Classical.choice`
**nor** `Quot.sound`: the result is not classical.

(Note: `Classical.choice` and `Quot.sound` do appear in the comparator's
`Exporting #[...]` line. This is not a dependency of the theorem: Lean's
three foundational axioms are always exported as part of the kernel
baseline, whether or not a given theorem uses them. The authoritative
statement of what the proof uses is the `depends on axioms: [propext]`
line above.)
