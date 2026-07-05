# Core Logic is Not Paraconsistent

A short, machine-checked proof that Neil Tennant's **Core Logic** (ℂ) is **not paraconsistent**: the paraconsistency claimed for ℂ cannot be sustained, since it would force *ex falso quodlibet*, against ℂ's own rationale. The argument uses neither Cut nor Weakening — only structural induction, which by definition admits no counterexample.


## Formal verifications

The same result is independently certified in three proof assistants, with a companion Prolog development:

| File | System |
|------|--------|
| `core_logic_is_not_paraconsistent.v`    | Coq / Rocq |
| `core_logic_is_not_paraconsistent.lean` | Lean 4 |
| `core_logic_is_not_paraconsistent.ath`  | Athena |
| `core_logic_is_not_paraconsistent.pl`   | SWI-Prolog |

`auto/` holds Coq build artefacts. `2026-05-01-core-logic-is-not-paraconsistent.org` is the org-mode source of the companion article, whose PDF is `2606.05953v1.pdf`.


## License

Released under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
