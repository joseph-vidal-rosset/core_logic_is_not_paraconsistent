# Core Logic is Not Paraconsistent

A short, machine-checked case against the paraconsistency claimed for
Neil Tennant's **Core Logic** (ℂ). Version 3 certifies a conditional
incompatibility result: Tennant's Claim 1 (A, ¬A ⊬ B, for distinct
atoms) and the transfer to ℂ of one single anti-DNS.1 antisequent
instance cannot both be maintained together with the rules of the
common fragment, since ℂ derives DNS.2 through its own rule R→core.
The anti-DNS.1 instance itself is not assumed: it is proved to be a
metatheorem of the shared minimal reading M, both via a focused
kernel F* in which DNS.1 is derivable and invertible, and directly,
by an invariant on contexts. The disputed transfer commitment is
displayed in the statement of the final theorem; nothing is
concealed in the trusted base. No primitive Exchange rule and no
universal transfer principle are postulated; weakening is proved
admissible.

## Formal verifications

| File | System |
|------|--------|
| `core_logic_is_not_paraconsistent.v`    | Coq / Rocq — all `Print Assumptions` closed |
| `core_logic_is_not_paraconsistent.lean` | Lean 4 — `[propext]` only, checked on 4.21.0, 4.31.0-rc2, 4.32.0 |
| `core_logic_is_not_paraconsistent.ath`  | Athena — certifies the earlier presentation, to be updated |
| `core_logic_is_not_paraconsistent.pl`   | SWI-Prolog — companion development, earlier presentation |

The `comparator/` directory contains the Challenge/Solution pair for
the Lean Comparator (four certified theorems; challenge SHA256
`30567c26411331afac2312b282d302437c9a359ced0e352eea3e2aef954f67ba`).

## License

Released under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
