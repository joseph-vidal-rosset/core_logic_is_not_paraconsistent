# Core Logic is Not Paraconsistent

A short, machine-checked case against the paraconsistency claimed for
Neil Tennant's **Core Logic** (ℂ).

The formalization considers one fragment ℱ — the four shared rules
Ax, L¬, R→, L→, with contexts as lists and left rules applying
extensionally through membership — under two readings: **ℱ_𝐌**, its
minimal reading, and **ℱ_ℂ**, its Core reading, which adds R→core.
Every rule of ℱ_𝐌 is a rule of ℂ; conservativity is a relation of ℂ
to its own kernel, so nothing foreign to Core is involved anywhere.

Version 4 certifies:

1. **DNS.1** is derivable uniformly in both readings (`DNS1_in_ℱ`).
2. The **anti-DNS.1 instance is a metatheorem of ℱ_𝐌 itself**
   (`anti_DNS1_holds_in_ℱ_M`), proved by a direct invariant on
   contexts — it is a mechanically certified fact, not an assumption.
3. **ℱ_ℂ is not conservative over ℱ_𝐌** at the DNS.1 instance
   (`ℱ_ℂ_not_conservative_at_DNS1`): DNS.2 is derivable in ℱ_ℂ
   through R→core while Claim 1 holds of the formalized fragment.
   The simplest certified witness of non-conservativity is
   ¬A ⊢ A → B (`non_conservativity_witness_*`).
4. The **conditional collision** (`claim1_false`): Tennant's Claim 1
   (restricted to distinct atoms) and the conservativity commitment
   at the DNS.1 instance — displayed as the explicit hypothesis
   `conservativity_at_DNS1` of the final theorem — jointly entail
   False, with a closed instance at atoms 0 and 1.

No primitive Exchange rule and no universal transfer principle are
postulated; weakening is proved admissible.

## Formal verifications

| File | System |
|------|--------|
| `core_logic_is_not_paraconsistent.v`    | Coq / Rocq 8.18 — all `Print Assumptions` closed |
| `core_logic_is_not_paraconsistent.lean` | Lean 4 — `[propext]` only, checked on 4.21.0, 4.31.0-rc2, 4.32.0 |
| `core_logic_is_not_paraconsistent.ath`  | Athena — certifies the earlier presentation, to be updated |
| `core_logic_is_not_paraconsistent.pl`   | SWI-Prolog — companion development, earlier presentation |

The `comparator/` directory contains the Challenge/Solution pair for
the Lean Comparator (four certified theorems; challenge SHA256
`2604e39526ad85b5497efdc9514f27c3774a47503dea76f97a20fa0f70bf70d9`).

## License

Released under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
