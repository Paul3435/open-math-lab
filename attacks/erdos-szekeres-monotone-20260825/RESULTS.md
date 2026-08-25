# RESULTS — erdos-szekeres-monotone (OPE-433)

## Verdict

**formalized** (formalize-only, known-classical). Full finite Erdős–Szekeres weak
monotone subsequence theorem, zero `sorry` / `admit` / custom `axiom`.

## Main theorem

`ProofLab.ErdosSzekeres.erdosSzekeres_monotone`

Any `f : Fin n → α` with `n ≥ (r-1)*(s-1)+1` has a weakly increasing subsequence
of length `r` or a weakly decreasing subsequence of length `s`
(`List.Sorted (· ≤ ·)` / `List.Sorted (· ≥ ·)`).

## Verify

```bash
cd proofs/lean-project
export PATH="$HOME/.elan/bin:$PATH"
lake env lean ProofLab/ErdosSzekeres.lean   # expect EXIT=0
lake build ProofLab                        # expect green
rg -n '\bsorry\b|\badmit\b|\baxiom\b' ProofLab/ErdosSzekeres.lean  # expect no matches
```

## Artifacts

| path | role |
|------|------|
| `proofs/lean-project/ProofLab/ErdosSzekeres.lean` | Lean proof |
| `proofs/lean-project/ProofLab.lean` | import wire |
| `problems/erdos-szekeres-monotone/STATEMENT.md` | weak-mono pin |
| `problems/erdos-szekeres-monotone/ATTACK_LOG.md` | session log |
| `catalog/problems/erdos-szekeres-monotone/DOSSIER.json` | Scout dossier (OPE-430) |
| `attacks/erdos-szekeres-monotone-20260825/` | STATUS + RESULTS |

## Claim

**No claim.** Default `mathforge claim prepare` → no claim. Board only for external communication.
