# LOG — OPE-462 weak-schur-ws2

| Time (local) | Step | Result |
|--------------|------|--------|
| 2026-08-25 | Wake issue_assigned OPE-462; harness checkout claimed | start |
| 2026-08-25 | Branch `ope/462-weak-schur-ws2` from `origin/scout/ope-458-next-shortlist` | done |
| 2026-08-25 | Read dossier + `SchurNumber.lean` / `VanDerWaerden.lean` structure | done |
| 2026-08-25 | Offline exhaustive 2-colour weak-Schur scan n=1..11 | n≤8 colourable; n≥9 not; n=8 witnesses `00101110`, `11010001` |
| 2026-08-25 | Pin `problems/weak-schur-ws2/STATEMENT.md` (x≠y; Fin+1; z≤n; not S(k)/partition) | done |
| 2026-08-25 | Author `ProofLab/WeakSchur.lean` (`HasMonoWeakSchur`, witness, gt/le/eq) | done |
| 2026-08-25 | Wire import in `ProofLab.lean` | done |
| 2026-08-25 | `lake env lean ProofLab/WeakSchur.lean` | EXIT=0 |
| 2026-08-25 | `lake build ProofLab` | green (Built ProofLab.WeakSchur) |
| 2026-08-25 | `#print axioms` audit | ws2_gt_7: propext, ofReduceBool, Quot.sound; ws2_le_8/eq_8: + Classical.choice |
| 2026-08-25 | Attack pack + ledger/catalog + PR | handoff |

## Offline probe (Python, Attack Lead re-derive)

Predicate: colouring of `{1..n}` valid iff no `1 ≤ x < y`, `z=x+y≤n` with
`c[x]=c[y]=c[z]` (x≠y pin; order x<y covers unordered pairs).

Result: colourable precisely for `n ≤ 8`. Length-8 valid bitstrings (only two,
complements): `00101110` and `11010001`.
