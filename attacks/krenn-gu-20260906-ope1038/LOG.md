# LOG — OPE-1038 krenn-gu Level B (8,3)

| Time (UTC) | Step | Result |
|------------|------|--------|
| 2026-09-06T21:40Z | Wake `issue_assigned` OPE-1038; harness checkout already claimed | start |
| 2026-09-06T21:40Z | `git fetch origin`; `origin/main` = `5bfc0ad`; KrennGu.lean on main | pin |
| 2026-09-06T21:41Z | Branch `ope/1038-krenn-gu-level-b` off `main` | done |
| 2026-09-06T21:41Z | Read STATEMENT Level B option 2 + `ProofLab/KrennGu.lean` encoding | reuse, not re-derive |
| 2026-09-06T21:48Z | Author `search_eqsystem.py` (ring `{-1,0,1}`; no Complex) | done |
| 2026-09-06T21:51Z | Run timeboxed search | see command |
| 2026-09-06T21:54Z | Search EXIT=0; 165.085s; no witness; tiny sets exhausted | honest stop |
| 2026-09-06T21:55Z | STATUS.json / RESULTS.md / ledger+catalog; PR; no merge | handoff |

## Command (honest stop)

```
python attacks/krenn-gu-20260906-ope1038/search_eqsystem.py \
  --timebox-83 120 --timebox-63 45 --seed 1038 \
  --out attacks/krenn-gu-20260906-ope1038/search_report.json
```

Stdout (verbatim):

```
SANITY_OK cycle d=2 for n=4,6,8
ARM signed 1-factors (8,3) until 120.0s
  1factors tried=143360 exhausted=True timeout=False witnesses=0 best=2
  cycle+1f tried=112 exhausted=True timeout=False witnesses=0 best=2
  local_mono restarts=48 steps=1182 witnesses=0 best=1
NO (8,3) witness on searched sets; fallback n=6 same ring
  n6 1factors tried=5120 exhausted=True timeout=False witnesses=0 best=1
  n6 cycle+1f tried=40 exhausted=True witnesses=0 best=1
  n6 local restarts=881 steps=22020 witnesses=0 best=1
STATUS exhausted OUTCOME no_witness_on_stated_finite_weight_sets elapsed 165.085
```

## Timebox

- `(8,3)` budget 120s. Did **not** explode. Tiny ±1 1-factor set finished inside
  the budget; mono hill-climb used the remainder and hit the wall.
- Fallback `(6,3)` 45s as specified when `(8,3)` produced no witness. Then stop.
- No second prime. No Lean nonexistence. No `sorry` of the namesake.
- Lake skipped (search log is the deliverable; Lean untouched).

## Stop

Clean negative on the stated finite weight-sets. Unrestricted `{-1,0,1}^{252}`
and `Complex` remain unsearched. Default no claim.
