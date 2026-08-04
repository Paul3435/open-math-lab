# Attack log — frobenius-coin-problem (starter)

**Dir:** `attacks/frobenius-coin-problem-20260804-222513/`  
**Opened:** 2026-08-04  
**Issues:** OPE-21 (director intake) / OPE-22 (Attack Lead owns continuation)

## 2026-08-04 — Level A certificate scaffold

- Script: `verify_frobenius.py`
- Checks C1 coprime pairs (exact max non-rep = ab−a−b), C2 min=1 convention, C3 gcd>1 branch.
- Local run: `python attacks/frobenius-coin-problem-20260804-222513/verify_frobenius.py` → **RESULT: PASS** (22/22 coprime pairs in default bound).
- Status: **heuristic** compute only — not a proof, not claim-ready.
- Attack Lead (OPE-22): extend pairs, document C2/C3 output explicitly in RESULTS, optional Lean Level B.
