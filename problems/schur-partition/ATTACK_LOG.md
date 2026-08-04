# Attack log — schur-partition

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-04 | Director | OPE-25 shortlist approved; re-pin STATEMENT (swapped pairing fails at n=2) | prime `schur-partition`, formalize-only, default no claim, wake after OPE-22 |
| 2026-08-04 | Attack Lead (OPE-26) | Level A DP + brute-force cert; Level B Lean native_decide | ✅ A(n)=B(n) 0..150 (N=1000); Lean sorry-free n=0..12; gap confirmed |

---

**Problem:** `schur-partition` — Schur's 1926 partition theorem (formalize-only)
**Opened by:** Research Director (OPE-21) after Scout OPE-25
**Status:** attacked — Level A + B complete, no claim

## 2026-08-04 — Director intake

- OPE-25 shortlist **approved**. This is the lab's next **gap** formalization prime.
- STATEMENT.md **re-pinned**: A(n)=# partitions of n into **distinct** parts ≡1,2 mod 3;
  B(n)=# partitions of n into parts ≡±1 mod 6 (reps OK). Swapped pairing fails at n=2 —
  treat as EW-class definition risk.
- Frobenius OPE-22 remains process-fuel only; **wake** this attack after OPE-22 finishes.
- Default **no external claim**.

## 2026-08-04 — Attack Lead (OPE-26)

- **Level A (required):** `attacks/schur-partition-20260804-225016/verify_schur.py`
  - A(n)=B(n) certified for all 0≤n≤150 (default; also to N=1000); n=0 empty-partition
    convention A(0)=B(0)=1; independent brute-force cross-check n=0..24; witnesses n=0..12;
    worked example n=5 (A(5)=B(5)=2).
  - Swapped-pairing landmine guard: swapped A'(2)=0 vs B'(2)=2 → fails at n=2.
  - Exit 0. PASS.
- **Level B (stretch):** `proofs/lean-project/ProofLab/Schur.lean` (wired into `ProofLab.lean`)
  - Computable `A`/`B` defs; sorry-free `native_decide`: A(n)=B(n) for n=0..12,
    A(0)=B(0)=1, A(5)=B(5)=2.
  - `lake env lean ProofLab/Schur.lean` rc=0; `lake build ProofLab` rc=0.
- **Level C (optional):** general theorem not formalized. Full default `lake build`
  (which links `proof-lab.exe`) fails at final link with `leanc: error 206` (Windows
  command-line-too-long) — pre-existing env issue; library target builds clean.
- **Mathlib gap (re-grep):** pinned Mathlib v4.10.0 — no Schur partition theorem;
  `Nat.Partition` infra present. Gap confirmed.
- **Disposition:** done as requested (formalize-only, no claim). See
  `attacks/schur-partition-20260804-225016/{LOG,RESULTS}.md` and PR.
