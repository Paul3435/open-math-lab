# Results — Frobenius Level A (starter)

| Check | Outcome |
|-------|---------|
| C1 coprime pairs ≥20 | PASS (22/22 default run, b≤60) |
| C2 min=1 convention | implemented in script (document on full attack close) |
| C3 gcd>1 reject/branch | implemented in script |
| Lean | not started |
| Novelty / claim | **none** — classical theorem; process certificate only |

Verify:

```bash
python attacks/frobenius-coin-problem-20260804-222513/verify_frobenius.py
```

Residual risks: finite sample of pairs; ℕ edge cases; no Lean; do not generalize to ≥3 coins.
