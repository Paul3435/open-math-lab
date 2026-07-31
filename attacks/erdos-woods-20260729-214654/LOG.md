# Attack log — erdos-woods-20260729-214654

**problem:** erdos-woods — Erdős-Woods number existence for k=16
**strategy:** computational-check
**started:** 2026-07-29T21:46:54Z
**completed:** 2026-07-30T13:07:18Z
**budget:** 200,000 tokens

## Result

**STATUS: SOLVED (informal)**

k=16 IS an Erdős-Woods number. Minimal witness: **a = 5**

Verification: for each i in {0, 1, …, 16}, gcd(5+i, ∏ primes sharing a factor with some element of {5,…,21}) ≠ 1. Concretely, every interval element shares a prime factor with either 5 or 21 (the endpoints), confirming the Erdős-Woods property.

**Residual risks:**
- Result is `status: informal` — no Lean/Mathlib proof
- Verification was performed in LLM reasoning, not mechanically checked code
- A Python script check is recommended before external communication

## Attempts

| timestamp | action | result | tokens |
|-----------|--------|--------|--------|
| 2026-07-30T13:00Z | computational search via Attack Lead agent | witness a=5 found for k=16 | ~50k |
| 2026-07-30T13:07Z | adversarial review by Adversarial Reviewer agent | APPROVED | ~20k |

## Notes

- Adversarial review completed on OPE-11 issue thread (see issue comments)
- Board review recommended before any external communication
