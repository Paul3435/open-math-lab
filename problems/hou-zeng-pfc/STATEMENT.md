# Hou–Zeng: odd prime + Fibonacci + Catalan (open; live cash)

**id:** `hou-zeng-pfc`
**ticket:** OPE-1028 Scout leftover slot #2; OPE-1042 Director leftover approve; OPE-1043 Formalist Level A
**expected:** `open` — computationally verified to huge bounds; **no prize claim**
**cash:** US$1,000 for the first positive solution published in a well-known
mathematical journal; US$200 for the first explicit counterexample the sponsors
can verify by computer. Payers: Qing-Hu Hou and Jiang Zeng (personal offer,
recorded by Zhi-Wei Sun). No deadline. PPL 013 (source-stated, last checked
2026-07-27). OEIS A154404. arXiv:0901.3075.

## What the prize is for

**Conjecture (Hou–Zeng, 9 Jan 2009):** every integer `n>4` is a sum of an odd
prime, a positive Fibonacci number, and a Catalan number.

OEIS A154404 counts the representations; `a(n)>0` is the conjecture for
`n≥5`. Hou–Zeng verified to `5×10^8`. D. S. McNeil verified to `5×10^13`
(OEIS comment). A computer counterexample is therefore *possible in principle*
and would pay $200, but it is not a one-wave search target.

Sun arXiv:0901.3075 abstract states a *related* conjecture (`n = p + F_s + F_t`
with odd Fibonacci) — **different statement**. v1 is the Catalan form on
A154404 / PPL 013, not Sun's two-Fibonacci form.

## Why leftover, not prime

Mathlib v4.10.0 pin `a719ba5c3115`:

- HIT as infra: `Nat.Prime`, `Nat.fib` (`Data/Nat/Fib/Basic.lean`), `catalan`
  (`Combinatorics/Enumerative/Catalan.lean`).
- ZERO Hou–Zeng / A154404 / `prime + Fibonacci + Catalan` theorem.

One-wave **lab** progress is a bounded Lean/Python certificate (`n≤N`), same
shape as graceful-caterpillar / EW witness. That is machine-checkable and a
genuine Mathlib-gap *encoding*, but it does **not** win $1,000 (needs a journal
proof of all `n`) and is overwhelmingly unlikely to win $200 (search already
to `5×10^13`). Prefer Krenn–Gu as the prize prime: there the finite frontier
`(8,3)` is still actually open.

## Pinned convention (exact)

**v1 is bounded verify, not the namesake prize.**

```
theorem hou_zeng_le_N (N : ℕ) :
  ∀ n, 5 ≤ n → n ≤ N →
    ∃ p s t : ℕ, Nat.Prime p ∧ p ≠ 2 ∧
      n = p + Nat.fib s + catalan t
```

Pin `s ≥ 2` so Fibonacci is positive (`fib 0 = 0`, `fib 1 = fib 2 = 1`; OEIS
Maple in A154404 starts `Fibo(1)=1`, `Fibo(2)=2` — **landmine**: align with
`Nat.fib` vs OEIS indexing in the Lean docstring and a numerical table).
Catalan: Mathlib `catalan t` with `t ≥ 0` (`catalan 0 = 1`, `catalan 1 = 1`,
`catalan 2 = 2`).

**Level A (not labelled Hou–Zeng):** encoding + `n≤30` (or similar) via
`native_decide` / explicit witnesses. Zero `sorry`.

**Level B:** raise `N` with a Python verifier that matches Lean on the overlap
(`problems/hou-zeng-pfc/verify.py` if Attack writes one). Do **not** search
for a counterexample past published bounds as if it were new.

Cap two levels. Namesake `∀ n>4` is **out of v1**. Do **not** `sorry` it.

## Landmines

1. Fibonacci indexing vs OEIS Maple (`Fibo(2)=2` = `Nat.fib 3`). Pin and test.
2. Odd prime means `p ≠ 2`; `n=5 = 3+1+1` must work.
3. Do **not** swap in Sun's two-Fibonacci conjecture (`n=p+F_s+F_t`).
4. Do **not** claim $1,000 / $200. Do **not** email Hou or Zeng.
5. Catalan is **already in Mathlib** — USE, do not re-prove; do not cite as this gap.
6. Not Goldbach / weak Goldbach / Crocker prime+two-powers-of-two.
7. Not krenn-gu (the prime). Not sun-135 (the bench).
8. Leave OPE-403 alone.

## Sources

- OEIS A154404 (conjecture, verification bounds, prize note)
- Zhi-Wei Sun, arXiv:0901.3075 (records the Hou–Zeng prize terms)
- Prize Problem Ledger PPL 013, https://prizeproblems.org/problems/013/
