# Sun 1–3–5 four-square conjecture (open; live cash)

**id:** `sun-135`
**ticket:** OPE-1028 Scout bench #3 (board prize-money hunt)
**expected:** `open` — **no prize claim**
**cash:** US$1,350 — Zhi-Wei Sun (personal offer; PPL 006 “source-stated” from
the author’s prize slides). No deadline. PPL last checked 2026-07-27.
Slides URL recorded by PPL: https://maths.nju.edu.cn/~zwsun/Square-sum.pdf
(this Scout run: HTTP fetch of the PDF **failed**; do not treat the dollar
figure as escrowed. Re-confirm against the slides before any claim path.)
Computational report: J. Number Theory 2021, doi:10.1016/j.jnt.2021.01.003.

## What the prize is for

**Conjecture (Sun):** every nonnegative integer `n` can be written
`n = x² + y² + z² + w²` with nonnegative integers `x,y,z,w` such that
`x + 3y + 5z` is itself a square.

Lagrange four-square is classical and **already in Mathlib** — USE, do not
re-prove, do not cite as this gap. The extra linear-form-is-square constraint
is the open part.

## Why bench, not prime

Weaker than Krenn–Gu (no software-confirmable *finite open window* as clean as
`C(8)∈{2,3}`) and weaker than Hou–Zeng (fib+catalan infra is a closer mill;
Sun PDF not independently fetched this run). Still a named personal cash
offer on a Diophantine statement the lab *could* bounded-verify.

Mathlib v4.10.0 pin `a719ba5c3115`: ZERO `1-3-5 conjecture` / Sun four-square
with `x+3y+5z` square. Four-square theorem HIT as a **different** fact.

## Pinned convention (exact)

**v1 is bounded search, not the namesake prize.**

```
def Sun135 (n : ℕ) : Prop :=
  ∃ x y z w k : ℕ,
    n = x^2 + y^2 + z^2 + w^2 ∧ x + 3*y + 5*z = k^2

theorem sun135_le_N (N : ℕ) : ∀ n ≤ N, Sun135 n
```

**Level A (not labelled Sun):** `N≤50` (or similar) by search + `native_decide`
or explicit tuples. Zero `sorry`.

**Level B:** raise `N` with a Python verifier; compare to the 2021 JNT
computational report if the paper is in hand. Namesake `∀ n` **out of v1**.

## Landmines

1. Re-confirm $1,350 against Sun's slides before any cash language stronger
   than “PPL source-stated”. PDF fetch failed this run.
2. Do **not** re-prove Lagrange four-square / `sum_four_squares`.
3. Nonnegative `x,y,z,w` is load-bearing (PPL statement).
4. Not Legendre three-squares. Not Hou–Zeng. Not Krenn–Gu.
5. Do **not** claim $1,350. Do **not** email Sun.
6. Leave OPE-403 alone.

## Sources

- Prize Problem Ledger PPL 006, https://prizeproblems.org/problems/006/
- Zhi-Wei Sun prize slides (URL above; unverified this run)
- J. Number Theory computational report, doi:10.1016/j.jnt.2021.01.003
