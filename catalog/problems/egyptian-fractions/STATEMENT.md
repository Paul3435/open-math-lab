# Egyptian fraction expansions — formalize-only

**id:** `egyptian-fractions`
**ticket:** OPE-1278 Scout leftover slot #2 (parent OPE-1277;
post fine-wilf #144 + british-flag #145)
**expected:** known-classical (Fibonacci–Sylvester greedy:
every positive rational is a finite sum of distinct
unit fractions) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory: a positive
rational `a/b` is a finite sum of distinct unit
fractions `∑ 1/nᵢ`. The greedy (Fibonacci–
Sylvester) algorithm takes `n = ⌈b/a⌉` and
repeats on the remainder; it terminates.
Completely classical (Rhind papyrus practice;
Fibonacci 1202 / Sylvester 1880).

Not an open problem. Not a novelty claim.

**Not** Farey sequences (consumed #127;
adjacent reduced fractions `bc−ad=1` —
**different theorem**; do **not** revive
`farey_adjacent` / Stern–Brocot /
Calkin–Wilf / Ford circles). **Not**
`sum_totient` as namesake. **Not** Kraft /
McMillan / Huffman / Shannon (consumed #138;
prefix-free sums ≠ unit-fraction sums).
**Not** harmonic-series divergence (already
`tendsto_sum_range_one_div_nat_succ_atTop`).
**Not** Erdős–Straus `4/n = 1/x+1/y+1/z`
(open; residual of *this* id; do **not**
sorry Erdős–Straus). **Not** Platonic solids
(prime of this shortlist).

Mathlib v4.10.0 already has the **rational /
field infra this theorem needs**:

- `Rat` (`Data/Rat/Defs.lean`)
- `add_div` (Algebra/Field/Basic.lean L27)
- `one_div_mul_add_mul_one_div_eq_one_div_add_one_div`
  (Field/Basic.lean L48) — **not** namesake
- `inv_sub_inv` (Field/Basic.lean L195)
  telescoping `n⁻¹ − (n+1)⁻¹ = 1/(n(n+1))`
  — **not** namesake
- `Finset.sum`

There is **no** named Egyptian-fraction
theorem, **no** `egyptian` / `EgyptianFraction`
/ `unitFractionSum` / `sylvesterGreedy`
anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names).
Do **not** import `Archive.*`.

OPE-1263 shortlist is **CONSUMED**
(#144+#145). This is a **fresh** catalog-audit
leftover id, **not** a Farey leftover
continuation, **not** a Kraft leftover,
**not** a Fine–Wilf leftover, **not** a
British-flag leftover, **not** a prize
leftover, **not** a Formalist Level B
revival, **not** a third slot.

Mill NOW: finite unit-fraction sums leftover
beside Platonic solids (Schläfli arithmetic).
`Rat` + `inv_sub_inv` are waiting the same
way `EuclideanSpace` waited for British flag.
**Not a rubber-stamp of Farey.** **Not a
rubber-stamp of Kraft.**

Do **not** describe an attack as discovering
Egyptian fractions. Do **not** expand into
Erdős–Straus / Sylvester sequence / harmonic
series as extra namesakes (Erdős–Straus is
leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the unit-fraction-sum
predicate on named rationals: `1 = 1/1`,
a pure unit `1/n`, `3/4 = 1/2 + 1/4`, and
`2/3 = 1/2 + 1/6`, not labelled Egyptian.**
Distinct positive denominators are
load-bearing. `Rat` addition of `1/n` is
load-bearing.

Suggested pin:

```text
-- Level A (not labelled Egyptian):
-- 1 = 1/1; 1/n; 3/4 = 1/2+1/4; 2/3 = 1/2+1/6.

def unitSum (denoms : Finset ℕ) : ℚ :=
  denoms.sum fun n => (1 : ℚ) / n

def Egyptian (denoms : Finset ℕ) : Prop :=
  (∀ n ∈ denoms, 0 < n) ∧ denoms.Nonempty

theorem egyptian_one :
    unitSum {1} = 1

theorem egyptian_unit (n : ℕ) (hn : 0 < n) :
    unitSum {n} = (1 : ℚ) / n

theorem egyptian_three_four :
    unitSum {2, 4} = (3 : ℚ) / 4

theorem egyptian_two_three :
    unitSum {2, 6} = (2 : ℚ) / 3

-- optional extra telescoping
theorem egyptian_one_half_third_sixth :
    unitSum {2, 3, 6} = 1

-- Level B namesake (every positive rational; residual OK)
theorem egyptian_fractions (q : ℚ) (hq : 0 < q) :
    ∃ denoms : Finset ℕ, Egyptian denoms ∧ unitSum denoms = q
```

Finite named rationals are load-bearing.
`Finset` of denominators is load-bearing.
`Rat` `1/n` is load-bearing.

**Level A may land only** `1=1/1` / unit
`1/n` / `3/4=1/2+1/4` / `2/3=1/2+1/6`
(optional extra `1=1/2+1/3+1/6`), **not**
labelled Egyptian. Reuse Mathlib `Rat` /
`add_div` / `inv_sub_inv` / `Finset.sum`
— **do not re-prove** field arithmetic.

**Level B** is the namesake: every positive
rational is a finite sum of distinct unit
fractions (greedy termination). Do not sorry
the namesake; honest partial is allowed
(comment residual, not `sorry`). Erdős–Straus
/ Sylvester sequence are residual.

## Landmines

1. **Do not re-prove** `Rat` / `add_div` /
   `inv_sub_inv` / `Finset.sum` /
   `one_div_add_one_div`.
   Already Mathlib. Use them.
2. **This is not** Farey / Stern–Brocot /
   Calkin–Wilf / Ford circles (consumed #127).
   Different theorem (adjacent det vs unit
   sums). Do not cite as Egyptian.
3. **This is not** Kraft / McMillan / Huffman
   / Shannon (consumed #138). Prefix-free
   sum ≠ unit-fraction sum.
4. **This is not** harmonic-series divergence
   (already-in). Do not cite as Egyptian.
5. **This is not** Erdős–Straus. Open.
   Residual of this id. Do not sorry it.
6. **This is not** `platonic-solids`
   (OPE-1278 prime). Do not prove Platonic
   here.
7. **This is not** Fine–Wilf / British flag /
   lame / Wantzel.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Erdős–Straus conjecture (open)
- Sylvester sequence / greedy-length bounds
- Harmonic series as namesake
- Prize claims / Millennium / Beal
