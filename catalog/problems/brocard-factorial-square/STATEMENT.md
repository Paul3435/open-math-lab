# Brocard factorial-plus-one squares (4!+1=5² / 5!+1=11² / 7!+1=71², formalize-only)

**id:** `brocard-factorial-square`
**ticket:** OPE-1419 Scout leftover slot #2 (parent OPE-1418;
post simpson-paradox #171 + a4-klein-four #172)
**expected:** known-classical (Brocard 1876 / Ramanujan:
`n! + 1 = m²` holds for the pairs `(n,m) = (4,5), (5,11),
(7,71)`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary arithmetic on small factorials. Pin the
three classical witnesses (no `Rat` required):

- `4! + 1 = 5²` (24 + 1 = 25)
- `5! + 1 = 11²` (120 + 1 = 121)
- `7! + 1 = 71²` (5040 + 1 = 5041)

That conjunction *is* the Level A theorem. Completely
classical. The namesake “these are the only solutions in
positive integers” is a **different**, larger residual
(Brocard–Ramanujan; still open) — do **not** sorry it.

Not a prize hunt. Not a novelty claim. Not live cash.

**Not** Wilson (`wilsons_lemma` Wilson.lean L38 already-in:
`(p-1)! ≡ -1 (mod p)` for prime `p` — **different**
congruence; USE `Nat.factorial`, do **not** re-prove
Wilson, do **not** cite as Brocard). **Not** Euclid
infinitude of primes (`exists_infinite_primes`
Data/Nat/Prime/Basic.lean L82 already-in; the proof uses
`minFac (n ! + 1)` as a *prime-producing* gadget, **not**
as a square; USE factorial, do **not** re-prove infinitude,
do **not** cite Euclid as Brocard). **Not** Brocard points /
Brocard angle of a triangle (geometry name collision;
British-flag / Heron leftover cluster; do **not** sorry
Brocard points; do **not** label theorems `brocard_point_*`).
**Not** cannonball (consumed #154; pyramidal-square ≠
factorial-plus-one square; do **not** revive Lucas
uniqueness / Watson). **Not** taxicab-1729 (consumed #168;
two-cube sums ≠ factorial squares; do **not** revive Hardy /
Ramanujan / smallest-n — Ramanujan’s name here is the
Brocard–Ramanujan residual of *this* id, not taxicab).
**Not** euler-brick (consumed #169). **Not** Perfect /
amicable 220–284 / Euclid–Euler (consumed; `Perfect`
Divisors.lean L314 already-in glue). **Not** n-queens
(prime of this shortlist). **Not** simpson-paradox /
a4-klein-four (consumed #171+#172).

Mathlib v4.10.0 already has the **factorial / square infra
this theorem needs**:

- `Nat.factorial` (Data/Nat/Factorial/Basic.lean L29)
- scoped `n !` L34 / `factorial_succ` L43
- `pow_two` (Algebra/Group/Defs.lean L581)
- `IsSquare` (Algebra/Group/Even.lean L46) as square glue
  **not** namesake

There is **no** named `brocard` / `Brocard` /
`brocard_problem` / `factorial_plus_one_square` /
`BrocardRamanujan` theorem anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (this run → ZERO on those names;
`n ! + 1` hits only Euclid’s infinitude proof L82–84, a
different theorem). Do **not** import `Archive.*`.

OPE-1405 shortlist is **CONSUMED** (#171+#172). This is a
**fresh** catalog-audit leftover id, **not** a Wilson
leftover-revival, **not** a cannonball leftover, **not** a
taxicab leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite factorial-plus-one square witnesses leftover
beside n-queens small boards. `Nat.factorial` / `pow_two`
are waiting the same way `Nat` mul waited for Simpson.
**Not a rubber-stamp of Wilson.** **Not a rubber-stamp of
Euclid infinitude.**

Do **not** describe an attack as discovering Brocard.
Do **not** expand into uniqueness / only-three-solutions as
a sorry (that is leftover-risk of *this* id, and **open** —
do **not** sorry it). Do **not** label theorems `wilson_*`
/ `euclid_*` / `brocard_point_*` / `taxicab_*` as the
namesake.

## Pinned convention (exact)

**v1 Level A is named small factorial-plus-one squares:
`4!+1=5²` / `5!+1=11²` / `7!+1=71²`, not labelled Brocard /
Ramanujan / Wilson.** The three identities together are
load-bearing, so the theorem is **not** “some Nats square.”

Suggested pin:

```text
-- Level A (not labelled Brocard / Ramanujan / Wilson):
-- named factorial-plus-one square witnesses.

theorem brocard_four :
    Nat.factorial 4 + 1 = 5 ^ 2

theorem brocard_five :
    Nat.factorial 5 + 1 = 11 ^ 2

theorem brocard_seven :
    Nat.factorial 7 + 1 = 71 ^ 2

-- optional extra: 6!+1=721 is not a square
-- theorem brocard_six_not : ¬ ∃ k : ℕ, Nat.factorial 6 + 1 = k ^ 2

-- Level B namesake (only n=4,5,7; OPEN residual OK)
theorem brocard_factorial_square ...
    -- do not sorry the namesake
```

Named three-line identities are load-bearing.

**Level A may land only** the three equalities (optional
extra: `6!+1` not square), **not** labelled Brocard /
Ramanujan / Wilson. Reuse Mathlib `Nat.factorial` /
`pow_two` — **do not re-prove** Wilson / Euclid infinitude.

**Level B** is the namesake uniqueness (only 4,5,7). That
is **open**. Do not sorry it. Brocard points / Wilson primes
are extras residual.

## Out of v1 this ticket

- Uniqueness / only `n = 4,5,7` (OPEN)
- Wilson’s theorem as namesake
- Euclid infinitude as namesake
- Brocard points / Brocard angle
- Wilson primes `(p-1)! ≡ -1 (mod p²)`
- cannonball / taxicab / euler-brick leftover-revivals
- Perfect / amicable / Euclid–Euler leftover-revivals
- n-queens (prime of this shortlist)
- simpson-paradox / a4-klein-four leftover-revivals
- OPE-403 Happy Ending
- OPE-1195 lame-euclid leftover-status

## Claim

Default **no claim**. Formalize-only. No novelty.
