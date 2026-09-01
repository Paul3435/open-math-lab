# Mason–Stothers theorem (polynomial ABC) (formalize-only)

**id:** `mason-stothers`
**ticket:** OPE-870 Scout RECOMMENDED PRIME (Director OPE-869; post erdos-ramsey-lower #94 + zsigmondy-theorem #95)
**expected:** known-classical (Stothers 1981 / Mason 1984; Snyder AMM 2000 Wronskian proof) — **no novelty claim**

## Why not classical / why formalize-only

Settled polynomial algebra: if `a, b, c` are coprime
polynomials over a characteristic-zero algebraically closed
field, not all constant, and `a + b = c`, then

`max(deg a, deg b, deg c) + 1 ≤ n₀(abc)`

where `n₀(f)` is the number of distinct roots of `f` in the
ground field (equivalently `f.roots.toFinset.card` once `f`
splits). Completely classical. The textbook corollary is
*polynomial Fermat*: `a^n + b^n = c^n` with `n ≥ 3` and
`gcd(a,b)=1` forces `a, b` constant.

Not an open problem. Not a novelty claim. **Not** the
integer *abc* conjecture (open — refuse). **Not**
number-theoretic FLT (Wiedijk #33; out of v1). **Not**
Descartes rule of signs (consumed #91 honest Level A —
coeff sign changes, a **different** theorem). **Not**
Sturm / Budan–Fourier / Gauss–Lucas (Descartes leftover
class; banned). **Not** combinatorial Nullstellensatz
(consumed #71). **Not** Schwartz–Zippel / Alon–Füredi
(CNS leftover-risk; banned). **Not** Zsigmondy / Bang /
LTE / full `a^n−b^n` / Artin (consumed #95 honest Level A
and its leftover class).

Mathlib v4.10.0 already has the **Wronskian this theorem
needs**:

- `Polynomial.wronskian` / `wronskian_eq_of_sum_zero`
  (`W(a,b)=W(b,c)` when `a+b+c=0`) /
  `degree_wronskian_lt_add` /
  `natDegree_wronskian_lt_add`
  (`RingTheory/Polynomial/Wronskian.lean`, authors Baek–Lee
  2024 — **infra only**, TODO is n-tuple Wronskian, **not**
  Mason–Stothers)
- `Polynomial.derivative` / `eval` / `IsRoot` / `roots`
  as a `Multiset` / `rootMultiplicity` / `natDegree`
- `Polynomial.Separable` `↔ IsCoprime f (derivative f)`
  (`FieldTheory/Separable.lean`)
- `IsAlgClosed` / `CharZero` / `IsCoprime`
- Eisenstein / rational-root / Gauss lemma /
  `cyclotomic.irreducible` / FTA `Complex.exists_root` /
  Newton identities / Lagrange interpolation /
  Chebyshev `T` — **already upstream. Different theorems.
  Never cite as this gap.**

There is **no** Mason–Stothers theorem, **no** polynomial
ABC, **no** `n₀(abc)` bound, and **no** named
`max deg + 1 ≤ distinct-root count` anywhere under
`Mathlib/` or `Archive/` (word-regexp `stothers` /
`MasonStothers` / `mason_stothers` this run → ZERO;
`wronskian` hits **only** `Wronskian.lean`, 34 matches,
no Mason). Do **not** import `Archive.*`.

OPE-853 considered-not-slotted did **not** slot this id
(the funded pair was Erdős–Ramsey + Bang/Zsigmondy). Both
of those are now **CONSUMED** (#94 namesake landed; #95
honest Level A partial). This is a **fresh** candidate,
**not** a Descartes leftover, **not** a Zsigmondy leftover,
**not** a third slot.

Mill NOW: univariate polynomial algebra after a
probabilistic-combinatorics prime (Erdős–Ramsey,
**CONSUMED** #94) and an elementary-NT leftover
(Zsigmondy, **CONSUMED** #95). Wronskian is waiting the
same way `cyclotomic.eval` waited for Zsigmondy and
`Polynomial.coeff` waited for Descartes. **Not a
rubber-stamp of Descartes rule of signs.**

Do **not** describe an attack as discovering polynomial
ABC. Do **not** expand into integer abc / Mordell /
Faltings / number-theoretic FLT. Do **not** prove Sturm /
Budan–Fourier / Gauss–Lucas / Niven cosine.

## Pinned convention (exact)

**v1 is the affine inequality** over an algebraically
closed field of characteristic zero. Encoding: Mathlib
`Polynomial.roots.toFinset.card` for `n₀`, Mathlib
`wronskian` as the engine.

Suggested pin:

```text
-- n₀(f) = number of distinct roots (alg. closed ⇒ splits)
def distinctRootCount {k : Type*} [Field k]
    (f : k[X]) : ℕ := f.roots.toFinset.card

-- Level A (not labelled Mason): Wronskian of coprime
-- non-proportional a, b is nonzero. Glue: wronskian_eq_of_sum_zero
-- for a + b + (-c) = 0.

-- Level B namesake
theorem mason_stothers {k : Type*} [Field k] [CharZero k]
    [IsAlgClosed k] {a b c : k[X]}
    (hsum : a + b = c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hcop : IsCoprime a b)
    (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0) :
    max a.natDegree (max b.natDegree c.natDegree) + 1
      ≤ distinctRootCount (a * b * c)
```

`CharZero` is load-bearing (separable / `f / gcd(f,f')`
squarefree). `IsAlgClosed` is load-bearing (`roots`
enumerates all geometric roots). `IsCoprime a b` is
load-bearing (pairwise coprimeness of `{a,b,c}` follows
from `a+b=c`). `hnonconst` is load-bearing (all-constant
counterexample: `1+1=2`, `n₀=0`). Prefer `+ 1 ≤ n₀` over
`≤ n₀ - 1` so `ℕ` subtraction is not load-bearing.

**Level A may land only** `wronskian a b ≠ 0` for coprime
non-constant-pair `a, b`, plus the already-upstream
`wronskian_eq_of_sum_zero` / `natDegree_wronskian_lt_add`
glue, **not** labelled Mason. Use the Wronskian file —
**do not re-prove degree of W**.

**Level B** is the namesake: `W(a,b)` is divisible by
high powers of the repeated roots, hence
`deg W + 1 ≤ n₀(abc)` together with
`max(deg a, deg b, deg c) ≤ deg a + deg b - 1 - (something)`
in Snyder's counting — pin Snyder AMM 2000, do not sorry
the namesake; honest partial is allowed (comment residual,
not `sorry`).

Optional cheap corollary (not labelled Mason, not required
for the namesake): polynomial Fermat `n ≥ 3`. **Not**
Wiedijk #33. Out of namesake if budget bites.

## Landmines

1. **Do not re-prove** `wronskian` / `wronskian_eq_of_sum_zero`
   / `degree_wronskian_lt_add` / `derivative` / `Separable` /
   Eisenstein / rational-root / Gauss lemma / FTA /
   Newton identities / Lagrange interpolation. Already
   Mathlib. Use them.
2. **This is not** Descartes rule of signs (consumed #91).
   Coeff sign changes ≠ distinct-root degree bound.
3. **This is not** Sturm / Budan–Fourier / Gauss–Lucas /
   Niven cosine. Descartes leftover class. Banned.
4. **This is not** combinatorial Nullstellensatz (consumed
   #71) / Schwartz–Zippel / Alon–Füredi. CNS leftover-risk.
5. **This is not** Zsigmondy / Bang / LTE / full `a^n−b^n`
   / Artin (consumed #95 and leftover class).
6. **This is not** integer abc / Mordell / Faltings /
   number-theoretic FLT (Wiedijk 33).
7. **This is not** `erdos-ramsey-lower` (consumed #94) or
   `expander-mixing` (the leftover). Do **not** assign the
   leftover first unless Director swaps.
8. **Do not re-prime** the consumed mill list
   (erdos-ramsey-lower / zsigmondy-theorem /
   descartes-rule-of-signs / e-irrational /
   n-fold-inclusion-exclusion / wolstenholme-theorem /
   lovasz-local-lemma / korselt-carmichael / vosper /
   heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / CNS / kk / oddtown /
   cayley / mycielski / friendship / havel / menger /
   greedy / Brooks / Dilworth / Eulerian / König / Dirac /
   EKR).
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Snyder)

Level A: if `IsCoprime a b` and not both constant then
`a, b` are linearly independent over `k`, so
`wronskian a b ≠ 0`. For `a+b=c`,
`wronskian a b = wronskian b (-c)` via
`wronskian_eq_of_sum_zero`. **Not** labelled Mason.

Level B: Snyder AMM 2000 — `W(a,b)` vanishes at repeated
roots of `abc` to one less than the multiplicity, so
`deg W + 1 ≤ n₀(abc)`; combined with
`deg W < deg a + deg b` and `deg c ≤ max(deg a, deg b)`
under `a+b=c` this is the namesake. Cap two levels. No
integer abc. No Sturm.

## Canonical source (pin in this STATEMENT)

W. W. Stothers, *Polynomial identities and Hauptmoduln*,
Quart. J. Math. Oxford 32 (1981). R. C. Mason,
*Diophantine Equations over Function Fields*, LMS Lecture
Note Series 96, Cambridge 1984. Elementary Wronskian
proof: Noah Snyder, *An elementary proof of Mason's
theorem*, Amer. Math. Monthly 107 (2000) 827–830.
Compact form: Wikipedia *Mason–Stothers theorem* —
**v1 pins the affine `max deg + 1 ≤ n₀(abc)` over
`CharZero` + `IsAlgClosed`, coprime `a+b=c`, not all
constant.** Type pin: `Polynomial.roots.toFinset.card`.
Wronskian.lean / Descartes / CNS / Zsigmondy are
**different** statements, not this claim.

## Out of scope

- Integer abc conjecture (open)
- Number-theoretic FLT / Fermat n=3,4
- Descartes-B / Sturm / Budan–Fourier / Gauss–Lucas
- Schwartz–Zippel / Alon–Füredi / CNS re-prime
- Bang / Zsigmondy-B / LTE / Artin / full `a^n−b^n`
- Function-field Mordell / Faltings
- Re-primes listed above
- Novelty / external claim
