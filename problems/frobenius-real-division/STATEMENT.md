# Frobenius theorem on real division algebras (formalize-only)

**id:** `frobenius-real-division`
**ticket:** OPE-886 Scout RECOMMENDED PRIME (Director OPE-885; post mason-stothers #97 + expander-mixing #98)
**expected:** known-classical (Frobenius 1878; Palais AMM 1968 elementary proof) — **no novelty claim**

## Why not classical / why formalize-only

Settled associative algebra: every finite-dimensional
division algebra `D` over `ℝ` is isomorphic, as an
`ℝ`-algebra, to exactly one of `ℝ`, `ℂ`, or `ℍ`
(Hamilton quaternions). Equivalently
`finrank ℝ D ∈ {1, 2, 4}` and the rank determines the
isomorphism type. Completely classical (Frobenius 1878).

Not an open problem. Not a novelty claim.

**Not** the Frobenius *coin* problem (already Mathlib
`frobeniusNumber_pair`; OPE-25 demoted; catalog
`frobenius-coin-problem` is **not** an unused Scout bet).
**Not** the Frobenius *endomorphism* `x ↦ x^q` in
characteristic `p`. **Not** Euclid–Euler even-perfect
(#80). **Not** Mason–Stothers (#97, univariate polynomial
ABC / Wronskian — a **different** algebra theorem).
**Not** Gelfand–Mazur (already Mathlib
`NormedRing.algEquivComplexOfComplete` — complex *Banach*
division algebras ≃ `ℂ`; analysis, infinite-dimensional
allowed; **different** theorem; USE as a different fact,
never cite as this gap). **Not** Artin–Wedderburn
(Mathlib `proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing`
— different theorem, too heavy, leftover-risk). **Not**
Hurwitz 1-2-4-8 composition algebras / octonions
(non-associative leftover class; banned as a leftover of
this id). **Not** Little Wedderburn (already Mathlib;
finite division rings are fields).

Mathlib v4.10.0 already has the **quaternion algebra this
theorem needs**:

- `Quaternion R` / `ℍ[R]` / `QuaternionAlgebra`
  (`Algebra/Quaternion.lean`) with
  `DivisionRing ℍ[R]` for a linear ordered field `R`
  (so `ℍ[ℝ]`), `Algebra R ℍ[R]`,
  `Quaternion.finrank_eq_four` (`finrank R ℍ[R] = 4`)
- `QuaternionAlgebra.Basis.lift` / `liftHom`
  (`Algebra/QuaternionBasis.lean`) — universal property
  for `ℝ`-algebra maps out of `ℍ[R,c₁,c₂]`
- `Complex` / `Algebra ℝ ℂ` /
  `Complex.finrank_real_complex` (`finrank ℝ ℂ = 2`)
- `FiniteDimensional` / `finrank` / `minpoly` /
  `DivisionRing` / `Algebra ℝ D`
- Gelfand–Mazur, Cayley–Hamilton, Jordan–Chevalley,
  spectral theorem, Little Wedderburn, Maschke,
  Jordan–Hölder — **already upstream. Different theorems.
  Never cite as this gap.**

There is **no** Frobenius classification of real division
algebras, **no** `finrank ∈ {1,2,4}` theorem for
`DivisionRing`+`Algebra ℝ`, and **no** named
`D ≃ₐ[ℝ] ℝ` / `ℂ` / `ℍ` trichotomy anywhere under
`Mathlib/` or `Archive/` (word-regexp `frobenius-real` /
`real division algebra` / `finrank.*1.*2.*4` this run →
ZERO). Do **not** import `Archive.*`.
Do **not** import `GroupTheory.SpecificGroups.Quaternion`
(that is the finite group `Q₈`, a **different** object).

OPE-870 considered-not-slotted did **not** slot this id
(the funded pair was Mason–Stothers + expander-mixing).
Both of those are now **CONSUMED** (#97 namesake landed;
#98 honest Level A + engine). This is a **fresh**
candidate, **not** a Mason leftover, **not** an expander
leftover, **not** a third slot, **not** a re-prime of
`frobenius-coin-problem`.

Mill NOW: associative real-algebra classification after a
univariate-polynomial prime (Mason–Stothers, **CONSUMED**
#97) and a spectral-graph leftover (expander-mixing,
**CONSUMED** #98). `ℍ[ℝ]` + `Basis.lift` +
`finrank_eq_four` are waiting the same way `wronskian`
waited for Mason and `adjMatrix` waited for expander
mixing. **Not a rubber-stamp of Mason–Stothers.**
**Not Gelfand–Mazur** (Banach / `ℂ`, already Mathlib).

Do **not** describe an attack as discovering the
classification of real division algebras. Do **not**
expand into octonions / Hurwitz composition / alternative
algebras / Banach Gelfand–Mazur re-proof. Do **not**
prove Artin–Wedderburn.

## Pinned convention (exact)

**v1 is the associative finite-dimensional classification
over `ℝ`.** Encoding: Mathlib `DivisionRing` +
`Algebra ℝ D` + `FiniteDimensional ℝ D`; targets
`ℝ`, `ℂ`, `ℍ[ℝ]`.

Suggested pin:

```text
-- Level A (not labelled Frobenius): dimension restriction.
-- Finite-dimensional real division algebras have rank 1, 2, or 4.
theorem real_division_finrank_one_two_four
    (D : Type*) [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] :
    finrank ℝ D = 1 ∨ finrank ℝ D = 2 ∨ finrank ℝ D = 4

-- Level B namesake
theorem frobenius_real_division
    (D : Type*) [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨
    Nonempty (D ≃ₐ[ℝ] ℂ) ∨
    Nonempty (D ≃ₐ[ℝ] ℍ[ℝ])
```

`FiniteDimensional ℝ D` is load-bearing (Gelfand–Mazur is
the Banach story without a finite-rank hypothesis).
`Algebra ℝ D` is load-bearing (`ℝ` sits in the centre).
Associativity is load-bearing (octonions out of v1).
`DivisionRing` (every nonzero is a unit) is load-bearing.

**Level A may land only** the rank trichotomy
`finrank ∈ {1,2,4}` (e.g. via minpoly of a non-real
element having degree 2, then a complementary `j` with
`j² = -1` and `ij = -ji`), **not** labelled Frobenius.
Use `Complex.finrank_real_complex` and
`Quaternion.finrank_eq_four` — **do not re-prove ranks of
`ℂ` and `ℍ`**.

**Level B** is the namesake: construct `AlgEquiv`s via
`Complex.lift` / `QuaternionAlgebra.Basis.lift`.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`).

Optional cheap corollaries (not labelled Frobenius, not
required): `finrank = 1 → D ≃ₐ[ℝ] ℝ`; commutativity
forces `ℝ` or `ℂ`. Out of namesake if budget bites.

## Landmines

1. **Do not re-prove** `Quaternion` / `DivisionRing ℍ[R]` /
   `finrank_eq_four` / `QuaternionAlgebra.Basis.lift` /
   `Complex.finrank_real_complex` / `minpoly` /
   Cayley–Hamilton / Jordan–Chevalley / Gelfand–Mazur /
   Little Wedderburn / Maschke / Jordan–Hölder.
   Already Mathlib. Use them.
2. **This is not** Gelfand–Mazur (already Mathlib;
   complex Banach division algebras). Different theorem.
3. **This is not** Mason–Stothers (#97) / Sturm /
   integer abc / FLT. Polynomial ABC ≠ division algebras.
4. **This is not** expander-mixing (#98) / Cheeger /
   Alon–Boppana / Wilf / Perron–Frobenius / Kirchhoff.
   Spectral leftover class. Banned.
5. **This is not** `frobenius-coin-problem` / Frobenius
   endomorphism / Euclid–Euler (#80).
6. **This is not** Artin–Wedderburn / Hurwitz 1-2-4-8 /
   octonions / alternative algebras. Leftover class of
   *this* id — do not invent as a leftover.
7. **This is not** `noether-normalization` (the leftover).
   Do **not** assign the leftover first unless Director
   swaps.
8. **Do not re-prime** the consumed mill list
   (mason-stothers / expander-mixing / erdos-ramsey-lower /
   zsigmondy-theorem / descartes-rule-of-signs /
   e-irrational / n-fold-inclusion-exclusion /
   wolstenholme-theorem / lovasz-local-lemma /
   korselt-carmichael / vosper / heron / euclid-euler /
   bipartite / moore / stirling / kst / pentagonal /
   sunflower / CNS / kk / oddtown / cayley / mycielski /
   friendship / havel / menger / greedy / Brooks /
   Dilworth / Eulerian / König / Dirac / EKR).
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Palais)

Level A: `ℝ ⊆ Z(D)`. If `D = ℝ`, rank 1. Otherwise take
`a ∉ ℝ`; `minpoly ℝ a` is irreducible degree 2, so `ℝ(a) ≃ ℂ`
and rank is even. If `D = ℝ(a)`, rank 2. Otherwise pick
`b` orthogonal to `ℝ(a)` under `(x,y) ↦ (x* star y).re`
(or Palais's elementary `b² = -1`, `ab = -ba`); the
span of `{1,i,j,ij}` is a copy of `ℍ`. A dimension count
rules out anything larger (a further element would
produce a zero divisor). **Not** labelled Frobenius.

Level B: package the copies as `AlgEquiv`s using
already-upstream `lift`. Cap two levels. No octonions.
No Gelfand–Mazur re-proof.

## Canonical source (pin in this STATEMENT)

F. G. Frobenius, *Über lineare Substitutionen und
bilineare Formen*, J. Reine Angew. Math. 84 (1878)
1–63. Elementary write-up: Richard S. Palais, *The
classification of real division algebras*, Amer. Math.
Monthly 75 (1968) 366–368. Compact form: Wikipedia
*Frobenius theorem (real division algebras)* —
**v1 pins associative finite-dimensional `D` over `ℝ`,
`D ≃ₐ[ℝ] ℝ` or `ℂ` or `ℍ[ℝ]`.** Type pin: Mathlib
`DivisionRing` + `Algebra ℝ` + `FiniteDimensional` +
`ℍ[ℝ]`. `NormedRing.algEquivComplexOfComplete` /
Mason–Stothers / expander-mixing are **different**
statements, not this claim.

## Out of scope

- Hurwitz composition algebras / octonions / 1-2-4-8
- Gelfand–Mazur re-proof (already Mathlib)
- Artin–Wedderburn / matrix rings over division rings
- Frobenius coin / Frobenius endomorphism
- Mason–Stothers leftover class (Sturm / abc / FLT)
- Expander leftover class (Cheeger / Alon–Boppana / Wilf)
- Novelty / external claim
