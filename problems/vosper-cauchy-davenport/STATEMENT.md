# Vosper's inverse Cauchy–Davenport theorem (formalize-only)

**id:** `vosper-cauchy-davenport`
**ticket:** OPE-788 Scout RECOMMENDED PRIME (support OPE-787; post bipartite #79 + Euclid–Euler #80)
**expected:** known-classical (Vosper 1956) — **no novelty claim**

## Why not classical / why formalize-only

Settled additive-combinatorics inverse theorem: if `A, B` are
nonempty finite subsets of `ℤ/pℤ` (`p` prime) and

```text
|A + B| = |A| + |B| - 1 < p
```

then `A` and `B` are arithmetic progressions with the **same**
difference. Not an open problem.

Mathlib v4.10.0 already has the **arithmetic this theorem needs**:

- `ZMod.min_le_card_add` (`Combinatorics/SetFamily/CauchyDavenport.lean`)
  — the **direct** Cauchy–Davenport theorem
  `|A+B| ≥ min(p, |A|+|B|-1)`. **Already upstream. Do not
  re-prove. Never cite CD as this gap.**
- `Finset` pointwise sum `s + t` (`Data/Finset/Pointwise.lean`)
- Dyson / pair e-transforms
  (`Combinatorics/Additive/ETransform.lean`):
  `addDysonETransform`, `mulDysonETransform.subset` /
  `.card` (cardinality invariance already proved)
- `ThreeAPFree` / Roth numbers
  (`Combinatorics/Additive/AP/Three/Defs.lean`) — **3-term
  AP-free sets**, a **different** predicate, **not** “`A` is
  itself an arithmetic progression”

There is **no** Vosper theorem, **no** `critical_pairs`, **no**
`isArithmeticProgression` / `IsAP` for a `Finset (ZMod p)`, and
**no** inverse-CD characterization anywhere under `Mathlib/` or
`Archive/` (word-regexp `vosper` / `critical pair` / `inverse
cauchy` this run → ZERO files). ProofLab has combinatorial
Nullstellensatz (Alon 1999 non-vanishing) — **different**
theorem. EGZ is **already Mathlib**. This is **not** a re-prime
of CNS, **not** Alon–Füredi / Chevalley–Warning / cap sets,
**not** Mann / Schnirelmann density, **not** Erdős–Heilbronn
(restricted sumsets), **not** additive Kneser (name collision
with banned graph-Kneser).

OPE-770 considered Vosper as a **fresh future candidate** and
did **not** slot it (leftover cap went to Euclid–Euler, now
**CONSUMED** as PR **#80**). This run is an **independent
re-eval**: gap+budget still hold; the mill reason for the skip
is gone. **Not a rubber-stamp.**

Do **not** describe an attack as discovering inverse theorems.
Do **not** expand into Mann / Schnirelmann / Heilbronn /
additive Kneser / Freiman `3k-4`.

## Pinned convention (exact)

**v1 is `ℤ/pℤ` only** (`p` prime), matching Mathlib
`ZMod.min_le_card_add`. Torsion-free / ordered-semigroup CD
already upstream are **different** theorems; do not inverse
those as this namesake.

**AP encoding is a new `IsAP` predicate**, not `ThreeAPFree`.
`IsAP s d` means `s` is a (possibly singleton) arithmetic
progression with difference `d`. Suggested pin:

```text
def IsAP {p : ℕ} (s : Finset (ZMod p)) (d : ZMod p) : Prop :=
  ∃ a, s = Finset.image (fun k : Fin s.card ↦ a + k.val • d) Finset.univ

theorem vosper
    {p : ℕ} [Fact p.Prime] {s t : Finset (ZMod p)}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hcard : (s + t).card = s.card + t.card - 1)
    (hlt : s.card + t.card - 1 < p) :
    ∃ d : ZMod p, IsAP s d ∧ IsAP t d
```

`Nonempty` + `hlt` already exclude `s = univ`. Singletons are
APs (any `d`); that is load-bearing, not a side case to drop.

**Level A may land only the direct extremal**: if `IsAP s d` and
`IsAP t d` then `(s+t).card = min p (s.card + t.card - 1)`.
**Not** labelled Vosper. Level B is the namesake inverse.

## Landmines

1. **This is not Cauchy–Davenport.** Already
   `ZMod.min_le_card_add`. Use it; do not re-prove it as this
   namesake. Never cite CD as a gap (OPE-25 class).
2. **This is not EGZ.** Already
   `Combinatorics/Additive/ErdosGinzburgZiv.lean`.
3. **This is not combinatorial Nullstellensatz.** Consumed PR
   **#71** (`ProofLab/CombinatorialNullstellensatz.lean`).
   CNS leftovers (Hilbert NS / Chevalley–Warning / EGZ /
   Alon–Füredi / cap sets) stay banned. Vosper is the **inverse
   of already-upstream CD**, a different named theorem.
4. **This is not Mann / Schnirelmann.** `schnirelmannDensity`
   *definition* is Mathlib; the density-subadditivity theorems
   are an explicit TODO — **different** mill, still fiddly
   infimum glue, **not** this id. Do not expand.
5. **This is not Erdős–Heilbronn** (restricted sumsets) and
   **not** additive Kneser (stabilizer form; name collision
   with banned graph-Kneser). Out of v1.
6. **`ThreeAPFree` is not `IsAP`.** Roth / 3-AP-free is a
   different predicate. Do not relabel it.
7. **Do not re-prime** bipartite-odd-cycle / euclid-euler-perfect
   / moore-degree-girth / stirling-second-kind / kovari-sos-turan
   / pentagonal-number-theorem / sunflower / combinatorial-nullstellensatz
   / kruskal-katona / oddtown / cayley-trees / mycielski /
   friendship / havel-hakimi / menger / greedy / Brooks /
   Dilworth / Eulerian / König / Dirac / EKR.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Vosper / e-transform)

Level A: if `s` and `t` are APs with the same difference `d`,
translate so `d = 1` and `s`, `t` are intervals; then `s+t` is
an interval of length `|s|+|t|-1`, or wraps to `univ` when that
exceeds `p`. **Not** labelled Vosper. Recovers equality in CD.

Level B: namesake `vosper`. Standard e-transform argument: if
`|s+t|` is critical and `< p`, apply Dyson / pair e-transforms
until one set is an interval (cardinality of the pair is
invariant; the sumset does not grow). Translate back. Cap two
levels. No Mann, no Heilbronn, no additive Kneser, no Freiman
`3k-4`.

## Canonical source (pin in this STATEMENT)

A. G. Vosper, *The critical pairs of subsets of a group of
prime order*, J. London Math. Soc. **31** (1956), 200–205.
Textbook: Tao–Vu, *Additive Combinatorics*, the inverse
Cauchy–Davenport theorem. Type pin: `Finset (ZMod p)` +
pointwise `+` + new `IsAP`. Cauchy–Davenport
(`ZMod.min_le_card_add`), EGZ, combinatorial Nullstellensatz,
and Schnirelmann density are **different** statements, not
this claim.

## Out of scope

- Re-proving Cauchy–Davenport / EGZ (already Mathlib)
- Mann / Schnirelmann density theorems
- Erdős–Heilbronn / additive Kneser / Freiman `3k-4`
- Alon–Füredi / Chevalley–Warning / cap sets (CNS leftovers)
- Odd-perfect / Lucas–Lehmer / Frobenius / Catalan
- Archive import
- Re-primes listed above
- Novelty / external claim
