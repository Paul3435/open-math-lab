# Singleton bound (error-correcting codes) — formalize-only

**id:** `singleton-bound`
**ticket:** OPE-1142 Scout RECOMMENDED PRIME (parent OPE-1141; post cauchy-binet #117 + bollobas-two-families #118)
**expected:** known-classical (Singleton 1964) — **no novelty claim**

## Why not classical / why formalize-only

Settled coding theory: a nonempty finite code
`C ⊆ (Fin n → α)` over a finite alphabet `α`
with minimum Hamming distance `d ≥ 1` satisfies

`|C| ≤ |α| ^ (n - d + 1)`.

Completely classical (Singleton 1964; the
Singleton / MDS bound). Equality cases are
MDS codes and are residual of *this* id.

Not an open problem. Not a novelty claim.

**Not** `hammingDist` / `hammingNorm`
(`InformationTheory/Hamming.lean` L38 / L137)
— already Mathlib; that is the **metric**.
USE it as glue; do **not** re-prove the
Hamming metric; do **not** cite the metric
as the Singleton bound. **Not** the Hamming
sphere-packing bound (volume of balls;
residual of this id). **Not** Plotkin /
Gilbert–Varshamov / Elias / MRRW. **Not**
MacWilliams identities. **Not** Hamming
codes / Hamming bound as a namesake.
**Not** Reed–Solomon existence (MDS
examples out of v1). **Not** Kraft /
Shannon source coding. **Not** linear-code
rank-nullity (`LinearCode` ZERO this pin —
do not invent a whole coding-theory library
as extra namesakes).

Mathlib v4.10.0 already has the **Hamming
infra this theorem needs**:

- `hammingDist` (`InformationTheory/Hamming.lean` L38)
- `hammingNorm` (L137)
- `Fintype` / `Finset.card` / `Fin n`
- `Pi` types with `DecidableEq`

There is **no** Singleton bound, **no** named
`singleton_bound`, **no** `minimumDistance` of
a code, **no** `LinearCode`, **no** Plotkin /
Hamming / GV bound anywhere under `Mathlib/`
or `Archive/` (word-regexp `singletonBound` /
`SingletonBound` / `minimumDistance` /
`LinearCode` / `plotkinBound` / `hammingBound`
this run → ZERO). Do **not** import
`Archive.*`.

OPE-1125 shortlist is **CONSUMED** (#117+#118).
This is a **fresh** catalog-audit id, **not**
a Cauchy–Binet leftover continuation, **not**
a Bollobás leftover, **not** a Hamming-metric
re-proof, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third
slot.

Mill NOW: finite coding bound after
Cauchy–Binet (rectangular det) + Bollobás
(set-pairs). `hammingDist` is waiting the
same way `submatrix` waited for Cauchy–Binet.
**Not a rubber-stamp of the Hamming metric.**

Do **not** describe an attack as discovering
the Singleton bound. Do **not** expand into
Hamming / Plotkin / MDS existence /
Reed–Solomon as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 is the combinatorial Singleton inequality
only.** Encoding: Mathlib `hammingDist` on
`Fin n → α`. Count in `ℕ`.

Suggested pin:

```text
-- Level A (not labelled Singleton): empty C;
-- |C| ≤ 1 (vacuous min-dist, bound holds for
-- any d); d = 1 (bound is |α|^n = whole
-- space); whole space min-dist = 1 when
-- 1 < |α| and 0 < n; repetition code of
-- length n over Fin 2 has min-dist n.
-- Not labelled Singleton.

def minDist {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (C : Finset (Fin n → α)) : ℕ :=
  -- infimum of hammingDist x y over
  -- distinct x, y ∈ C; convention n+1
  -- when |C| ≤ 1.

-- Level B namesake
theorem singleton_bound
    {n : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (C : Finset (Fin n → α))
    {d : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      d ≤ hammingDist x y) :
    C.card ≤ Fintype.card α ^ (n + 1 - d)
```

`1 ≤ d` is load-bearing (`n + 1 - d` in `ℕ`
subtraction). Finite `α` and `Fin n` are
load-bearing. Distinct-pair quantification
is load-bearing (a singleton is allowed and
must not crash). Puncturing `d-1`
coordinates is the engine, not a second
theorem.

**Level A may land only** empty / singleton /
`d = 1` / whole-space min-dist / binary
repetition glue, **not** labelled Singleton.
Reuse Mathlib `hammingDist` — **do not
re-prove** the Hamming metric.

**Level B** is the namesake: the evaluation
map forgetting the last `d-1` coordinates
is injective on `C` (two distinct codewords
differ in ≥ `d` places, so they still differ
after dropping `d-1` coordinates). Hence
`|C| ≤ |α|^{n-(d-1)}`. Do not sorry the
namesake; honest partial is allowed (comment
residual, not `sorry`). Hamming /
Plotkin / MDS are residual.

## Landmines

1. **Do not re-prove** `hammingDist` /
   `hammingNorm` / `Fintype.card`. Already
   Mathlib. Use the metric.
2. **This is not** the Hamming metric.
   Different object (distance vs a bound
   on `|C|`).
3. **This is not** the Hamming
   sphere-packing bound. Volume of balls.
   Residual of this id.
4. **This is not** Plotkin / Gilbert–Varshamov /
   MacWilliams / Reed–Solomon / Hamming codes.
5. **This is not** Kraft / Shannon / Huffman.
6. **`1 ≤ d` is load-bearing** for `ℕ`
   subtraction.
7. **This is not** Cauchy–Binet (#117) /
   Bollobás (#118) / Kirchhoff / `cauchy_binet`
   / `bollobas` Level B.
8. **This is not** Ore / `konig_edge_chromatic`
   / AES / ostrowski / krenn-gu / hou-zeng-pfc
   / sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (cauchy-binet / bollobas-two-families /
   schwartz-zippel / hadamard-det /
   ore-hamiltonian / bipartite-chromatic-index /
   ostrowski-q / andrasfai-erdos-sos /
   noether-normalization / frobenius-real-division /
   mason-stothers / expander-mixing / zsigmondy /
   erdos-ramsey-lower / e-irrational / descartes /
   n-fold-inclusion-exclusion / wolstenholme /
   lovasz-local-lemma / korselt-carmichael / vosper /
   heron / euclid-euler / bipartite / moore /
   stirling / kst / pentagonal / sunflower / CNS /
   kk / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth /
   Eulerian / König / Dirac / EKR / Ramsey
   r33/r35/r333 / frobenius-coin-problem).
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: empty `C`, card `0`. Singleton:
vacuous min-dist, bound holds. `d = 1`:
right-hand side `|α|^n` is the whole space.
Whole space over `α` with `|α| > 1` and
`n > 0` has min-dist `1` via a one-coordinate
flip. Binary repetition of length `n` has
min-dist `n`. **Not** labelled Singleton.

Level B: puncture `d-1` coordinates.
If two codewords agreed on the remaining
`n-d+1` positions they would differ in at
most `d-1` places, contradicting min-dist
`d`. Injection into `α^{n-d+1}`. Cap two
levels. No Hamming-bound re-proof. No
Plotkin.

## Canonical source (pin in this STATEMENT)

R. C. Singleton, *Maximum distance q-nary
codes*, IEEE Trans. Inform. Theory 10 (1964)
116–118. Textbook: MacWilliams–Sloane,
*The Theory of Error-Correcting Codes*,
Ch. 1. Compact form: Wikipedia *Singleton
bound*. Type pin: Mathlib `hammingDist`.
The Hamming metric is a **different**
already-in definition, not this claim.

## Out of scope

- Hamming / Plotkin / GV / MDS existence as extra namesakes
- Linear codes / generator matrices / duals / MacWilliams
- Reed–Solomon / Hamming codes / BCH
- Cauchy–Binet (#117) / Bollobás (#118) Level B
- Kirchhoff / `cauchy_binet` / weighted Bollobás
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
