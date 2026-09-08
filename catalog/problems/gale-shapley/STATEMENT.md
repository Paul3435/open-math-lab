# Gale–Shapley stable matching — formalize-only

**id:** `gale-shapley`
**ticket:** OPE-1179 Formalist Level A (Scout OPE-1173 RECOMMENDED PRIME; Director OPE-1178; parent OPE-1172; post birkhoff-von-neumann #123 + nash-williams-arboricity #124)
**expected:** known-classical (Gale–Shapley 1962) — **no novelty claim**

## Why not classical / why formalize-only

Settled matching theory: given complete
preference rankings of `n` men for `n` women
and vice versa, there exists a *stable*
perfect matching — no unmatched pair who
both prefer each other to their assigned
partners (Gale–Shapley 1962; deferred
acceptance). Completely classical.

Not an open problem. Not a novelty claim.

**Not** Gale–Ryser (existence of (0,1)-matrices
with given margins) — that is a **different
Gale**, residual of consumed `birkhoff-von-neumann`
(#123). Do **not** revive Gale–Ryser. **Not**
Hall's marriage theorem
(`Combinatorics/Hall/Basic.lean`
`Finset.all_card_le_biUnion_card_iff_exists_injective`
L116) — already Mathlib; existence of *some*
perfect matching in `K_{n,n}` is trivial.
USE `Equiv.Perm` as the matching type; do
**not** re-prove Hall. **Not** König matching
`ν=τ` (consumed #48+#50). **Not**
`IsMatching` as namesake
(`SimpleGraph/Matching.lean` L50) — already
Mathlib; optional matching language only.
**Not** `Equiv.Perm.permMatrix`
(`LinearAlgebra/Matrix/Permutation.lean` L34)
— that is BvN glue. **Not** assignment-game
core / Hungarian optimality (BvN leftover-risk).

Mathlib v4.10.0 already has the **finite
permutation / matching infra this theorem
needs**:

- `Equiv.Perm` (`Logic/Equiv/Basic.lean`;
  `Perm.subtypeCongr` L520)
- `Function.Bijective`
- `SimpleGraph.Subgraph.IsMatching`
  (Matching.lean L50)
- `completeBipartiteGraph`
  (`SimpleGraph/Basic.lean` L153)
- `Fin n` / `Finset`

There is **no** Gale–Shapley theorem,
**no** named `galeShapley` / `GaleShapley` /
`stableMatching` / `StableMatching` /
`IsStableMatching` / `deferredAcceptance`
anywhere under `Mathlib/` or `Archive/`
(word-regexp this run → ZERO). Do **not**
import `Archive.*`.

OPE-1157 shortlist is **CONSUMED** (#123+#124).
This is a **fresh** catalog-audit id, **not**
a BvN leftover continuation, **not** a
Nash–Williams leftover, **not** a Gale–Ryser
revival, **not** a Hall leftover, **not** a
König leftover revival, **not** a prize
leftover, **not** a Formalist Level B
revival, **not** a third slot.

Mill NOW: finite preference-matching theorem
after BvN (doubly stochastic polytopes) +
Nash–Williams (forest partitions).
`Equiv.Perm` is waiting the same way
`stdBasisMatrix` waited for BvN. **Not a
rubber-stamp of Hall.**

Do **not** describe an attack as discovering
Gale–Shapley. Do **not** expand into
man-optimal uniqueness / rural hospitals /
strategy-proofness / stable roommates as
extra namesakes (leftover-risk of *this* id).

## Pinned convention (exact)

**v1 is existence of a stable perfect matching
on `Fin n`.** Rankings are functions to `Fin n`
(0 = most preferred). Count / bijection in
`ℕ`.

Suggested pin:

```text
-- Level A (not labelled Gale–Shapley):
-- n = 0 empty perm is stable; n = 1 unique
-- perm is stable; if everyone ranks their
-- μ-partner first then μ is stable; n = 2
-- explicit two-profile cases.
-- Not labelled Gale–Shapley.

abbrev Ranking (n : ℕ) := Fin n → Fin n → Fin n

def Prefers {n : ℕ} (rank : Ranking n)
    (a x y : Fin n) : Prop :=
  rank a x < rank a y

def Blocks {n : ℕ}
    (mRank wRank : Ranking n)
    (μ : Equiv.Perm (Fin n)) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
  Prefers mRank m w (μ m) ∧
  Prefers wRank w m (μ.symm w)

def IsStable {n : ℕ}
    (mRank wRank : Ranking n)
    (μ : Equiv.Perm (Fin n)) : Prop :=
  ∀ m w, ¬ Blocks mRank wRank μ m w

-- Level B namesake
theorem gale_shapley {n : ℕ}
    (mRank wRank : Ranking n)
    (hm : ∀ m, Function.Bijective (mRank m))
    (hw : ∀ w, Function.Bijective (wRank w)) :
    ∃ μ : Equiv.Perm (Fin n), IsStable mRank wRank μ
```

Finite `Fin n` is load-bearing. Completeness
of both sides' rankings (bijective rank
functions) is load-bearing. Incomplete lists
/ ties are a different theorem.

**Level A may land only** empty / `n = 1` /
partner-is-top-choice ⇒ stable / `n = 2`
explicit, **not** labelled Gale–Shapley.
Reuse Mathlib `Equiv.Perm` / `Function.Bijective`
— **do not re-prove** Hall, König `ν=τ`, or
`IsMatching`.

**Level B** is the namesake: existence via
deferred acceptance. Do not sorry the
namesake; honest partial is allowed
(comment residual, not `sorry`). Man-optimal
/ rural hospitals / strategy-proofness are
residual.

## Landmines

1. **Do not re-prove** `Equiv.Perm` /
   `Function.Bijective` / `IsMatching` /
   Hall / `completeBipartiteGraph`.
   Already Mathlib. Use them.
2. **This is not** Gale–Ryser / transportation
   margins (#123 residual). Different Gale.
   Do not revive.
3. **This is not** Hall's marriage theorem.
   Existence of a matching in `K_{n,n}` is
   trivial; stability is the content. Do not
   cite Hall as Gale–Shapley.
4. **This is not** König matching `ν=τ`
   (consumed). Do not revive König Level B.
5. **This is not** `Equiv.Perm.permMatrix`
   / Birkhoff–von Neumann (#123). Different
   use of `Equiv.Perm`.
6. **This is not** Nash–Williams arboricity
   (#124) / matroid-union residual.
7. **This is not** assignment / Hungarian /
   Shapley–Shubik index as extra namesakes.
8. **This is not** Singleton (#120) /
   hook-length (#121) / `cauchy_binet` /
   `bollobas` / Ore / `konig_edge_chromatic` /
   AES / ostrowski / krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (nash-williams-arboricity /
   birkhoff-von-neumann / hook-length /
   singleton-bound / cauchy-binet /
   bollobas-two-families / schwartz-zippel /
   hadamard-det / ore-hamiltonian /
   bipartite-chromatic-index / ostrowski-q /
   andrasfai-erdos-sos / noether-normalization /
   frobenius-real-division / mason-stothers /
   expander-mixing / zsigmondy /
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

Level A: `n = 0` empty permutation, no pair
to block. `n = 1` the unique map is stable.
If `μ m` is every man's unique rank-0 woman
and symmetrically, no blocking pair exists.
For `n = 2`, enumerate the (finitely many)
bijective ranking pairs and name a stable
`μ`. **Not** labelled Gale–Shapley.

Level B: deferred acceptance (men propose in
rounds; women keep the best so far; a rejected
man never re-proposes to that woman). The
terminal matching is perfect and stable.
Cap two levels. No rural hospitals. No
Gale–Ryser. No Hall re-proof.

## Canonical source (pin in this STATEMENT)

D. Gale and L. S. Shapley, *College admissions
and the stability of marriage*, Amer. Math.
Monthly 69 (1962) 9–15. Textbook: Knuth,
*Stable Marriage and its Relation to Other
Combinatorial Problems*; Gusfield–Irving,
*The Stable Marriage Problem*. Compact form:
Wikipedia *Gale–Shapley algorithm* /
*Stable marriage problem*. Type pin:
`Equiv.Perm` / `Fin n` / bijective rankings.
Hall is a **different** already-in theorem.
Gale–Ryser is a **different** consumed-mill
residual.

## Out of scope

- Man-optimal uniqueness / woman-pessimal
- Rural hospitals / many-to-one college admissions
- Strategy-proofness / Roth–Sotomayor lattice
- Stable roommates (incomplete, non-bipartite)
- Gale–Ryser / transportation / BvN Level B
- Hall / König `ν=τ` / `konig_edge_chromatic` Level B
- Nash–Williams (#124) Level B / matroid union
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
