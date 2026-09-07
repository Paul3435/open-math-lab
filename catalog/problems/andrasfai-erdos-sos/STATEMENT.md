# Andrásfai–Erdős–Sós theorem, triangle-free case (formalize-only)

**id:** `andrasfai-erdos-sos`
**ticket:** OPE-1078 Scout RECOMMENDED PRIME (parent OPE-1077; post noether-normalization #106 + frobenius-real-division #105)
**expected:** known-classical (Andrásfai–Erdős–Sós 1974, r=3 / triangle-free case) — **no novelty claim**

## Why not classical / why formalize-only

Settled extremal graph theory: a finite triangle-free
graph on `n` vertices with minimum degree `δ > 3n/5`
is bipartite. Equivalently (ℕ pin)
`5 * minDegree > 3 * n ⇒ Colorable 2`. Completely
classical (Andrásfai–Erdős–Sós 1974, the `r=3`
case of the general `K_r`-free form).

Not an open problem. Not a novelty claim.

**Not** Turán (already Mathlib
`isTuranMaximal_iff_nonempty_iso_turanGraph` —
max-edges, a **different** theorem; negative
control; never cite as this gap). **Not** Mantel
(Turán `r=2` corollary). **Not**
`bipartite-odd-cycle` (#79, `Colorable 2 ↔` no
odd closed walk — a **different** characterization;
USE the encoding, do not re-prove). **Not**
Mycielski (#65, unbounded chromatic number of
triangle-free graphs — the **opposite** direction).
**Not** Moore / cages / Hoffman–Singleton. **Not**
KST / Zarankiewicz. **Not** greedy / Brooks /
Vizing / 4CT. **Not** expander-mixing (#98).
**Not** frobenius-real-division Level B. **Not**
noether-normalization Level B.

Mathlib v4.10.0 already has the **graph infra this
theorem needs**:

- `SimpleGraph.CliqueFree` (`Clique.lean` L261)
  — `CliqueFree 3` is triangle-free
- `SimpleGraph.Colorable` (`Coloring.lean` L127)
  — `Colorable 2` is the bipartite pin used by
  `ProofLab/BipartiteOddCycle.lean`
- `SimpleGraph.minDegree` (`Finite.lean` L314)
- `Walk` / odd closed walks / `egirth` (Moore mill)
- Turán's theorem — **already upstream. Different
  theorem. Never cite as this gap.**

There is **no** Andrásfai–Erdős–Sós theorem, **no**
`δ > 3n/5 ⇒ bipartite` implication, and **no**
named degree-condition-for-bipartiteness anywhere
under `Mathlib/` or `Archive/` (word-regexp
`andrasfai` / `Andrásfai` / `three_n_div_five` /
`minDegree.*Colorable` this run → ZERO). Do **not**
import `Archive.*`.

OPE-1062 shortlist is **CONSUMED** (#105+#106).
This is a **fresh** catalog-audit id, **not** a
Frobenius leftover, **not** a Noether leftover,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite extremal-graph prime after two
algebra theorems (Frobenius real-division **CONSUMED**
#105; Noether normalization Level A **CONSUMED**
#106). `CliqueFree 3` + `Colorable 2` + `minDegree`
are waiting the same way `Quaternion` waited for
Frobenius and `adjMatrix` waited for expander
mixing. **Not a rubber-stamp of bipartite-odd-cycle.**
**Not Turán.**

Do **not** describe an attack as discovering AES.
Do **not** expand into the general `K_r`-free form
(`δ > (1 − 3/(3r−1))n ⇒ Colorable (r−1)`) as an
extra namesake (leftover-risk of *this* id).
Do **not** prove Turán / Mantel / Mycielski-C /
Brooks C / Vizing.

## Pinned convention (exact)

**v1 is the triangle-free / `r=3` case only.**
Encoding: Mathlib `CliqueFree 3` + `minDegree` +
`Colorable 2`. Inequality in `ℕ` (no `ℚ`).

Suggested pin:

```text
-- Level A (not labelled AES): shortest odd closed
-- walk in a non-2-colourable triangle-free graph
-- has length ≥ 5 and is an induced cycle; a vertex
-- off the cycle has ≤ 2 neighbours on it.

-- Level B namesake
theorem andrasfai_erdos_sos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3)
    (hδ : 5 * G.minDegree > 3 * Fintype.card V) :
    G.Colorable 2
```

`CliqueFree 3` is load-bearing (C5 is a landmine
without it). The strict `ℕ` inequality
`5 * minDegree > 3 * n` is load-bearing
(C5: `n=5`, `δ=2`, `5*2=10`, `3*5=15`, `10 ≯ 15`
— the theorem does **not** claim C5 is bipartite).
`Fintype V` is load-bearing. `DecidableRel G.Adj`
is load-bearing (`minDegree` needs it).

**Level A may land only** shortest-odd-cycle /
induced-C_{2k+1} / at-most-two-neighbours glue,
**not** labelled AES. Reuse `Colorable 2` and
odd-walk vocabulary from consumed
`bipartite-odd-cycle` — **do not re-prove**
`colorable_two_iff_no_odd_walk`.

**Level B** is the namesake: if not `Colorable 2`,
a shortest odd cycle C plus the degree hypothesis
contradicts `5δ > 3n` by double-counting edges
between C and V\C. Do not sorry the namesake;
honest partial is allowed (comment residual, not
`sorry`). General `K_r`-free AES is residual.

Optional cheap corollaries (not labelled AES, not
required): empty / edgeless; complete bipartite
balanced `δ = n/2` does **not** fire the hypothesis.
Out of namesake if budget bites.

## Landmines

1. **Do not re-prove** `CliqueFree` / `Colorable` /
   `minDegree` / `colorable_two_iff_no_odd_walk` /
   Turán / Mantel / Mycielski / Moore / greedy /
   Brooks. Already Mathlib or consumed ProofLab.
   Use them.
2. **This is not** Turán / Mantel (already Mathlib
   / corollary). Different theorem.
3. **This is not** `bipartite-odd-cycle` (#79).
   Characterization ≠ degree condition.
4. **This is not** Mycielski (#65). Unbounded χ of
   triangle-free graphs is the opposite direction.
5. **This is not** Moore / cages / Hoffman–Singleton
   / KST / Zarankiewicz / expander-mixing.
6. **This is not** greedy / Brooks C / Vizing / 4CT
   / Grötzsch / Hajós / Kneser.
7. **This is not** `ostrowski-q` (the leftover).
   Do **not** assign the leftover first unless
   Director swaps.
8. **This is not** frobenius-real-division Level B /
   noether-normalization Level B / krenn-gu /
   hou-zeng-pfc / sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (frobenius-real-division / noether-normalization /
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

## Proof sketch (classical, r=3)

Level A: if G is not `Colorable 2`, there is an odd
closed walk; a shortest one is an induced cycle C
of length `2k+1 ≥ 5` (no triangles). A vertex
outside C has at most two neighbours on C (else a
shorter odd cycle or a triangle). **Not** labelled
AES.

Level B: double-count edges between C and V\C.
The degree hypothesis forces too many such edges
for `k ≥ 2`. Cap two levels. No general `K_r`.
No Turán re-proof.

## Canonical source (pin in this STATEMENT)

B. Andrásfai, P. Erdős and V. T. Sós, *On the
connection between chromatic number, maximal clique
and minimal degree of a graph*, Discrete Math. 8
(1974) 205–218. Textbook: Diestel, *Graph Theory*,
the degree form of AES for triangle-free graphs.
Compact form: Wikipedia *Andrásfai–Erdős–Sós
theorem* — **v1 pins `CliqueFree 3` and
`5 * minDegree > 3 * n ⇒ Colorable 2`.** Type pin:
Mathlib `CliqueFree` / `Colorable` / `minDegree`.
Turán / bipartite-odd-cycle / Mycielski are
**different** statements, not this claim.

## Out of scope

- General `K_r`-free AES (`r ≥ 4`)
- Turán / Mantel re-proof (already Mathlib)
- Mycielski-C / Brooks C / Vizing / 4CT
- Frobenius / Noether Level B revival
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
