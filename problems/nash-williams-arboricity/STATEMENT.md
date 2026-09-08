# Nash–Williams arboricity theorem — formalize-only

**id:** `nash-williams-arboricity`
**ticket:** OPE-1157 Scout leftover slot #2 (parent OPE-1156; post singleton-bound #120 + hook-length #121)
**expected:** known-classical (Nash-Williams 1964) — **no novelty claim**

## Why not classical / why formalize-only

Settled extremal graph theory: the *arboricity*
`Υ(G)` of a finite simple graph `G` — the
minimum number of forests needed to partition
`E(G)` — equals

`max_H ceil( e(H) / (|V(H)| − 1) )`

over subgraphs `H` with at least two vertices
(Nash-Williams 1964). Equivalent packing form:
the edges of `G` partition into `k` forests
iff every subgraph `H` satisfies
`e(H) ≤ k (|V(H)| − 1)`. Completely classical.

Not an open problem. Not a novelty claim.

**Not** Cayley's formula for labelled trees
(consumed #64 informal leftover Prüfer) —
that is a **count**. USE `IsTree.card_edgeFinset`
as glue; do **not** re-prove Cayley; do **not**
revive Prüfer. **Not** Kirchhoff matrix-tree
(Cayley leftover **and** Cauchy–Binet leftover).
**Not** `IsAcyclic` / `IsTree`
(`Combinatorics/SimpleGraph/Acyclic.lean` L50 /
L54) — already Mathlib; that is the **forest
predicate**. USE it; do **not** re-prove
acyclicity. **Not** Moore / cages (#76).
**Not** KST (#73). **Not** Turán (already
`isTuranMaximal_iff_nonempty_iso_turanGraph`).
**Not** König edge-colouring (#112). **Not**
matroid union / graphic-matroid packing as
an extra namesake (residual of *this* id).

Mathlib v4.10.0 already has the **graph infra
this theorem needs**:

- `IsAcyclic` (Acyclic.lean L50; module doc:
  acyclic = forest)
- `IsTree` (L54) / `IsTree.card_edgeFinset` (L150)
- `induce` (`SimpleGraph/Maps.lean` L177)
- `edgeFinset` (`SimpleGraph/Finite.lean` L53)
- `completeGraph` (`SimpleGraph/Basic.lean` L144)
- `pathGraph` (`SimpleGraph/Hasse.lean` L94)
- `isAcyclic_bot` (Acyclic.lean L62)

There is **no** Nash–Williams arboricity
theorem, **no** named `nashWilliams` /
`NashWilliams` / `arboricity` / `IsForest`
(beyond the `IsAcyclic` synonym in the module
doc) anywhere under `Mathlib/` or `Archive/`
(word-regexp this run → ZERO). Do **not**
import `Archive.*`.

OPE-1142 shortlist is **CONSUMED** (#120+#121).
This is a **fresh** catalog-audit id, **not**
a Cayley leftover continuation, **not** a
hook-length leftover, **not** a Singleton
leftover, **not** a chromatic-index leftover,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite forest-packing leftover beside
BvN (doubly stochastic polytopes). `IsAcyclic`
is waiting the same way `stdBasisMatrix` waits
for BvN. **Not a rubber-stamp of `IsTree`.**

Do **not** describe an attack as discovering
Nash–Williams. Do **not** expand into matroid
union / branching-number / Nash–Williams for
directed graphs as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 is the undirected finite packing form
only.** Encoding: Mathlib `SimpleGraph` +
`IsAcyclic`. Count in `ℕ`.

Suggested pin:

```text
-- Level A (not labelled Nash-Williams):
-- empty / ⊥ is 0-forest (IsAcyclic);
-- a tree is 1-forest and e = n-1;
-- a path is a tree; a star is a tree;
-- a cycle needs 2 forests
-- (e = n, ceil(n/(n-1)) = 2);
-- K₂ is a tree. Not labelled Nash-Williams.

def IsForestPartition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ F : Fin k → SimpleGraph V,
    (∀ i, F i ≤ G ∧ (F i).IsAcyclic) ∧
    (∀ e ∈ G.edgeSet, ∃! i, e ∈ (F i).edgeSet)

-- Level B namesake
theorem nash_williams {V : Type*} [Fintype V]
    [DecidableEq V] [DecidableRel (· : SimpleGraph V).Adj]
    (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k) :
    IsForestPartition G k ↔
      ∀ s : Set V, 2 ≤ Fintype.card s →
        (G.induce s).edgeFinset.card ≤
          k * (Fintype.card s - 1)
```

`1 ≤ k` is load-bearing (`ℕ` subtraction).
Finite `V` is load-bearing. The max is over
induced subgraphs on `s` with `|s| ≥ 2`
(equivalent to all subgraphs: extra edges
only increase `e`). Partition of *edges*
is load-bearing (a cover by overlapping
forests is a different, weaker statement).

**Level A may land only** empty / bot /
tree `e = n-1` / `pathGraph` / star /
`completeGraph` on 2 vertices / cycle
2-forest glue, **not** labelled
Nash-Williams. Reuse Mathlib `IsAcyclic` /
`induce` / `edgeFinset` — **do not re-prove**
acyclicity or Cayley.

**Level B** is the namesake packing ↔
subgraph bound. Do not sorry the namesake;
honest partial is allowed (comment residual,
not `sorry`). Matroid union / directed
branching are residual.

## Landmines

1. **Do not re-prove** `IsAcyclic` / `IsTree` /
   `induce` / `edgeFinset` / `completeGraph` /
   `pathGraph`. Already Mathlib. Use them.
2. **This is not** Cayley labelled-tree count
   (#64). Different theorem. Do not revive
   Prüfer.
3. **This is not** Kirchhoff matrix-tree.
   Cayley leftover **and** Cauchy–Binet leftover.
4. **This is not** Turán / Mantel / KST / Moore.
5. **This is not** König edge-colouring (#112) /
   Vizing / Brooks / greedy. Colouring ≠ forest
   packing.
6. **This is not** matroid union / Edmonds
   packing / Nash–Williams for directed graphs.
   Residual of this id.
7. **This is not** Singleton (#120) /
   Hamming-bound / Plotkin / hook-length (#121) /
   Catalan / RSK / BvN / Gale–Ryser /
   `cauchy_binet` / `bollobas` / Ore / AES /
   ostrowski / krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
8. **Do not re-prime** the consumed mill list
   (hook-length / singleton-bound / cauchy-binet /
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
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: `⊥` is acyclic (`isAcyclic_bot`).
A tree has `e = n-1` (`IsTree.card_edgeFinset`)
and is already one forest. `pathGraph n` is
a tree for `n ≥ 1`. A star is a tree. `K₂`
is a tree. A cycle has `e = n` and
`ceil(n/(n-1)) = 2`; deleting one edge
leaves a path (1-forest) plus a leftover
edge (1-forest). **Not** labelled
Nash-Williams.

Level B: the subgraph bound is necessary
because a forest on `s` has `< |s|` edges.
Sufficiency is the Nash-Williams packing
(induct / greedy spanning-forest extraction).
Cap two levels. No Cayley re-proof. No
Kirchhoff. No matroid union.

## Canonical source (pin in this STATEMENT)

C. St. J. A. Nash-Williams, *Decomposition of
finite graphs into forests*, J. London Math.
Soc. 39 (1964) 12. Textbook: Diestel,
*Graph Theory*, §2.4 / arboricity. Compact
form: Wikipedia *Nash-Williams theorem*
(arboricity). Type pin: Mathlib `IsAcyclic` /
`induce` / `edgeFinset`. `IsTree` is a
**different** already-in predicate, used as
glue. Cayley is a **different** consumed
count.

## Out of scope

- Matroid union / Edmonds / directed branching as extra namesakes
- Kirchhoff / Cayley namesake / Prüfer
- Turán / KST / Moore / chromatic index
- Singleton (#120) / hook-length (#121) / BvN Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
