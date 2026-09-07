# König's line-colouring theorem (bipartite χ' = Δ) — formalize-only

**id:** `bipartite-chromatic-index`
**ticket:** OPE-1095 Scout leftover slot #2 (parent OPE-1094; post ostrowski-q #109 + andrasfai-erdos-sos #108)
**expected:** known-classical (König 1916, bipartite edge-chromatic number) — **no novelty claim**

## Why not classical / why formalize-only

Settled graph theory: a finite bipartite graph is
class 1, i.e. its edge-chromatic number equals its
maximum degree (`χ' = Δ`). Equivalently, the edges
can be properly coloured with `maxDegree` colours.
Completely classical (Dénes König, 1916; often
called König's line-colouring theorem).

Not an open problem. Not a novelty claim.

**Not** König matching `ν = τ` (`konig-bipartite`,
PRs **#48+#50**, `konig_bipartite` already in
ProofLab — a **different** named theorem on
matchings vs vertex covers; USE matching infra;
do **not** re-prove `konig_bipartite`; do **not**
revive König matching). **Not** Vizing
(`χ' ∈ {Δ, Δ+1}` for general simple graphs — out
of v1). **Not** greedy vertex-colouring (#57).
**Not** Brooks. **Not** Hall SDR (already Mathlib
`hall_hard_inductive` — a **different** statement;
may USE). **Not** Tutte (Matching.lean TODO; not
one-wave). **Not** Ore (the prime). **Not** AES
Level B. **Not** ostrowski-q Level B.

Mathlib v4.10.0 already has the **matching / colouring
infra this theorem needs**:

- `SimpleGraph.Colorable` (`Coloring.lean` L127)
  — `Colorable 2` is the bipartite pin
- `SimpleGraph.maxDegree` (`Finite.lean` L343)
- `Subgraph.IsMatching` / `IsPerfectMatching`
  (`Matching.lean` L50 / L139)
- Hall marriage (`Combinatorics/Hall/Finite.lean`)
  — **different** SDR theorem; USE if needed, do
  not re-prove
- ProofLab `konig_bipartite` (`ν = τ`) — **different
  consumed theorem. Do not re-prove. Do not re-prime.**

There is **no** edge-colouring predicate, **no**
`chromaticIndex` / `EdgeColorable`, **no** Vizing,
and **no** bipartite `χ' = Δ` theorem anywhere under
`Mathlib/` or `Archive/` (word-regexp `chromaticIndex`
/ `EdgeColorable` / `vizing` / `edge_color` this run
→ ZERO). Matching.lean TODOs Tutte and a
graph-form Hall, **not** this line-colouring theorem.
Do **not** import `Archive.*`.

OPE-1078 shortlist is **CONSUMED** (#108+#109).
This is a **fresh** leftover, **not** a König-matching
leftover continuation, **not** a Brooks leftover,
**not** a Vizing hunt, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a third
slot.

König matching's own STATEMENT listed `χ' = Δ` as a
**different** theorem (“Not `χ'=Δ`”). This run
introduces that theorem under a new id. **Not a
rubber-stamp of `konig_bipartite`.**

Mill NOW: finite bipartite edge-colouring leftover
after an Ore Hamiltonian prime — `Colorable 2` +
`maxDegree` + `IsMatching` are waiting the same way
`IsHamiltonian` waits for Ore.

Do **not** describe an attack as discovering König.
Do **not** expand into Vizing / list-edge-colouring /
class 2 graphs as extra namesakes (leftover-risk of
*this* id). Do **not** re-prove König matching /
Hall / greedy / Brooks.

## Pinned convention (exact)

**v1 is the bipartite `χ' ≤ Δ` theorem only**
(together with the trivial `Δ ≤ χ'`). Encoding: a
ProofLab `EdgeColorable` predicate on `G.edgeSet`
(Mathlib has no line-graph / chromatic-index yet —
**one new def**, not a theory gap). Bipartite pin
is Mathlib `Colorable 2`.

Suggested pin:

```text
-- Level A (not labelled König): EdgeColorable
-- encoding; a matching is EdgeColorable 1; a star
-- is EdgeColorable Δ; Δ ≤ χ' is trivial. Not
-- labelled König.

def EdgeColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  ∃ f : G.edgeSet → Fin n,
    ∀ ⦃e₁ e₂ : G.edgeSet⦄, e₁ ≠ e₂ →
      (∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)) →
        f e₁ ≠ f e₂

-- Level B namesake
theorem konig_edge_chromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : G.Colorable 2) :
    EdgeColorable G G.maxDegree
```

`Colorable 2` is load-bearing (odd cycles have
`χ' = Δ + 1`; `C₅` is the landmine). `Fintype V`
is load-bearing. `DecidableRel G.Adj` is
load-bearing (`maxDegree` / `edgeSet`).

**Level A may land only** the `EdgeColorable`
encoding + matching/star/trivial `Δ ≤ χ'` glue,
**not** labelled König. Reuse Mathlib `Colorable 2`
and matching vocabulary from consumed
`konig-bipartite` — **do not re-prove**
`konig_bipartite`.

**Level B** is the namesake: missing-colour
alternating path / matching at a vertex of degree
`Δ` colours the edges with `Δ` colours. Do not
sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Vizing for
general graphs is residual.

## Landmines

1. **Do not re-prove** `Colorable` / `maxDegree` /
   `IsMatching` / `konig_bipartite` / Hall /
   greedy / Brooks. Already Mathlib or consumed
   ProofLab. Use them.
2. **This is not** König matching `ν = τ` (#48+#50).
   Min-max ≠ chromatic index.
3. **This is not** Vizing (`χ' ≤ Δ+1` for general
   simple graphs). Out of v1. `C₅` shows why
   `Colorable 2` is load-bearing.
4. **This is not** greedy vertex-colouring / Brooks /
   AES / Mycielski / 4CT / list-colouring.
5. **This is not** Tutte (Matching.lean TODO; not
   one-wave this mill).
6. **This is not** `ore-hamiltonian` (the prime).
   Do **not** assign this leftover first unless
   Director swaps.
7. **This is not** ostrowski-q Level B /
   andrasfai-erdos-sos Level B / Dirac leftover /
   krenn-gu / hou-zeng-pfc / sun-135. Do not revive.
8. **Do not re-prime** the consumed mill list
   (ostrowski-q / andrasfai-erdos-sos /
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
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: encode a proper edge-colouring as a map
on `edgeSet` that separates edges sharing a vertex.
A matching uses 1 colour; a star uses `Δ` colours;
any proper colouring needs `≥ Δ` colours. **Not**
labelled König.

Level B: given `Colorable 2`, colour greedily and
repair a missing colour at a vertex via an
alternating path in two colours (or take a matching
of unsaturated edges). Cap two levels. No Vizing.
No `ν = τ` re-proof.

## Canonical source (pin in this STATEMENT)

D. König, *Über Graphen und ihre Anwendung auf
Determinantentheorie und Mengenlehre*, Math. Ann.
77 (1916) 453–465. Textbook: Diestel, edge-colouring
of bipartite graphs (`χ' = Δ`). Compact form:
Wikipedia *König's theorem (graph theory)* — the
**line-colouring** form, **not** the matching
min-max. Type pin: Mathlib `Colorable 2` /
`maxDegree` + ProofLab `EdgeColorable`. Vizing /
König matching are **different** statements, not
this claim.

## Out of scope

- Vizing / class 2 / list-edge-colouring
- König matching `ν = τ` re-proof
- Tutte / Hall re-proof
- Ore / AES Level B / Ostrowski Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
