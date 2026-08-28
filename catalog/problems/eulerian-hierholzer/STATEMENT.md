# Euler's theorem — existence of Eulerian trails (Hierholzer) — formalize-only

**id:** `eulerian-hierholzer`
**ticket:** OPE-574 Scout recommended prime; OPE-579 Formalist Level A MERGED (PR #47); **OPE-591 Scout independently re-scored Level B** (support OPE-590)
**expected:** known-classical (Euler 1736 / Hierholzer 1873) — **no novelty claim**

## Why not classical / why formalize-only

Settled 18th-century sufficient condition for Eulerian trails, not an
open problem. Mathlib v4.10.0 `Combinatorics/SimpleGraph/Trails.lean`
already defines `Walk.IsEulerian` and proves the **necessary** degree
parity (`IsEulerian.card_odd_degree`: 0 or 2 odd-degree vertices). The
module TODO (L28–29) is exactly the **existence** direction: there
exists an Eulerian trail when that conclusion holds (plus connectivity).
Archive `Wiedijk100Theorems/Konigsberg.lean` is a **negative instance**
(a custom 4-vertex / 7-bridge graph is not Eulerian) — not the
existence theorem, and not Mathlib. Do not describe an attack as
discovering Euler's theorem.

## Pinned convention (exact)

Let `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`.
Write `oddDeg := { v : V | Odd (G.degree v) }`.

**Hypotheses:** `G.Connected` (Mathlib `SimpleGraph.Connected` =
`Preconnected` + `Nonempty V`).

**Claim (Euler / Hierholzer), two clauses:**

```text
-- circuit case
Fintype.card oddDeg = 0 →
  ∃ u : V, ∃ p : G.Walk u u, p.IsEulerian ∧ p.IsCircuit

-- trail case
Fintype.card oddDeg = 2 →
  ∃ u v : V, u ≠ v ∧ Odd (G.degree u) ∧ Odd (G.degree v) ∧
    ∃ p : G.Walk u v, p.IsEulerian
```

using Mathlib `Walk.IsEulerian` (`∀ e, e ∈ G.edgeSet → p.edges.count e = 1`)
and `Walk.IsCircuit`.

**Encoding pin:** Mathlib `SimpleGraph` + `Walk`. Do **not** roll a
custom multigraph / incidence-matrix Euler checker. Do **not** import
`Archive.Wiedijk100Theorems.Konigsberg`.

**v1-b (stretch, same heartbeat only if cheap):** the two clauses
packaged as one `∃ p, p.IsEulerian` with endpoints the odd-degree
vertices (or a circuit if none). Not required if the two lemmas land.

## Landmines

1. **Connectivity is load-bearing.** `card_odd_degree = 0 ∨ 2` is
   necessary but **not** sufficient: two disjoint copies of `C_4` have
   zero odd degrees and no trail covering every edge. Pin
   `G.Connected`. Do not transcribe the Trails.lean TODO literally
   without this hypothesis.
2. **Simple graphs, not Königsberg.** Classical Euler is often stated
   for multigraphs; Königsberg is a multigraph. Mathlib `SimpleGraph`
   has no parallel edges. The existence theorem still holds for simple
   graphs; the Archive Königsberg **counterexample** is out of scope
   (and already proved there). Do not claim to formalize Königsberg.
3. **Trail vs circuit vs path vs Hamiltonian.** Eulerian = every *edge*
   once. Hamiltonian (just closed in `ProofLab/Dirac.lean`) = every
   *vertex* once. Do not re-prime Dirac. `IsTrail` is weaker than
   `IsEulerian`.
4. **0 odd degrees ⇒ closed circuit**, 2 odd degrees ⇒ open trail
   between those two vertices. 1 odd degree is impossible by
   handshaking (`DegreeSum`). >2 odd degrees ⇒ no Eulerian trail
   (already in Mathlib as the necessary direction).
5. **Isolates vs Connected.** Degree-0 vertices are even. A connected
   graph cannot have extra isolated vertices, so `G.Connected` is the
   clean pin (slightly stronger than “the subgraph of positive-degree
   vertices is connected”). `K_1` (no edges) is connected; the nil
   walk is Eulerian.
6. **Finite is required** (`Fintype V`). Infinite Eulerian theory is
   out of scope.

## Proof sketch (classical, Hierholzer)

- All even degrees: start at any vertex, walk unused edges until stuck;
  stuck only at the start (parity); the trail is closed. If any edge
  remains, connectivity gives a vertex on the circuit incident to an
  unused edge; splice a new closed trail (circuit-merging). Induction
  on `|edgeSet|`.
- Two odd degrees: add a virtual edge between them (or start at one
  odd vertex); reduce to the even case; delete the virtual edge.

Partial: **Level A LANDED** (OPE-579 / PR #47 MERGED, do not re-prime):
`eulerian_k1` (`K_1` nil walk Eulerian), `eulerian_cycle`
(`n ≥ 3` ⇒ `C_n` Eulerian circuit + `G.Connected`), `eulerian_k2`
open trail. **Level B (OPE-597):** `eulerian_hierholzer_circuit`
(connected `G`, 0 odd degrees, nonempty `edgeSet`) +
`eulerian_complete_odd`. Trail clause (`card oddDeg = 2`) residual.
`IsCircuit` excludes the `K_1` nil walk (already in the Lean header).

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Eulerian.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

L. Euler, *Solutio problematis ad geometriam situs pertinentis*,
Commentarii academiae scientiarum Petropolitanae **8** (1736) 128–140.
Constructive proof pin: C. Hierholzer, *Über die Möglichkeit, einen
Linienzug ohne Wiederholung und ohne Unterbrechung zu umfahren*,
Math. Ann. **6** (1873) 30–32. Type pin: Mathlib
`SimpleGraph.Walk.IsEulerian` / `SimpleGraph.Connected`. Textbook:
Bondy–Murty / Diestel, Eulerian graphs.
