# Ore's theorem (nonadjacent degree-sum Hamiltonian cycle) — formalize-only

**id:** `ore-hamiltonian`
**ticket:** OPE-1100 Formalist Level A (Scout OPE-1095 RECOMMENDED PRIME; Director OPE-1099; parent OPE-1094; post ostrowski-q #109 + andrasfai-erdos-sos #108)
**expected:** known-classical (Ore 1960) — **no novelty claim**

## Why not classical / why formalize-only

Settled graph theory: a finite simple graph on `n ≥ 3`
vertices is Hamiltonian whenever every pair of
*nonadjacent* vertices `u, v` satisfies
`deg u + deg v ≥ n`. Completely classical
(Øystein Ore, 1960). Dirac 1952 (`δ ≥ n/2`) is the
**special case** where the degree-sum bound holds
for *every* pair, adjacent or not.

Not an open problem. Not a novelty claim.

**Not** Dirac (`dirac-hamiltonian`, PRs **#44+#45**,
`dirac_hamiltonian` already in ProofLab — a
**different** named theorem, the `minDegree` special
case; USE `IsHamiltonian` encoding; do **not**
re-prove `dirac_hamiltonian`; do **not** revive
Dirac as a leftover). **Not** Bondy–Chvátal
(closure; out of v1). **Not** Chvátal degree-sequence
/ Pósa. **Not** Ore for *digraphs*. **Not**
Hamiltonian *path* (the pin is a cycle). **Not**
AES / Mycielski / Moore / greedy / Brooks / König
matching. **Not** ostrowski-q Level B. **Not**
andrasfai-erdos-sos Level B.

Mathlib v4.10.0 already has the **Hamiltonian infra
this theorem needs**:

- `SimpleGraph.IsHamiltonian` (`Hamiltonian.lean` L119)
  — graph contains a Hamiltonian cycle (n=1 convention
  unused under `n ≥ 3`)
- `Walk.IsHamiltonian` / `Walk.IsHamiltonianCycle`
  (`Hamiltonian.lean` L31 / L64)
- `SimpleGraph.degree` / `minDegree` (`Finite.lean` L314)
- Dirac namesake in `ProofLab/Dirac.lean` — **different
  theorem. Consumed. Do not re-prove. Do not re-prime.**

There is **no** Ore theorem, **no** nonadjacent
degree-sum Hamiltonian sufficient condition, and **no**
named `deg u + deg v ≥ n` implication anywhere under
`Mathlib/` or `Archive/` (word-regexp `ore_hamiltonian` /
`Ore's theorem` / `degree u + degree v` Hamiltonian
this run → ZERO). Graph `dirac` hits in the pin are
Dirac **measures**, not Ore. Do **not** import
`Archive.*`.

OPE-1078 shortlist is **CONSUMED** (#108+#109).
This is a **fresh** catalog-audit id, **not** a
Dirac leftover continuation, **not** an AES leftover,
**not** an Ostrowski leftover, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a third
slot.

Dirac's own STATEMENT named Ore as an optional
v1-b stretch of *that* ticket and Formalist left it
unattacked with “not a Scout leftover re-prime.”
This run introduces Ore as its **own** named theorem
under a new id. That is the correct path; it is
**not** reopening OPE-568.

Mill NOW: finite Hamiltonian sufficient-condition
prime after AES (extremal) + Ostrowski (valuations).
`IsHamiltonian` is waiting the same way `CliqueFree`
waited for AES. **Not a rubber-stamp of Dirac.**

Do **not** describe an attack as discovering Ore.
Do **not** expand into Bondy–Chvátal closure /
Chvátal sequence / Pósa as extra namesakes
(leftover-risk of *this* id). Do **not** re-prove
Dirac / AES Level B / Ostrowski Level B.

## Pinned convention (exact)

**v1 is the undirected simple Ore cycle theorem only.**
Encoding: Mathlib `SimpleGraph.IsHamiltonian` + `degree`.
Inequality in `ℕ` (no `ℚ`).

Suggested pin:

```text
-- Level A (not labelled Ore): n=3; complete graphs;
-- Ore-condition ⇒ connected; longest-path endpoints
-- have N(u), N(v) ⊆ V(P). Not labelled Ore.

-- Level B namesake
theorem ore_hamiltonian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hOre : ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian
```

`3 ≤ n` is load-bearing (`K₂`: `n=2`, `δ=1`, the
nonadjacent-pair quantifier is vacuous on the only
edge, and `K₂` is not Hamiltonian). The restriction
to **nonadjacent** `u ≠ v` is load-bearing (that is
the difference from Dirac). `Fintype V` is
load-bearing. `DecidableRel G.Adj` is load-bearing.

**Level A may land only** n=3 / complete /
connectedness-from-Ore / longest-path neighbourhood
glue, **not** labelled Ore. Reuse Mathlib
`IsHamiltonian` and the longest-path *idea* from
consumed Dirac — **do not re-prove**
`dirac_hamiltonian`.

**Level B** is the namesake: longest-path / cycle-closing
under the degree-sum hypothesis (Bondy–Murty / Diestel
style). Do not sorry the namesake; honest partial is
allowed (comment residual, not `sorry`). Bondy–Chvátal
closure is residual.

Optional cheap corollary (not labelled Ore, not
required): Dirac's `2 * minDegree ≥ n` implies the
Ore hypothesis, so Ore ⇒ Dirac as a *comment*. Do
**not** re-prove `dirac_hamiltonian` to “get” this.

## Landmines

1. **Do not re-prove** `IsHamiltonian` / `degree` /
   `minDegree` / `dirac_hamiltonian` / AES /
   bipartite-odd-cycle / greedy / Brooks. Already
   Mathlib or consumed ProofLab. Use them.
2. **This is not** Dirac (#44+#45). Special case ≠
   this theorem. Do not revive Dirac Level C / Ore
   as a Dirac leftover.
3. **`n ≥ 3` is load-bearing.** Same `K₂` landmine
   as Dirac.
4. **Cycle, not path.** Directed Ore out of v1.
5. **This is not** Bondy–Chvátal / Chvátal sequence /
   Pósa / Nash–Williams / Tutte.
6. **This is not** AES (#108) / ostrowski-q (#109) /
   Mycielski / Moore / König matching / König
   edge-colouring (the leftover).
7. **This is not** `bipartite-chromatic-index` (the
   leftover). Do **not** assign the leftover first
   unless Director swaps.
8. **This is not** ostrowski-q Level B /
   andrasfai-erdos-sos Level B / frobenius-real-division
   Level B / noether-normalization Level B / krenn-gu /
   hou-zeng-pfc / sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
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
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: `n=3` is `K₃` or a path of length 2 (the
path fails Ore). Complete graphs are Hamiltonian.
Ore ⇒ connected (a component missing a vertex cannot
meet the nonadjacent degree-sum). Longest path `P`
has `N(u), N(v) ⊆ V(P)`. **Not** labelled Ore.

Level B: if `u,v` are nonadjacent, `deg u + deg v ≥ n`
forces an index on `P` that closes a cycle through
`V(P)`; that cycle is spanning. Cap two levels. No
Bondy–Chvátal. No Dirac re-proof.

## Canonical source (pin in this STATEMENT)

O. Ore, *Note on Hamilton circuits*, Amer. Math.
Monthly 67 (1960) 55. Textbook: Bondy–Murty /
Diestel, Ore's theorem. Compact form: Wikipedia
*Ore's theorem* — **v1 pins `n ≥ 3` and nonadjacent
`deg u + deg v ≥ n ⇒ IsHamiltonian`.** Type pin:
Mathlib `IsHamiltonian` / `degree`. Dirac is a
**different** (consumed) special case, not this claim.

## Out of scope

- Bondy–Chvátal closure / Chvátal sequence / Pósa
- Directed Ore
- Hamiltonian *path* as namesake
- Dirac re-proof / AES Level B / Ostrowski Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
