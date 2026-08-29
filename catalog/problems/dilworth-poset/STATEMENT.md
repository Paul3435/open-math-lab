# Dilworth's theorem — min chain partition = max antichain (finite posets) — formalize-only

**id:** `dilworth-poset`
**ticket:** OPE-613 Scout recommended prime (support OPE-612; post König B PR #50)
**expected:** known-classical (Dilworth 1950) — **no novelty claim**

## Why not classical / why formalize-only

Settled 1950 min-max for finite posets, not an open problem. Mathlib
v4.10.0 has `Order.Chain.IsChain` and `Order.Antichain.IsAntichain`,
and ProofLab now has Kőnig `Colorable 2 → ν=τ` (`ProofLab/Konig.lean`,
PR #50 MERGED). There is **no** Dilworth theorem, **no** chain-partition
number, and **no** width (= max antichain size) anywhere under
`Mathlib/` or `Archive/` (word-regexp `dilworth` → ZERO this run).

This is **not** a re-prime of König Level A/B (namesake graph min-max
is closed). It is a **new proof layer**: the poset theorem, classically
reduced to König via the Fulkerson split construction. König was the
blocking primitive on prior Scout runs (OPE-533/553/574/591); that
block is gone as of PR #50. Do not describe an attack as discovering
Dilworth's theorem.

## Pinned convention (exact)

Let `α` be a finite type with `[Fintype α] [DecidableEq α] [PartialOrder α]`
and `[DecidableRel ((· : α) ≤ ·)]`.

**Chain / antichain (Mathlib predicates, Finset wrappers in ProofLab):**

```text
def IsChainSet (C : Finset α) : Prop :=
  IsChain (· ≤ ·) (C : Set α)

def IsAntichainSet (A : Finset α) : Prop :=
  IsAntichain (· ≤ ·) (A : Set α)
```

**Chain partition of `univ`:** a finite family of pairwise-disjoint
chains whose union is `Finset.univ`. Cardinality of the family is the
number of chains.

**Width:**

```text
def width : ℕ :=
  Finset.univ.sup (fun A : Finset α => if IsAntichainSet A then A.card else 0)
```

(Implementation may use `sSup` / `Finset.sup` / an explicit maximum
antichain; the **claim** is equality of width with the minimum size of
a chain partition.)

**Claim (Dilworth, finite):**

```text
∃ (n : ℕ) (chains : Fin n → Finset α) (A : Finset α),
    (∀ i, IsChainSet (chains i)) ∧
    (∀ i j, i ≠ j → Disjoint (chains i) (chains j)) ∧
    (∀ x, ∃ i, x ∈ chains i) ∧
    IsAntichainSet A ∧
    A.card = n ∧
    n = width
```

equivalently: there is a chain partition of size `width`. The easy
inequality `width ≤ min chain-partition size` holds for every finite
poset (an antichain meets each chain in at most one element) and is
**Level A**, not the namesake.

**Encoding pin:** Mathlib `PartialOrder` + `IsChain` + `IsAntichain`.
König reduction (allowed, not required) goes through a bipartite
`SimpleGraph` on `α ⊕ α` with `Adj (inl a) (inr b) ↔ a < b` (strict),
then `ProofLab.Konig.konig_bipartite`. Do **not** apply König to the
comparability graph of the poset (that graph is not bipartite in
general). Do **not** cite `hall_hard_inductive` or `konig_bipartite`
*as* Dilworth.

**v1-b (stretch, same heartbeat only if cheap):** Mirsky's dual
(min antichain partition = height = max chain size). Not required for
v1. Dual, not the same theorem.

## Landmines

1. **Finite is load-bearing.** Infinite Dilworth needs choice and a
   different statement. Pin `Fintype α`.
2. **`PartialOrder`, not `Preorder`.** Preorders can have nontrivial
   equivalences; chain/antichain conventions then slip.
3. **This is not König.** `ProofLab/Konig.lean` `konig_bipartite` is
   the *engine*, not the claim. Do not re-prime König A/B.
4. **This is not Hall.** SDR is a different upstream theorem.
5. **This is not Mirsky.** Chain partition / antichain size, not
   antichain partition / chain size. Swapping them is the classic
   off-by-duality bug.
6. **Split graph uses strict `<`, not `≤`.** Diagonal `a ≤ a` would
   add junk (or fail irreflexivity of `SimpleGraph.Adj`).
7. **Comparability graph ≠ split graph.** Comparability graphs of
   posets need not be bipartite (`3`-element chain is a triangle in
   the comparability graph if one adds both covering and long
   relations carelessly; in any case do not Colorable-2 the
   comparability graph and call König).
8. **Empty poset:** width 0, empty partition. A total chain: width 1.
   An antichain poset: width = `card α`, one-element chains.
9. **Do not expand v1 into infinite Dilworth, Greene's theorem, or
   the Greene–Kleitman extension.**

## Proof sketch (classical, Fulkerson / König)

Easy inequality (all finite posets): any antichain meets any chain in
at most one point, so `width ≤` number of chains in any partition.

Hard inequality: build the bipartite split graph `G` on `α ⊕ α` with
an edge `inl a — inr b` iff `a < b`. `G.Colorable 2` is immediate.
A maximum matching in `G` links covering relations into paths; the
unmatched elements start/end chains. König `ν = τ` converts a minimum
vertex cover into the identity that the number of chains equals the
size of a maximum antichain (the complement of the cover, intersected
appropriately with the two copies, yields the antichain). Textbook:
Dilworth 1950; Fulkerson 1956 matching formulation; Diestel / Trotter.

Partial: **Level A** easy inequality + chain poset / antichain poset /
empty / 2-element specials. **Level B** ∀ finite poset via König
split (or an equivalent max-flow / Hall proof — still Dilworth, not a
citation of Hall as Dilworth).

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Dilworth.lean`
- Reuse `ProofLab.Konig` (`IsVertexCover`, `matchingNumber`,
  `vertexCoverNumber`, `konig_bipartite`). Do **not** re-prove König.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

R. P. Dilworth, *A decomposition theorem for partially ordered sets*,
Annals of Mathematics **51** (1950) 161–166. Matching formulation:
D. R. Fulkerson, *Note on Dilworth's decomposition theorem for
partially ordered sets*, Proc. Amer. Math. Soc. **7** (1956) 701–702.
Textbook pin: Trotter / Anderson, Dilworth's theorem. Type pin:
Mathlib `IsChain` / `IsAntichain` + ProofLab `konig_bipartite`.
