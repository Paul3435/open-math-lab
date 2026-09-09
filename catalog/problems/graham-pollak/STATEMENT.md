# Graham–Pollak biclique decomposition of K_n — formalize-only

**id:** `graham-pollak`
**ticket:** OPE-1248 Scout leftover slot #2 (Director approves after this shortlist)
**expected:** known-classical (Graham–Pollak 1971:
the edges of `K_n` partition into `n−1` complete
bipartite graphs, and not fewer) — **no novelty claim**

## Why not classical / why formalize-only

Settled extremal graph theory: the minimum number
of bicliques (complete bipartite graphs) whose
edges partition `E(K_n)` is `n−1`. Completely
classical (Graham–Pollak 1971; linear-algebra rank
proof).

Not an open problem. Not a novelty claim.

**Not** Nash–Williams arboricity (consumed #124;
edge partition into *forests* — **different
theorem**; do **not** revive `nash_williams` /
matroid-union). **Not** Cayley labelled-tree count
(consumed; do **not** revive Kirchhoff). **Not**
Kővári–Sós–Turán (consumed `kst`; forbidding a
biclique is the opposite of decomposing into
bicliques). **Not** König χ' / Vizing (edge
*colouring*, consumed). **Not** Sabidussi box
products / Hedetniemi (consumed #139). **Not**
Brooks / greedy / AES / bipartite-odd-cycle /
Mycielski.

Mathlib v4.10.0 already has the **complete-graph /
edge-finset / bipartite infra this theorem needs**:

- `SimpleGraph.completeGraph` (`Basic.lean` L144)
- `completeGraph_eq_top` L339
- `completeBipartiteGraph` L153 — **not** namesake
  (König matching glue; a biclique *in* `K_n` is a
  Finset-pair encoding, not a re-proof of `K_{a,b}`)
- `edgeFinset` (`Finite.lean` L53)
- `edgeFinset_bot` L81
- `card_edgeFinset_top_eq_card_choose_two` L110
  (`|E(K_n)| = C(n,2)`)

There is **no** named Graham–Pollak theorem, **no**
`grahamPollak` / `graham_pollak` / `biclique` /
`bicliquePartition` / `Pollak` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names). Do **not** import
`Archive.*`.

OPE-1233 shortlist is **CONSUMED**
(#138+#139). This is a **fresh** catalog-audit
leftover id, **not** a Kraft leftover continuation,
**not** a Sabidussi leftover, **not** an NW /
Cayley / KST revival, **not** a prize leftover,
**not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite biclique decomposition leftover
beside Sherman–Morrison (rank-one inverse).
`completeGraph` + `edgeFinset` are waiting the same
way `boxProd` waited for Sabidussi colouring.
**Not a rubber-stamp of Nash–Williams.** **Not a
rubber-stamp of KST.**

Do **not** describe an attack as discovering
Graham–Pollak. Do **not** expand into biclique
*cover* (not partition) / Zarankiewicz / C₄ as
extra namesakes (cover vs partition is residual of
*this* id).

## Pinned convention (exact)

**v1 Level A is an explicit biclique-edge partition
of `completeGraph (Fin n)` of size `n−1` for
`n = 1, 2, 3`, not labelled Graham–Pollak.**
Bipartition `Disjoint X Y` is load-bearing.
Partition of `edgeFinset` is load-bearing.
`n ≥ 1` is load-bearing (`n−1` for `n = 0` is
not a Nat).

Suggested pin:

```text
-- Level A (not labelled Graham–Pollak):
-- K_1 empty partition; K_2 one K_{1,1}; K_3 star plus leftover edge.
-- Not labelled Graham–Pollak.

def bicliqueEdges {V} [DecidableEq V] (X Y : Finset V) :
    Finset (Sym2 V) :=
  ((X ×ˢ Y).filter fun p => p.1 ≠ p.2).image fun p => s(p.1, p.2)

def IsBicliquePartition {V} [Fintype V] [DecidableEq V]
    (parts : Finset (Finset V × Finset V)) : Prop :=
  (∀ p ∈ parts, Disjoint p.1 p.2)
  ∧ parts.toSet.Pairwise fun p q =>
      Disjoint (bicliqueEdges p.1 p.2) (bicliqueEdges q.1 q.2)
  ∧ parts.biUnion (fun p => bicliqueEdges p.1 p.2)
      = (completeGraph V).edgeFinset

theorem bicliquePartition_complete_fin_one :
    IsBicliquePartition
      (∅ : Finset (Finset (Fin 1) × Finset (Fin 1)))
    ∧ (∅ : Finset (Finset (Fin 1) × Finset (Fin 1))).card
        = 1 - 1

theorem bicliquePartition_complete_fin_two :
    IsBicliquePartition {({0}, {1}) : Finset (Fin 2) × Finset (Fin 2)}
    ∧ ({({0}, {1}) : Finset (Finset (Fin 2) × Finset (Fin 2))}).card
        = 2 - 1

theorem bicliquePartition_complete_fin_three :
    -- star at 0 covering {0-1, 0-2} plus leftover {1-2}
    IsBicliquePartition
      {({0}, {1, 2}), ({1}, {2})}
    ∧ ({({0}, {1, 2}), ({1}, {2})}
        : Finset (Finset (Fin 3) × Finset (Fin 3))).card
        = 3 - 1

-- Level B namesake (minimum is n-1; residual OK)
theorem graham_pollak {n : ℕ} (hn : 0 < n) :
    IsLeast {k | ∃ parts : Finset (Finset (Fin n) × Finset (Fin n)),
      IsBicliquePartition parts ∧ parts.card = k} (n - 1)
```

Finite `Fin 1` / `Fin 2` / `Fin 3` is load-bearing.
`Disjoint` bipartition is load-bearing. Equality
with `(completeGraph V).edgeFinset` is load-bearing.

**Level A may land only** K₁ empty / K₂ one edge /
K₃ star-plus-edge (optional extra: K₄ two stars plus
a leftover matching), **not** labelled Graham–Pollak.
Reuse Mathlib `completeGraph` / `edgeFinset` /
`card_edgeFinset_top_eq_card_choose_two` /
`Disjoint` — **do not re-prove** complete graphs or
handshaking.

**Level B** is the namesake: every biclique partition
of `K_n` (`n ≥ 1`) has size `≥ n−1`, and size `n−1`
is achieved. Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`).
Biclique *cover* (overlapping allowed) / Zarankiewicz
are residual.

## Landmines

1. **Do not re-prove** `completeGraph` /
   `completeGraph_eq_top` / `edgeFinset` /
   `card_edgeFinset_top_eq_card_choose_two` /
   `completeBipartiteGraph` / `Disjoint`.
   Already Mathlib. Use them.
2. **This is not** Nash–Williams arboricity
   (consumed #124). Forests ≠ bicliques. Do not
   revive `nash_williams` / matroid-union.
3. **This is not** Cayley / Kirchhoff (consumed
   leftover). Do not count spanning trees.
4. **This is not** KST / Zarankiewicz (consumed
   `kst`). Forbidding a biclique is the opposite
   theorem.
5. **This is not** König χ' / Vizing / Sabidussi /
   Brooks / greedy / AES / bipartite-odd-cycle.
6. **This is not** `kraft-inequality` (#138) /
   McMillan / Huffman / Shannon.
7. **This is not** `sherman-morrison` (OPE-1248
   prime). Do not prove Sherman–Morrison here.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Biclique *cover* number (not partition)
- Zarankiewicz / even-cycle extremal
- Linear-algebra rank proof of the `n−1` lower bound
  (namesake engine; residual OK as comment)
- Prize claims / Millennium / Beal
