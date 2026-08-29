# Cayley's formula — labelled trees `n^{n-2}` (formalize-only)

**id:** `cayley-trees`
**ticket:** OPE-683 Scout recommended prime (support OPE-682; post havel-hakimi #61 + menger-vertex #62)
**expected:** known-classical (Cayley 1889 / Prüfer 1918) — **no novelty claim**

## Why not classical / why formalize-only

Settled undergraduate count: the number of distinct trees on `n` labelled
vertices is `n^{n-2}`. Not an open problem. Mathlib v4.10.0 already has
`SimpleGraph.IsTree` (connected + acyclic), `IsTree.card_edgeFinset`
(`|E| + 1 = |V|`), and `fromEdgeSet`. There is **no** labelled-tree
cardinality, **no** Prüfer code, and **no** `n^{n-2}` count anywhere under
`Mathlib/` or `Archive/` (word-regexp this run → ZERO `Prufer`/`Prüfer`
in combinatorics; the only "Prüfer" hit is the unrelated Prüfer *subgroup*
in `Data/Set/Pointwise/Iterate.lean`).

This is **not** a re-prime of havel-hakimi, menger-vertex, greedy-chromatic,
Brooks A/B, Dilworth, Eulerian, König, or Dirac. It is a **new proof layer**:
enumerative counting on tree predicates that already exist.

OPE-666 considered-not-slotted Cayley and **benched it for definition
risk** (`SimpleGraph` is a large type). This run **does not rubber-stamp**:
the encoding is now pinned (edge-Finsets, not `{G // G.IsTree}`), so the
previous bench reason no longer holds. Gap + budget still hold.

Do **not** describe an attack as discovering Cayley's formula.
Do **not** expand into Kirchhoff / matrix-tree, spanning trees of arbitrary
`G`, Tutte, or unlabelled tree enumeration (OEIS A000055 — a different
sequence).

## Pinned convention (exact)

**Encoding pin (load-bearing):** `SimpleGraph` is a structure with
`Adj : V → V → Prop`. The type `{ G : SimpleGraph (Fin n) // G.IsTree }`
is **not** a `Fintype`. The claim is a count of *edge-sets*.

```text
/-- Edge-sets of labelled trees on `Fin n`. Loops are dropped by `fromEdgeSet`. -/
def LabelledTree (n : ℕ) : Type :=
  { s : Finset (Sym2 (Fin n)) //
      (SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))).IsTree }

theorem cayley_formula {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (LabelledTree n) = n ^ (n - 2)
```

**Nat arithmetic pin:** for `n = 1`, `n - 2 = 0` and `1 ^ 0 = 1` (one
empty tree). Scope is `n ≥ 1`. Do **not** pass `n = 0`.

**Prüfer (optional engine, same heartbeat as Level B):** a bijection
`LabelledTree n ≃ (Fin n) → Fin (n - 2)` for `n ≥ 2` (equivalently
`(Fin (n - 2)) → Fin n`) implies the cardinality. Either the bijection
or a direct inductive count is in v1; both are the same namesake.

**v1 is this cardinality**, labelled, simple graphs, `Fin n`.
Unlabelled isomorphism classes are **out of scope** (and the formula
would be false).

## Landmines

1. **Do not write `Fintype.card {G : SimpleGraph (Fin n) // G.IsTree}`.**
   That type is not finite in the way the theorem needs. Edge-Finsets only.
2. **This is not group Cayley's theorem** (`G` embeds in `Sym G`). Already
   in Mathlib: `MulAction.toPermHom` / `GroupTheory.Perm.Subgroup`
   ("Cayley's theorem"). Different theorem.
3. **This is not Cayley–Hamilton** (`charpoly`). Already in
   `LinearAlgebra.Matrix.Charpoly`. Different theorem.
4. **This is not the Cayley graph of a group.**
5. **This is not Kirchhoff / matrix-tree.** `LapMatrix.lean` exists
   (kernel rank = components) but has ZERO spanning-tree count. Cayley
   is the `K_n` special case; do **not** prove matrix-tree in this id
   and do **not** invent it as a leftover.
6. **This is not Tutte, not Whitney, not spanning-tree packing.**
7. **`fromEdgeSet` drops diagonals.** Pin `s` as a `Finset (Sym2 (Fin n))`;
   loops are not edges of a simple graph. Do not count looped Sym2's as
   extra trees.
8. **Unlabelled count is a different (harder, smaller) sequence.**
9. **Do not re-prime havel-hakimi / menger-vertex / greedy / Brooks /
   Dilworth / Eulerian / König / Dirac.** Counting trees is not graphic
   sequences and not separators.
10. **No `Archive.*` import.**

## Proof sketch (classical, Cayley 1889 / Prüfer 1918)

Prüfer: from a labelled tree on `{0,…,n-1}` (`n ≥ 2`), iteratively delete
the leaf with smallest label and record its unique neighbour. The record
has length `n-2`. Reverse: grow `n` isolated vertices by reading the code
backwards, attaching the smallest unused leaf at each step. The map is a
bijection, so there are `n^{n-2}` codes and `n^{n-2}` trees.

Partial: **Level A** `n = 1` (empty / `⊥`), `n = 2` (`K_2`, one tree),
`n = 3` (three paths on three labelled vertices), plus the glue
`IsTree.card_edgeFinset` (`|E| = n-1`), zero sorry. **Level B** namesake
`cayley_formula` via Prüfer (or an equivalent induction). Cap two levels.
No matrix-tree / no Tutte / no unlabelled count.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/CayleyTrees.lean`
- Reuse Mathlib `IsTree`, `IsTree.card_edgeFinset`, `fromEdgeSet`,
  `edgeFinset`. Do **not** re-prove Havel / Menger / greedy / Brooks /
  König / Dirac / Eulerian / Dilworth.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

A. Cayley, *A theorem on trees*, Quart. J. Pure Appl. Math. **23** (1889)
376–378. H. Prüfer, *Neuer Beweis eines Satzes über Permutationen*,
Arch. Math. Phys. **27** (1918) 742–744. Textbook pin: Aigner–Ziegler,
*Proofs from THE BOOK*, Cayley's formula (Prüfer code); or Diestel,
*Graph Theory*, counting labelled trees. Type pin: Mathlib
`SimpleGraph.IsTree` + `fromEdgeSet` on `Finset (Sym2 (Fin n))`.
Group Cayley and Cayley–Hamilton are **different** already-upstream
theorems, not this claim.
