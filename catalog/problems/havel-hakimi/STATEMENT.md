# Havel–Hakimi — graphic sequences (finite simple graphs) — formalize-only

**id:** `havel-hakimi`
**ticket:** OPE-666 Scout recommended prime (support OPE-665; post greedy #57 + Brooks A #58 + Brooks B #59)
**expected:** known-classical (Havel 1955 / Hakimi 1962) — **no novelty claim**

## Why not classical / why formalize-only

Settled undergraduate characterisation: a nonincreasing sequence of
nonnegative integers is *graphic* (realised by a finite simple graph)
if and only if the Havel–Hakimi reduction of that sequence is graphic.
Not an open problem. Mathlib v4.10.0 already has `SimpleGraph.degree`,
`neighborFinset`, `maxDegree`, `minDegree`, and the handshaking lemma
(`sum_degrees_eq_twice_card_edges`, `even_card_odd_degree_vertices`).
There is **no** `IsGraphic` / `degreeSequence` / `Havel` / `Hakimi`
predicate anywhere under `Mathlib/` or `Archive/` (word-regexp this
run → ZERO). Handshaking is a *necessary* even-sum test, not the
characterisation.

This is **not** a re-prime of greedy-chromatic, Brooks A/B, Dilworth,
Eulerian, König, or Dirac. It is a **new proof layer**: degree-sequence
realisability on infra that already exists. Do not describe an attack
as discovering Havel–Hakimi. Do **not** expand into Erdős–Gállai,
Gale–Ryser, or Tutte.

## Pinned convention (exact)

Let `n : ℕ` and `d : Fin n → ℕ`.

**Nonincreasing pin:**

```text
def IsNoninc (d : Fin n → ℕ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≤ j → d j ≤ d i
```

**Realisation (labelled):** `G : SimpleGraph (Fin n)` with
`[DecidableRel G.Adj]` *realises* `d` when `∀ i, G.degree i = d i`.

**Graphic:**

```text
def IsGraphic (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    ∀ i, G.degree i = d i
```

**Reduction (Havel–Hakimi):** if `n = 0`, `d` is graphic (empty graph).
If `n ≥ 1` let `s := d 0`. If `s ≥ n` the sequence is not graphic.
Otherwise form the length-`(n-1)` sequence by deleting index `0` and
subtracting `1` from the next `s` entries (`d 1, …, d s`); if any
entry would go negative, not graphic. Re-sort the result
nonincreasing; call it `reduce d`.

**Claim (Havel–Hakimi iff):**

```text
theorem havel_hakimi {n : ℕ} {d : Fin n → ℕ}
    (hni : IsNoninc d) :
    IsGraphic d ↔ IsGraphic (reduce d)
```

with the convention that a failed reduction (negative entry, or
`d 0 ≥ n`) is `¬ IsGraphic d` on the left and is not passed to
`IsGraphic` on the right.

**v1 is this iff**, for simple graphs, labelled `Fin n`. The
constructive “build a realisation by reversing the reduction” is the
same heartbeat, not a second theorem.

**Encoding pin:** Mathlib `SimpleGraph.degree` on `Fin n`. Do **not**
count unlabelled isomorphism classes. Do **not** import `Archive.*`.

## Landmines

1. **Simple graphs only.** No loops, no multiple edges. `d i ≤ n-1`
   is necessary; `d 0 ≥ n` is immediately non-graphic.
2. **Re-sort after reduction is load-bearing.** The reduced tuple is
   not automatically nonincreasing. Dropping the sort is a false
   theorem.
3. **Even sum is necessary, not sufficient.** Handshaking
   (`sum_degrees_eq_twice_card_edges`) already lives in
   `DegreeSum.lean`. `(2,2,0,0)` has even sum and is **not** graphic
   — use it as a landmine, not as a “handshaking suffices” claim.
4. **This is not Erdős–Gállai.** EG is a different characterisation
   (partial sums). Out of v1. Do not invent it as Level C.
5. **This is not Gale–Ryser** (bipartite degree sequences) and **not
   Tutte** (1-factors). Matching.lean's Tutte TODO is a different
   theorem (`tutte`).
6. **Labelling is the claim.** Two non-isomorphic graphs may share a
   degree sequence. Existence only.
7. **`n = 0` / all-zeros / complete.** Empty is graphic. The constant
   sequence `n-1` is `⊤`. The sequence `(1)` on `n = 1` is not
   graphic (`1 ≥ 1`).
8. **Do not re-prime greedy / Brooks / König / Dirac / Eulerian /
   Dilworth.** Degree is not chromatic number.

## Proof sketch (classical, Havel 1955 / Hakimi 1962)

⇒ If `G` realises `d`, one may switch edges so that a maximum-degree
vertex is adjacent to the next `s` highest-degree vertices (Havel
switching). Delete that vertex; the remainder realises the unsorted
reduction, hence the sorted one.

⇐ Take a realisation of `reduce d`, insert a new vertex adjacent to
the first `s` vertices of the sorted remainder.

Partial: **Level A** empty / all-zeros (`⊥`) / complete (`⊤`) /
`K_2 = (1,1)` / non-graphic `(1)` and `(2,2,0,0)`, plus the easy
`d i ≤ n-1` glue, zero sorry. **Level B** namesake `havel_hakimi`.
Cap two levels. No Erdős–Gállai / Gale–Ryser / Tutte.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/HavelHakimi.lean`
- Reuse Mathlib `degree`, `neighborFinset`, `fromEdgeSet` (optional),
  `sum_degrees_eq_twice_card_edges`. Do **not** re-prove greedy /
  Brooks / König / Dirac / Eulerian / Dilworth.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

V. Havel, *Poznámka o existenci konečných grafů*, Časopis pro
pěstování matematiky **80** (1955) 477–480. S. L. Hakimi, *On
realizability of a set of integers as degrees of the vertices of a
linear graph. I*, J. Soc. Indust. Appl. Math. **10** (1962) 496–506.
Textbook pin: Diestel, *Graph Theory*, graphic sequences / Havel–Hakimi
algorithm (the iff, not the runtime). Type pin: Mathlib
`SimpleGraph.degree` on `Fin n`. Erdős–Gállai is a **different**
theorem, not this claim.
