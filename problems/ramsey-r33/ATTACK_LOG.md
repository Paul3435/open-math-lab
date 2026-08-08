# Attack log — ramsey-r33

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-08 14:40 | Attack Lead | R(3,3) via certified exhaustive enumeration (`native_decide` over Fin 15 edge-boolean colourings of K6); lower bound via 5-cycle witness | R(3,3) ≤ 6 PROVED zero-sorry (ProofLab/Ramsey.lean `ramsey33_le_6`); R(3,3) > 5 PROVED (`not_ramsey33_5`, `ramsey33_gt_5`). `lake build ProofLab.Ramsey` green, `lake env lean ProofLab.lean` exit 0. |
| 2026-08-08 15:40 | Attack Lead | Certified lower-bound witnesses via `native_decide` on concrete graph colourings; complement symmetry lemma | R(3,4) > 8 PROVED (`ramsey34_gt_8`, 8-vertex witness, 10 red edges, no red K3 / no blue K4). R(4,4) > 17 PROVED (`ramsey44_gt_17`, Paley-17 self-complementary colouring, 68 red edges, no K4 in either colour). `ramseyUpper_swap` proves `RamseyUpper k l n ↔ RamseyUpper l k n` (⇒ `R(3,4)=R(4,3)`). `lake build ProofLab` green, zero sorries. Upper bounds `R(3,4)≤9`, `R(4,4)≤18` remain (see plan below). |

## Status

- **Done (zero sorry), `lake build ProofLab` green:**
  - `RamseyUpper k l n` predicate over `SimpleGraph (Fin n)` red/blue colourings
    (red = graph, blue = complement), using Mathlib `IsNClique`/`Clique`.
  - `ramsey33_le_6` : `R(3,3) ≤ 6` — exhaustive search of all 2^15 colourings of `K_6`.
  - `not_ramsey33_5` / `ramsey33_gt_5` : `R(3,3) > 5` via the 5-cycle witness.
  - `ramsey34_gt_8` : `R(3,4) > 8` — 8-vertex witness (no red K3, no blue K4).
  - `ramsey44_gt_17` : `R(4,4) > 17` — Paley-17 witness (68 red edges, self-complementary, no K4 either colour).
  - `ramseyUpper_swap` : `RamseyUpper k l n ↔ RamseyUpper l k n` (colour-role symmetry).
- **Not yet proved:** `R(3,4) ≤ 9` and `R(4,4) ≤ 18` (upper bounds).

## Why R(3,4)=9 / R(4,4)=18 upper bounds cannot use the R(3,3) enumeration trick

`native_decide` enumerates the colouring space `2^C(N,2)`:
- `R(3,4) ≤ 9`: `K_9` → `2^36 ≈ 6.9e10` colourings (infeasible).
- `R(4,4) ≤ 18`: `K_18` → `2^153` (astronomical).

Upper bounds therefore need a **hand argument** (or a certified pruned search).

## Plan for the remaining upper bounds (next run)

**R(3,4) ≤ 9 — degree-parity hand proof (classical, clean):**
Assume a `K_9` colouring with no red K3 (`¬HasClique G 3`) and no blue K4
(`¬HasClique Gᶜ 4`); derive a contradiction.
1. **Every vertex red-degree ≤ 3** (pigeonhole): if a vertex `v` has ≥4 red
   neighbours, either two are red-adjacent (→ red K3 with `v`) or all are
   pairwise-blue (→ blue K4).  Hence every vertex has blue-degree ≥ 5 (8 − 3).
2. **Every vertex blue-degree ≤ 5**: if `v` had ≥6 blue-neighbours, take 6 of
   them `S`; by `R(3,3)=6` on `S` there is a monochromatic triangle — a red one
   contradicts step 1's source, a blue one plus `v` is a blue K4.
   So every vertex has blue-degree **exactly 5**.
3. **Parity contradiction**: sum of blue degrees = 9 × 5 = 45, but the
   degree-sum formula (`SimpleGraph.sum_degrees_eq_twice_card_edges`, needs
   `[Fintype (Sym2 V)]`) forces this sum to be `2 × (#blue edges)`, even.

Lean infra needed: a transfer lemma "R(3,3)=6 holds on any 6-vertex induced
subgraph" (reuse the `Fin 15 → Bool` edge encoding via an isomorphism, or
state `R(3,3)≤6` for arbitrary `SimpleGraph (Fin 6)`), plus degree-count and
the `DegreeSum` handshake lemma.

**R(4,4) ≤ 18 — recursion from R(3,4)≤9:**
`R(4,4) ≤ R(3,4) + R(4,3) = 9 + 9 = 18` by the classical recurrence
`R(k,l) ≤ R(k−1,l) + R(k,l−1)`, with `R(4,3)=R(3,4)` via `ramseyUpper_swap`.
A generic recursion lemma `RamseyUpper (k-1) l a → RamseyUpper k (l-1) b →
RamseyUpper k l (a+b)` needs the same local-degree / subgraph reasoning as
step 2 of the R(3,4) proof.

## Search / witness generation (reproducible)

- 8-vertex `R(3,4)>8` witness and Paley-17 check are reproducible from
  `bin/`-adjacent scripts; the Lean side hardcodes the two colourings and
  re-verifies them with `native_decide`, so the certificate is checked in Lean.
