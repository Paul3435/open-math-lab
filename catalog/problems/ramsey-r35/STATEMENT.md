# Ramsey number R(3,5)=14 (formalize-only)

**id:** `ramsey-r35`
**ticket:** OPE-393
**expected:** known-classical (Greenwood–Gleason 1955)
**frame:** **formalize-only** — do NOT re-fund as novel research; default **no claim**

## Informal statement

For integers `k,l ≥ 2`, the Ramsey number `R(k,l)` is the least `N` such that every
2-colouring of the edges of `K_N` contains a red `K_k` or a blue `K_l`.

Classical value (Greenwood–Gleason 1955):

- **`R(3,5) = 14`**
  - Lower: there exists a 2-colouring of `K_13` with no red triangle and no blue `K_5`
    (equivalently: a triangle-free graph on 13 vertices with independence number `α ≤ 4`).
  - Upper: every 2-colouring of `K_14` has a red triangle or a blue `K_5`.

By colour-swap symmetry, `R(5,3) = R(3,5) = 14`.

## Lab predicate (reuse, do not fork)

Use the existing vocabulary in `proofs/lean-project/ProofLab/Ramsey.lean` (OPE-44 / PR #18):

- Red edges = `G : SimpleGraph (Fin n)`; blue = `Gᶜ`.
- `HasClique G k` := `G` contains a `k`-clique.
- `RamseyUpper k l n` := every `G` on `Fin n` satisfies `HasClique G k ∨ HasClique Gᶜ l`
  (i.e. `R(k,l) ≤ n`).
- Target equality package: `(¬ RamseyUpper 3 5 13) ∧ RamseyUpper 3 5 14`.

## Proof plan (pinned before attack)

### Lower bound `R(3,5) > 13`

**Witness:** circulant graph `C₁₃({±1, ±5})` on `ℤ/13ℤ` — vertices `Fin 13`, red edge
between `u` and `v` iff the circular distance `(v−u) mod 13` is in `{1,5,8,12}`.

Offline checks (Python enumeration, 2026-08-24):

- 26 red edges, triangle-free.
- Independence number `α = 4` (no independent set of size 5) ⇒ complement is `K_5`-free.

Lean gate: `native_decide` on `cliqueFinset 3` (red) and `cliqueFinset 5` (blue/complement),
same pattern as the OPE-44 8-vertex and Paley-17 witnesses.

### Upper bound `R(3,5) ≤ 14`

Classical recurrence already formalized as `ramseyUpper_add`:

```
R(3,5) ≤ R(2,5) + R(3,4) = 5 + 9 = 14
```

Ingredients:

1. **`R(2,l) ≤ l`** (trivial): if the red graph has no edge then blue is complete on `l` verts.
2. **`R(3,4) ≤ 9`** already proved as `ramsey34_le_9` (OPE-44).
3. Apply `ramseyUpper_add` with `k=3`, `l=5`, `a=5`, `b=9`.

(Optional hand degree-count on `K_14` is unnecessary once the recurrence closes; Scout’s
“degree-counting” note is satisfied by the same degree/recurrence family used for R(3,4)/R(4,4).)

## Acceptance criteria

1. `STATEMENT.md` pinned (this file) before Lean edits land on the branch.
2. Lean theorems (zero `sorry` / `admit` / custom `axiom`):
   - `ramsey35_gt_13` / `not_ramsey35_13` — lower bound via circulant witness.
   - `ramsey35_le_14` — upper bound via `R(2,5)+R(3,4)`.
   - `ramsey35_eq_14` — pair of bounds.
3. `lake build ProofLab` green (or at least `lake env lean ProofLab/Ramsey.lean` exit 0).
4. ATTACK_LOG + ledger + catalog updated; branch + PR; **no novelty / no external claim**.

## References

- Greenwood & Gleason, “Combinatorial relations and chromatic graphs”, Can. J. Math. 7 (1955)
  — includes `R(3,5)=14`.
- Standard elementary presentation: `R(3,5) ≤ R(2,5)+R(3,4)=5+9=14`; lower via the
  13-vertex circulant of connection set `{±1,±5}` (unique critical colouring up to iso).
- OEIS A000791 (triangle–pentagon Ramsey numbers / small off-diagonal Ramsey).
- Prior lab art: `problems/ramsey-r33/`, `ProofLab/Ramsey.lean` (R(3,3)/R(3,4)/R(4,4)).

## Novelty pre-screen

- **Mathlib gap (v4.10.0 pin):** still no `ramsey` / `ramseyNumber` theorem under `Mathlib/`
  (re-confirmed OPE-390 Scout). Reusing `ProofLab.Ramsey` is correct; not a Mathlib import.
- **Status:** known-classical → **formalize-only**. Value = Lean certificate + API growth, not a new theorem.
