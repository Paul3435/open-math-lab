# Oddtown — odd sets, even intersections, at most `n` of them (formalize-only)

**id:** `oddtown`
**ticket:** OPE-702 Scout leftover slot (support OPE-701; post cayley-trees #64 + mycielski-triangle-free #65)
**expected:** known-classical (Berlekamp 1969 / linear algebra method) — **no novelty claim**

## Why not classical / why formalize-only

Settled linear-algebra bound: a family of subsets of an `n`-set in which
every set has odd cardinality and every pairwise intersection has even
cardinality has size at most `n`. Not an open problem. Mathlib v4.10.0
has `LinearIndependent`, `ZMod 2`, `Finset`, and graph `incMatrix`
(different object). There is **no** Oddtown / Eventown / Berlekamp set
theorem anywhere under `Mathlib/` or `Archive/` (word-regexp this run →
ZERO). ProofLab has k-uniform intersecting EKR (`ErdosKoRado.lean`) —
**different** theorem (intersecting vs parity).

This is **not** a re-prime of `erdos-ko-rado`, friendship, Sperner/LYM,
Dilworth, or Kruskal–Katona. It is a **new proof layer**: the linear
algebra method over `GF(2)` on characteristic vectors of set families.

Do **not** describe an attack as discovering Oddtown.
Do **not** expand into Eventown (`m ≤ 2^{n-1}` even-town), Fisher’s
inequality / BIBD, or the nonuniform EKR bound (already upstream as
`Intersecting.card_le`).

## Pinned convention (exact)

**Ground set:** `Fin n`. Family: `𝒜 : Finset (Finset (Fin n))`.

**Parity pin:** `Odd s.card` and `Even (s ∩ t).card`. Equivalent and
allowed: `s.card % 2 = 1` / `(s ∩ t).card % 2 = 0`. Do **not** mix
`ℤ`-inner-products with the `ZMod 2` argument without a lemma.

**Characteristic vector (engine, not a second id):**

```text
def charVec {n : ℕ} (s : Finset (Fin n)) : Fin n → ZMod 2 :=
  fun i => if i ∈ s then 1 else 0

def Oddtown {n : ℕ} (𝒜 : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ 𝒜, Odd s.card) ∧
  (∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → Even (s ∩ t).card)

theorem oddtown {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h : Oddtown 𝒜) : 𝒜.card ≤ n
```

**v1 is the cardinality bound.** Linear independence of `{charVec s | s ∈ 𝒜}`
in `(Fin n → ZMod 2)` is the named engine, not a leftover id. Eventown
is **out of v1**.

## Landmines

1. **This is not EKR.** EKR is intersecting k-uniform families; ProofLab
   already has `erdos_ko_rado`. Oddtown is a parity constraint. Do not
   cite EKR as Oddtown and do not re-prove EKR here.
2. **This is not Eventown.** Eventown (all even sizes, even intersections,
   `m ≤ 2^{n-1}`) is a different theorem with a different bound. Out of
   v1 — do not invent as a leftover.
3. **This is not Fisher / BIBD / de Bruijn–Erdős.** Configuration
   `HasLines.card_le` is already upstream (incidence form). Different.
4. **This is not Kruskal–Katona / Sperner / LYM.** Shadows and antichains
   are different. Do not mix ids.
5. **Characteristic vectors over `ZMod 2`, not `ℝ`.** The inner product
   `∑ i, charVec s i * charVec t i` equals `|s ∩ t| mod 2`. Over `ℝ` the
   same family need not be orthogonal in the same way.
6. **Graph `incMatrix` is the wrong matrix.** `SimpleGraph.incMatrix` is
   vertex–edge incidence of a graph, not the set-family characteristic
   matrix. Do not reuse it as the engine.
7. **Finite only.** Ground set `Fin n`. Infinite oddtown out of scope.
8. **Do not re-prime** erdos-ko-rado / friendship / cayley-trees /
   mycielski-triangle-free / havel-hakimi / menger-vertex / greedy /
   Brooks / Dilworth / Eulerian / König / Dirac.
9. **No `Archive.*` import.**

## Proof sketch (classical, Berlekamp 1969)

Level A: empty family; `n = 0`; `n = 1` (at most `{ {0} }`); the `n`
singletons (each odd, pairwise intersections empty = even) achieve
tightness `m = n`.

Level B: namesake `oddtown`. The vectors `charVec s` for `s ∈ 𝒜` are
linearly independent over `ZMod 2` because the Gram matrix is the
identity (`⟨v_s, v_s⟩ = 1`, `⟨v_s, v_t⟩ = 0` for `s ≠ t`). Hence
`m ≤ dim(Fin n → ZMod 2) = n`.

Partial: **Level A** empty / `n ≤ 1` / singleton tightness, zero sorry,
not labelled Oddtown. **Level B** namesake via linear independence.
Cap two levels. No Eventown, no Fisher, no EKR.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Oddtown.lean`
- Reuse Mathlib `LinearIndependent`, `ZMod`, `Finset`. Do **not**
  re-prove EKR / Sperner / Dilworth / Kruskal–Katona. Do **not** import
  graph `incMatrix` as a substitute for `charVec`.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

E. R. Berlekamp, *On subsets with intersections of even cardinality*,
J. Combinatorial Theory **6** (1969) 298–301. Textbook pin: Babai–Frankl,
*Linear Algebra Methods in Combinatorics* (unpublished notes), Oddtown;
or Jukna, *Extremal Combinatorics*, linear algebra method / Oddtown.
Type pin: `Finset (Finset (Fin n))` + `ZMod 2` characteristic vectors.
EKR, Eventown, Fisher, Sperner, and Kruskal–Katona are **different**
theorems, not this claim.
