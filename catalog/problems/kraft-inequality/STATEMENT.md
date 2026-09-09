# Kraft inequality — formalize-only

**id:** `kraft-inequality`
**ticket:** OPE-1238 Formalist Level A (Scout OPE-1233 RECOMMENDED PRIME; Director OPE-1237)
**expected:** known-classical (Kraft 1949: prefix-free
codes satisfy ∑ r^{-ℓ} ≤ 1) — **no novelty claim**

## Why not classical / why formalize-only

Settled source-coding / combinatorics on
words: a finite prefix-free code over an
alphabet of size `r ≥ 2` has Kraft sum
`∑_w r^{-|w|} ≤ 1`. Completely classical
(Kraft 1949; McMillan 1956 for uniquely
decodable).

Not an open problem. Not a novelty claim.

**Not** the Hamming metric / Singleton bound
(consumed #120; `hammingDist` is
InformationTheory/Hamming.lean L38 —
error-correcting min-distance, **different
theorem**; USE nothing as namesake; do
**not** revive `singleton_bound` /
Hamming-bound / Plotkin / MDS). **Not**
Shannon source-coding / Huffman optimality
(residual of *this* id). **Not** McMillan
uniquely-decodable (residual of *this* id;
prefix-free is the v1 pin). **Not** Kraft
as a namesake of Singleton (OPE-1147
explicitly: "This is not Kraft / Shannon /
Huffman" — different statement).

Mathlib v4.10.0 already has the **list-prefix
/ Finset / Hamming-folder infra this
theorem needs**:

- `List.IsPrefix` / notation `<+:`
  (`Data/List/Infix.lean` L12 / L23;
  defined in `Data/List/Defs`)
- `Finset.sum` / `Fintype.card`
- `hammingDist` (Hamming.lean L38) —
  **not** namesake (Singleton glue)

There is **no** named Kraft inequality,
**no** `kraft` / `PrefixFree` /
`kraftSum` / `McMillan` / `Huffman` /
`uniquelyDecodable` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(this run → ZERO on those names).
InformationTheory/ contains **only**
`Hamming.lean` (metric). Do **not**
import `Archive.*`.

OPE-1216 shortlist is **CONSUMED**
(#135 petersen-1-factor Level A +
#136 lagrange-quadratic-cf Level A).
This is a **fresh** catalog-audit id,
**not** a Petersen leftover continuation,
**not** a Lagrange leftover, **not** a
Singleton leftover, **not** a Hamming-bound
revival, **not** a prize leftover, **not**
a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite prefix-free Kraft after
Petersen 1-factor (cubic matching) +
Lagrange φ-CF. `List.IsPrefix` + the
almost-empty `InformationTheory/` folder
are waiting the same way `Matrix.circulant`
waited for the circulant determinant.
**Not a rubber-stamp of Singleton.**
**Not a rubber-stamp of Huffman.**

Do **not** describe an attack as discovering
Kraft's inequality. Do **not** expand into
McMillan / Huffman / Shannon entropy /
Hamming-bound / Plotkin / MDS as extra
namesakes (McMillan/Huffman/Shannon are
leftover-risk of *this* id; Hamming-bound
is leftover of consumed Singleton).

## Pinned convention (exact)

**v1 Level A is prefix-free + Kraft sum on
finite named codes over `Fin 2`: empty
`Finset`, singleton, and the binary
tree `{[0], [1,0], [1,1]}` with Kraft
sum `1`, not labelled Kraft.** Count in
`ℚ`. Alphabet cardinality `r = 2` is
load-bearing for the explicit example.

Suggested pin:

```text
-- Level A (not labelled Kraft / Huffman):
-- empty Finset; singleton; binary {0, 10, 11}.
-- Not labelled Kraft.

def PrefixFree {α} (C : Finset (List α)) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v

def kraftSum {α} [Fintype α] [DecidableEq α]
    (C : Finset (List α)) : ℚ :=
  C.sum fun w => ((Fintype.card α : ℚ)⁻¹) ^ w.length

theorem prefixFree_empty {α} :
    PrefixFree (∅ : Finset (List α))

theorem kraftSum_empty {α}
    [Fintype α] [DecidableEq α] :
    kraftSum (∅ : Finset (List α)) = 0

theorem prefixFree_singleton {α} (w : List α) :
    PrefixFree {w}

def kraftBinaryExample : Finset (List (Fin 2)) :=
  { [0], [1, 0], [1, 1] }

theorem prefixFree_kraftBinaryExample :
    PrefixFree kraftBinaryExample

theorem kraftSum_kraftBinaryExample :
    kraftSum kraftBinaryExample = 1

-- Level B namesake (all finite prefix-free; residual OK)
theorem kraft_inequality {α}
    [Fintype α] [DecidableEq α]
    {C : Finset (List α)}
    (hα : 1 < Fintype.card α)
    (h : PrefixFree C) :
    kraftSum C ≤ 1
```

Finite `Fin 2` / `Finset (List (Fin 2))` is
load-bearing. Prefix-free (`¬ <+:`) is
load-bearing. Kraft sum in `ℚ` is
load-bearing.

**Level A may land only** empty / singleton
/ `{[0],[1,0],[1,1]}` (optional extra:
singleton empty-word Kraft `1`), **not**
labelled Kraft.
Reuse Mathlib `List.IsPrefix` / `<+:` /
`Finset.sum` / `Fintype.card` —
**do not re-prove** prefix or summation.

**Level B** is the namesake: every finite
prefix-free code over `r ≥ 2` has Kraft
sum `≤ 1`. Do not sorry the namesake;
honest partial is allowed (comment
residual, not `sorry`). McMillan /
Huffman / Shannon are residual.

## Landmines

1. **Do not re-prove** `List.IsPrefix` /
   `<+:` / `Finset.sum` / `Fintype.card` /
   `hammingDist`. Already Mathlib. Use them.
2. **This is not** Singleton / `hammingDist`
   (consumed #120). Different theorem
   (min-distance vs prefix-free source
   codes). Do not revive Hamming-bound /
   Plotkin / MDS.
3. **This is not** McMillan uniquely
   decodable. Residual of this id. Do not
   sorry McMillan. Do not take McMillan as
   namesake.
4. **This is not** Huffman optimality /
   Shannon noiseless coding / Fano.
   Residual of this id.
5. **This is not** `petersen-1-factor`
   (#135) / Tutte / Hall / König.
6. **This is not** `lagrange-quadratic-cf`
   (#136) / Pell / Galois / Hurwitz /
   `terminates_iff_rat`.
7. **This is not** Gauss–Lucas / Sturm /
   Budan–Fourier (Descartes leftover).
8. **Do not** re-prime the consumed mill
   list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- McMillan uniquely-decodable inequality
- Huffman optimality / Shannon source coding
- Hamming-bound / Plotkin / MDS (Singleton leftover)
- Kraft equality characterisation (complete trees)
- Infinite codes / σ-finite Kraft
- Prize claims / Millennium / Beal
