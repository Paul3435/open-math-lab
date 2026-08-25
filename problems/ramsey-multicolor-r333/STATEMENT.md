# Multicolour Ramsey number R(3,3,3) = 17 (formalize-only)

**id:** `ramsey-multicolor-r333`
**ticket:** OPE-461 (prime from Scout OPE-458)
**expected:** known-classical (Greenwood & Gleason 1955) — **no novelty claim**

## Pinned convention (exact)

### Edge colouring

An edge **k-colouring** of the complete graph on `n` vertices is a function

```text
f : Fin n → Fin n → Fin k
```

that is **symmetric** (`f a b = f b a` for all `a, b`) and **irreflexive in intent**
(the diagonal `f a a` is unused by monochromatic-triangle predicates; Lean
implementations may default it, e.g. to `0`).

**Pinned encoding:** the function form above.
**Noted alternative (not used):** `Sym2 (Fin n) → Fin k` (unordered edges).

### Monochromatic triangle

```text
HasMonoTriangle f  ↔  ∃ distinct a b c,  f a b = f a c = f b c
```

### Certificate edge order

For witness strings / `native_decide` certificates, unordered edges are listed in
**lexicographic order `(i,j)` with `i < j`**, index

```text
edgeIndex(i,j) = i·(2n − i − 1)/2 + (j − i − 1)
```

Same convention as the W(2,4) > 34 witness string in `VanDerWaerden.lean`.

## Claim

The multicolour Ramsey number `R(3,3,3)` — the least `N` such that every
3-edge-colouring of `K_N` contains a monochromatic triangle — equals **17**:

1. **Lower bound** `R(3,3,3) > 16`: there exists a 3-edge-colouring of `K_16`
   with no monochromatic triangle
   (Greenwood–Gleason `F₂⁴` construction; certificate
   `catalog/problems/ramsey-multicolor-r333/witness16_certificate.txt`,
   length 120 = C(16,2)).
2. **Upper bound** `R(3,3,3) ≤ 17`: every symmetric 3-edge-colouring of `K_17`
   has a monochromatic triangle.

## Proof sketch (classical)

### Lower

Import the length-120 digit string over `{0,1,2}`. Decode via `edgeIndex`.
Check `¬ HasMonoTriangle witness16` by decidable enumeration of triples on
`Fin 16` (not by brute-forcing `3^120` colourings).

### Upper

Fix vertex `v` in `K_17`. The 16 incident edges are 3-coloured, so some colour
`c` appears at least 6 times (pigeonhole: `⌈16/3⌉ = 6`). Let `S` be a 6-subset of
the `c`-neighbourhood of `v`.

- If any edge inside `S` has colour `c`, that edge + `v` is a mono-`c` triangle.
- Otherwise edges of `S` use only the other two colours. Pull back `R(3,3) ≤ 6`
  (`ramsey33_clique_inside_finset` from `ProofLab/Ramsey.lean`) to obtain a
  monochromatic triangle in one of those two colours.

Note: the complementary “all colour-degrees ≤ 5 at `v`” case is impossible on
`K_17` because `5+5+5 = 15 < 16`. Handshake parity is **not** required for the
upper bound (and does not obstruct the 5-regular-per-colour GG colouring on 16
vertices either: degree sum `16·5 = 80` is even).

## Lean gate

- File: `proofs/lean-project/ProofLab/RamseyMulticolor.lean`
- Theorems: `r333_gt_16`, `r333_le_17`, `r333_eq_17`
- Zero `sorry` / `admit` / custom axiom; `lake env lean ProofLab/RamseyMulticolor.lean` EXIT=0
- Does **not** modify closed `Ramsey.lean` / `VanDerWaerden.lean`

## References

- Greenwood & Gleason, “Combinatorial relations and chromatic graphs”,
  Canadian Journal of Mathematics 7 (1955) 1–7.
- Scout dossier: `catalog/problems/ramsey-multicolor-r333/DOSSIER.json` (OPE-458).
