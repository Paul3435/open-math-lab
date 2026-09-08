# Schur product theorem — formalize-only

**id:** `schur-product`
**ticket:** OPE-1189 Scout RECOMMENDED PRIME (parent OPE-1188; post gale-shapley #126 + farey-sequence #127)
**expected:** known-classical (Schur 1911 / Hadamard 1894) — **no novelty claim**

## Why not classical / why formalize-only

Settled matrix analysis: if `A` and `B` are
positive semidefinite, then the *Hadamard*
(entrywise) product `A ⊙ B` is positive
semidefinite (Issai Schur 1911; also called
the Schur / Hadamard product theorem).
Completely classical.

Not an open problem. Not a novelty claim.

**Not** the Hadamard *determinant* inequality
`|det A| ≤ ∏ ‖rowᵢ‖₂` — that is consumed
`hadamard-det` (PR **#115**). Do **not**
revive `hadamard_det` / Fischer / Minkowski
det residuals / Hadamard three-lines. **Not**
Schur *complement* (`SchurComplement.lean`
`det_one_add_mul_comm` L395) — already
Mathlib; Weinstein–Aronszajn / matrix-det
lemma; USE `PosSemidef`, do **not** re-prove
the complement identity; do **not** cite it
as the product theorem. **Not** Schur
*partition* / Schur *number* (consumed mill).
**Not** SVD / polar / Moore–Penrose as extra
namesakes (leftover-risk of *this* id).

Mathlib v4.10.0 already has the **Hadamard
product / PSD infra this theorem needs**:

- `Matrix.hadamard` / `⊙`
  (`Data/Matrix/Hadamard.lean` L42;
  `hadamard_apply` L47; `hadamard_one` L104)
- `Matrix.PosSemidef`
  (`LinearAlgebra/Matrix/PosDef.lean` L45)
- `posSemidef_diagonal_iff` (L49)
- `posSemidef_iff_eq_transpose_mul_self` (L252)
- `Matrix.IsHermitian.eigenvalues`
  (`LinearAlgebra/Matrix/Spectrum.lean` L40)
- `Fin n` / `dotProduct`

There is **no** Schur product theorem,
**no** named `schurProduct` / `SchurProduct` /
`schur_product` / `hadamard_posSemidef` /
`posSemidef_hadamard` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/`
(word-regexp this run → ZERO). Do **not**
import `Archive.*`.

OPE-1173 shortlist is **CONSUMED** (#126+#127).
This is a **fresh** catalog-audit id, **not**
a Farey leftover continuation, **not** a
Gale–Shapley leftover, **not** a Hadamard-det
Level B revival, **not** a Schur-complement
re-proof, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third
slot.

Mill NOW: finite PSD-Hadamard theorem after
Gale–Shapley (stable matchings) + Farey
(coprime adjacency). `Matrix.hadamard` is
waiting the same way `Equiv.Perm` waited for
Gale–Shapley. **Not a rubber-stamp of
`hadamard_det`.**

Do **not** describe an attack as discovering
the Schur product theorem. Do **not** expand
into SVD / polar / Moore–Penrose / Fischer
det as extra namesakes (leftover-risk of
*this* id).

## Pinned convention (exact)

**v1 is PSD-preservation of `⊙` on real
square matrices indexed by `Fin n`.** Pin `ℝ`
(not `ℂ`) to keep one-wave. Count / card in
`ℕ`.

Suggested pin:

```text
-- Level A (not labelled Schur / Hadamard product):
-- empty Fin 0; n = 1 nonnegative scalars;
-- diagonal of nonnegative via posSemidef_diagonal_iff;
-- rank-one (v * vᵀ) ⊙ (w * wᵀ) = (v ⊙ w)(v ⊙ w)ᵀ.
-- Not labelled Schur.

open scoped Matrix

theorem posSemidef_hadamard_fin_zero
    (A B : Matrix (Fin 0) (Fin 0) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef

theorem posSemidef_hadamard_fin_one
    (A B : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef

theorem posSemidef_hadamard_diagonal
    {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (diagonal a ⊙ diagonal b).PosSemidef

-- Level B namesake
theorem schur_product {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef
```

Finite `Fin n` is load-bearing. Real `ℝ` (not
`ℂ`) is load-bearing for v1. Hermitian /
`PosSemidef` hypotheses are load-bearing.

**Level A may land only** empty / `n = 1` /
nonnegative diagonal / rank-one outer-product
identity, **not** labelled Schur. Reuse
Mathlib `hadamard` / `PosSemidef` /
`posSemidef_diagonal_iff` /
`posSemidef_iff_eq_transpose_mul_self` —
**do not re-prove** the Hadamard product
definition, PSD, or the spectral theorem.

**Level B** is the namesake: general `n` via
Gram / spectral (`A = Cᵀ * C`, reduce to
rank-one sum). Do not sorry the namesake;
honest partial is allowed (comment residual,
not `sorry`). SVD / polar / Moore–Penrose /
complex form are residual.

## Landmines

1. **Do not re-prove** `Matrix.hadamard` /
   `PosSemidef` / `posSemidef_diagonal_iff` /
   `posSemidef_iff_eq_transpose_mul_self` /
   `IsHermitian.eigenvalues`. Already Mathlib.
   Use them.
2. **This is not** `hadamard-det` (#115) /
   `hadamard_det` Level B / Fischer /
   Minkowski det / Hadamard three-lines.
   Different Hadamard. Do not revive.
3. **This is not** Schur complement /
   Weinstein–Aronszajn /
   `det_one_add_mul_comm` (already-in). Do
   not cite the complement as the product
   theorem.
4. **This is not** Schur partition / Schur
   number (consumed mill). Different Schur
   theorems.
5. **This is not** SVD / polar decomposition
   / Moore–Penrose (Mathlib
   `NonsingularInverse.lean` explicitly
   declines pseudoinverses). Residual of
   *this* id.
6. **This is not** Cauchy–Binet (#117) /
   Birkhoff–von Neumann (#123) /
   expander-mixing spectral leftover /
   Courant–Fischer.
7. **This is not** gale-shapley (#126) /
   farey-sequence (#127) / `farey_adjacent` /
   rural hospitals / Stern–Brocot.
8. **This is not** krenn-gu / hou-zeng-pfc /
   sun-135 / AES / ostrowski / noether
   Level B / frobenius-real-division Level B.
9. **Do not re-prime** the consumed mill list
   (farey-sequence / gale-shapley /
   nash-williams-arboricity /
   birkhoff-von-neumann / hook-length /
   singleton-bound / cauchy-binet /
   bollobas-two-families / schwartz-zippel /
   hadamard-det / ore-hamiltonian /
   bipartite-chromatic-index / ostrowski-q /
   andrasfai-erdos-sos / noether-normalization /
   frobenius-real-division / mason-stothers /
   expander-mixing / zsigmondy /
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

Level A: `Fin 0` empty Hermitian form is
vacuous. `Fin 1` reduces to `0 ≤ a * b` from
`0 ≤ a` and `0 ≤ b`. Diagonal case is
`posSemidef_diagonal_iff` plus entrywise
products. Rank-one: `(v * vᵀ) ⊙ (w * wᵀ)`
has entries `vᵢ wᵢ vⱼ wⱼ`, which is
`(v ⊙ w) * (v ⊙ w)ᵀ`, hence a Gram matrix.
**Not** labelled Schur.

Level B: write `A = Cᵀ * C`
(`posSemidef_iff_eq_transpose_mul_self`);
`A ⊙ B = ∑_k (row_k C)ᵀ (row_k C) ⊙ B`,
each summand `D_k B D_k` for a real diagonal
`D_k`, hence PSD. Cap two levels. No SVD.
No Schur complement re-proof. No
`hadamard_det`.

## Canonical source (pin in this STATEMENT)

I. Schur, *Bemerkungen zur Theorie der
beschränkten Bilinearformen mit unendlich
vielen Veränderlichen*, J. Reine Angew. Math.
140 (1911) 1–28. Compact form: Wikipedia
*Schur product theorem*. Textbook: Horn–
Johnson, *Topics in Matrix Analysis*,
Hadamard products. Type pin: `Matrix.hadamard`
/ `PosSemidef` / `Fin n` / `ℝ`. Hadamard
determinant inequality is a **different**
consumed theorem. Schur complement is a
**different** already-in identity.

## Out of scope

- Complex / `RCLike` form (true, not v1)
- SVD / polar / Moore–Penrose
- Fischer / Minkowski determinant inequalities
  (`hadamard-det` residual)
- Hadamard three-lines
- Schur complement / LDL / Cholesky as namesake
- Continuous Schur multiplier / completely
  positive maps
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
