# Orthogonal Latin squares (order 2 none / order 3 a pair, formalize-only)

**id:** `orthogonal-latin-squares`
**ticket:** OPE-1326 Scout leftover slot #2 (parent OPE-1325;
post alcuin-integer-triangles #153 + cannonball-square-pyramid #154)
**expected:** known-classical (Euler 1782 Graeco-Latin squares:
two Latin squares of the same order are orthogonal when the
ordered pairs of symbols cover the full product; order 3 admits
a pair, order 2 admits none) —
**no novelty claim**

## Why not classical / why formalize-only

Settled enumerative combinatorics: an `n×n` Latin square is an
`n`-symbol filling with each symbol once per row and once per
column; two Latin squares `A, B` are orthogonal when
`(A i j, B i j)` runs through all of `[n] × [n]` as `(i, j)`
does. Completely classical (Euler; affine plane of order 3).
Euler's officers / “no pair of order 6” is a **different**,
larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** projective planes (`Configuration.ProjectivePlane`,
Configuration.lean L329 already-in; Fano / order-2 plane is a
**different** incidence structure — **USE** as glue if needed, do
**not** re-prove, do **not** cite as Latin squares). **Not** de
Bruijn–Erdős incidence (`HasLines.card_le` L211 already-in).
**Not** Birkhoff–von Neumann (consumed #123; doubly stochastic /
permutation convex hull ≠ Latin orthogonality; do **not** revive
Gale–Ryser). **Not** Gale–Shapley (consumed #126; matching ≠
Latin). **Not** Cayley trees / `Equiv.Perm` as namesake
(`Equiv.Perm` HIT as row-permutation glue **not** namesake).
**Not** Alcuin integer triangles (consumed #153). **Not**
cannonball square-pyramid (consumed #154). **Not** Jordan
canonical form (prime of this shortlist).

Mathlib v4.10.0 already has the **Fin / permutation infra this
theorem needs**:

- `Fin n` / addition / multiplication
- `Function.Injective`
- `Equiv.Perm` — **not** namesake (row of a Latin square is a
  permutation)
- `Configuration.ProjectivePlane` (L329) — **different**
  incidence glue; do **not** re-prove
- `HasLines.card_le` (L211) — **different** de Bruijn–Erdős

There is **no** named Latin-square / orthogonal-Latin /
Graeco-Latin theorem, **no** `latinSquare` / `LatinSquare` /
`IsLatinSquare` / `orthogonalLatin` / `graecoLatin` /
`GraecoLatin` anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names). Do **not** import
`Archive.*`.

OPE-1310 shortlist is **CONSUMED** (#153+#154). This is a
**fresh** catalog-audit leftover id, **not** an Alcuin leftover
continuation, **not** a cannonball leftover, **not** a
projective-plane leftover, **not** a BvN leftover, **not** a
prize leftover, **not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite Latin-square witnesses leftover beside Jordan
2×2 blocks. `Fin` / `Function.Injective` are waiting the same
way `Nat` waited for Alcuin. **Not a rubber-stamp of
ProjectivePlane.** **Not a rubber-stamp of Equiv.Perm.**

Do **not** describe an attack as discovering Euler's officers.
Do **not** expand into existence of `n−1` MOLS / projective
planes of order `n` / the `n ≠ 2, 6` classification / Bose–
Shrikhande–Parker as a sorry (those are leftover-risk of *this*
id — do **not** sorry them).

## Pinned convention (exact)

**v1 Level A is the Latin-square predicate on named small
orders: order 2 has no orthogonal pair, and order 3 has the
affine pair `L_k(i,j) = i + k*j` for `k = 1, 2`, not labelled
Euler / Graeco-Latin.** Row/column injectivity and the pair map
`(A, B)` injective on `Fin n × Fin n` are load-bearing.

Suggested pin:

```text
-- Level A (not labelled Euler / Graeco-Latin):
-- named small orders.

def IsLatinSquare {n : ℕ} (A : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Injective (A i)) ∧
  (∀ j, Function.Injective (fun i => A i j))

def Orthogonal {n : ℕ} (A B : Fin n → Fin n → Fin n) : Prop :=
  Function.Injective (fun p : Fin n × Fin n => (A p.1 p.2, B p.1 p.2))

def affineLatin {n : ℕ} [NeZero n] (k : Fin n)
    (i j : Fin n) : Fin n := i + k * j

theorem latin_cyclic_three :
    IsLatinSquare (affineLatin (1 : Fin 3))

theorem mols_order_three :
    IsLatinSquare (affineLatin (1 : Fin 3)) ∧
    IsLatinSquare (affineLatin (2 : Fin 3)) ∧
    Orthogonal (affineLatin (1 : Fin 3)) (affineLatin (2 : Fin 3))

theorem no_mols_order_two :
    ∀ A B : Fin 2 → Fin 2 → Fin 2,
      ¬ (IsLatinSquare A ∧ IsLatinSquare B ∧ Orthogonal A B)

-- optional extra: the cyclic table of order 2 is Latin
--   (exactly one reduced Latin square of order 2)

-- Level B namesake (MOLS classification / Euler officers; residual OK)
theorem orthogonal_latin_squares :
    (∃ pair of MOLS of order n) ↔ n ≠ 2 ∧ n ≠ 6
    -- do not sorry the namesake; Bose–Shrikhande–Parker residual
```

Named small orders are load-bearing.
`IsLatinSquare` row **and** column injectivity is load-bearing
(so a row-Latin rectangle is **not** a Latin square).
`Orthogonal` covering all pairs is load-bearing.

**Level A may land only** order-2 nonexistence / order-3 affine
pair (optional extra: cyclic order-2 is Latin), **not** labelled
Euler. Reuse Mathlib `Fin` / `Function.Injective` —
**do not re-prove** `Equiv.Perm` / `ProjectivePlane` /
`HasLines.card_le`.

**Level B** is the namesake existence classification (including
Euler's officers / order 6). Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`). Projective
planes of every order / MacNeish extras are residual.

## Landmines

1. **Do not re-prove** `Fin` arithmetic / `Function.Injective` /
   `Equiv.Perm` / `ProjectivePlane` / `HasLines.card_le`.
   Already Mathlib. Use them if needed.
2. **This is not** a projective plane. Affine MOLS of order 3
   are a different encoding. Do not cite as Latin squares.
3. **This is not** de Bruijn–Erdős incidence (already-in).
4. **This is not** Birkhoff–von Neumann / Gale–Ryser (consumed
   #123). Permutation matrices ≠ orthogonal Latin pairs.
5. **This is not** Gale–Shapley (consumed #126).
6. **This is not** Cayley trees / `Equiv.Perm` as namesake.
7. **This is not** `jordan-canonical-form` (OPE-1326 prime).
   Do not prove Jordan form here.
8. **This is not** alcuin-integer-triangles / cannonball-square-pyramid
   (consumed #153+#154) / Frucht / Proth / magic squares as
   namesake (Lo Shu residual of *this* id — do **not** sorry it).
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Orthogonal-Latin namesake (existence for every `n ≠ 2, 6`)
- Euler's 36 officers / Bose–Shrikhande–Parker
- `n−1` MOLS iff projective plane of order `n`
- Magic squares / Lo Shu as extra namesakes
- Prize claims / Millennium / Beal
