# Langford pairing (order 1 none / order 2 none / order 3 a witness, formalize-only)

**id:** `langford-pairing`
**ticket:** OPE-1342 Scout leftover slot #2 (parent OPE-1341;
post jordan-canonical-form #156 + orthogonal-latin-squares #157)
**expected:** known-classical (C. Dudley Langford 1958: a
sequence that is a permutation of `{1,1,…,n,n}` in which the
two copies of `k` have exactly `k` entries between them exists
iff `n ≡ 0 or 3 (mod 4)`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled enumerative combinatorics: a Langford pairing of order
`n` is a list of length `2n` containing each `k ∈ {1,…,n}`
twice, with exactly `k` entries strictly between the two
copies of `k`. Completely classical (Langford 1958; existence
characterization `n ≡ 0 or 3 (mod 4)`). The namesake “exists
for every such n” is a **different**, larger residual — do
**not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** Skolem sequences (two copies of `k` at distance `k`,
exists iff `n ≡ 0 or 1 (mod 4)` — **different** theorem;
residual of this id; do **not** sorry Skolem). **Not**
Skolem–Mahler–Lech / Skolemization (name collision only).
**Not** Fine–Wilf (consumed #144; linear periods ≠ between-
counts; do **not** revive Lyndon–Schützenberger). **Not**
orthogonal Latin squares (consumed #157; Latin orthogonality
≠ Langford between-counts; do **not** revive Euler officers /
`n≠2,6` / magic squares / Lo Shu). **Not** Jordan canonical
form (consumed #156). **Not** Alcuin integer triangles
(consumed #153). **Not** graceful trees (heuristic mill;
vertex labels ≠ Langford). **Not** Kraft prefix-free codes
(consumed #138).

Mathlib v4.10.0 already has the **list / Fin infra this
theorem needs**:

- `List` / `List.length` / `GetElem` / `List.get`
- `Finset.Icc` / `List.filter` / `List.count`
- `Nat` arithmetic (`j = i + k + 1`)

There is **no** named Langford / Skolem-sequence theorem,
**no** `langford` / `Langford` / `LangfordPairing` /
`skolemSequence` / `SkolemSequence` anywhere under `Mathlib/`
or `Archive/` or `ProofLab/` (this run → ZERO on those names).
Do **not** import `Archive.*`.

OPE-1326 shortlist is **CONSUMED** (#156+#157). This is a
**fresh** catalog-audit leftover id, **not** an OLS leftover
continuation, **not** a Fine–Wilf leftover, **not** a
Jordan leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite Langford witnesses leftover beside three-
square small-n. `List` / `GetElem` are waiting the same way
`Fin` / `Function.Injective` waited for OLS. **Not a
rubber-stamp of Fine–Wilf.** **Not a rubber-stamp of OLS.**

Do **not** describe an attack as discovering Langford pairings.
Do **not** expand into existence iff `n ≡ 0 or 3 (mod 4)` as
a sorry (that is leftover-risk of *this* id — do **not**
sorry it). Do **not** label theorems `skolem_*` (Skolem–
Mahler–Lech / Skolemization collision).

## Pinned convention (exact)

**v1 Level A is named small-order Langford witnesses: order 1
has none, order 2 has none, and order 3 has `[2,3,1,2,1,3]`,
not labelled Langford / Skolem.** Between-count `k` (so the
indices differ by `k+1`) is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Langford / Skolem):
-- named small-order witnesses.

def IsLangford (w : List ℕ) (n : ℕ) : Prop :=
  w.length = 2 * n ∧
  (∀ k, 1 ≤ k ∧ k ≤ n → (w.filter (· = k)).length = 2) ∧
  (∀ k, 1 ≤ k ∧ k ≤ n →
    ∃ i j : ℕ, i < j ∧ j = i + k + 1 ∧
      w[i]? = some k ∧ w[j]? = some k)

theorem langford_one_none : ¬ ∃ w, IsLangford w 1
    -- 2n=2 cannot place two 1s with 1 between

theorem langford_two_none : ¬ ∃ w, IsLangford w 2

theorem langford_three :
    IsLangford [2, 3, 1, 2, 1, 3] 3
    -- 1s at 3,5 (one between); 2s at 1,4; 3s at 2,6

-- optional extra: an order-4 witness

-- Level B namesake (exists iff n ≡ 0 or 3 mod 4; residual OK)
theorem langford_pairing :
    ∀ n : ℕ, (∃ w, IsLangford w n) ↔ n % 4 = 0 ∨ n % 4 = 3
    -- do not sorry the namesake
```

Named small-order witnesses are load-bearing.
`langford_one_none` / `langford_two_none` are load-bearing
(so the theorem is **not** “some sequences exist”).

**Level A may land only** the order-1 none / order-2 none /
order-3 witness (optional extra: one order-4 witness),
**not** labelled Langford / Skolem. Reuse Mathlib `List` /
`GetElem` — **do not re-prove** Fine–Wilf periods / Latin
squares.

**Level B** is the namesake existence characterization. Do
not sorry the namesake; honest partial is allowed (comment
residual, not `sorry`). Skolem sequences extras are residual.

## Landmines

1. **Do not re-prove** `List.get` / `GetElem` / `List.filter`.
   Already Mathlib. Use them if needed.
2. **This is not** Skolem sequences (distance `k`, different
   modulus). Residual of this id. Do not sorry Skolem. Do not
   label theorems `skolem_*`.
3. **This is not** Fine–Wilf / Lyndon–Schützenberger
   (consumed #144; periods ≠ between-counts).
4. **This is not** orthogonal Latin squares / Euler officers /
   magic squares / Lo Shu (consumed #157).
5. **This is not** `legendre-three-squares` (prime of this
   shortlist). Do not prove three-square here.
6. **This is not** graceful trees / Alcuin / Kraft.
7. **Do not** re-prime the consumed mill list.
8. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
9. **Do not import `Archive.*`.**
10. Default no claim. No novelty claim.

## Out of v1

- Langford namesake (exists iff `n ≡ 0 or 3 (mod 4)`)
- Skolem sequences / hooked Langford / Nickerson variants
- Prize claims / Millennium / Beal
