# Erdős–Ko–Rado (k-uniform intersecting families) — formalize-only

**id:** `erdos-ko-rado`
**ticket:** OPE-533 Scout recommended prime (support OPE-475)
**expected:** known-classical (Erdős–Ko–Rado 1961) — **no novelty claim**

## Why not classical / why formalize-only

This is a **settled 1961 theorem**, not an open problem. The lab value is a
Lean/Mathlib contribution: Mathlib v4.10.0 has the *non-uniform* intersecting
bound (`Set.Intersecting.card_le`, size ≤ 2^{n−1}) but **not** the k-uniform
EKR bound. Do not describe an attack as discovering EKR.

## Pinned convention (exact)

Let `n k : ℕ` satisfy `2 * k ≤ n` and `1 ≤ k`. Write `[n] := Fin n`.

A family `F` of `k`-subsets of `[n]` is **intersecting** when

```text
∀ A ∈ F, ∀ B ∈ F, A ∩ B ≠ ∅
```

**Claim (EKR):**

```text
F.card ≤ Nat.choose (n - 1) (k - 1)
```

**Star construction (sharpness):** for any `i : Fin n`,

```text
star i := { A : Finset (Fin n) | A.card = k ∧ i ∈ A }
```

is intersecting and has cardinality `Nat.choose (n - 1) (k - 1)`.

**Encoding pin:** ground set `Fin n`; members of `F` are `Finset (Fin n)` of
`card = k`. Alternative `Sym`-encodings are out of scope.

## Landmines

1. **`n ≥ 2k` is load-bearing.** For `n < 2k` every two `k`-sets intersect, so
   the maximum is `C(n,k)`, not `C(n-1, k-1)`.
2. Mathlib `Intersecting.card_le` is **not** this theorem (no uniformity).
3. Uniqueness of stars when `n > 2k` is **not** in v1.
4. Trivial `k = 0` / `k > n`: exclude or dispatch separately; do not let them
   poison the main statement.

## Proof sketch (classical, Katona)

Count pairs `(σ, A)` where `σ` is a cyclic permutation of `[n]` and `A ∈ F`
appears as an interval of length `k` on the cycle. Each `A` sits on
`k! · (n-k)!` cyclic orders as an interval; each cycle contributes at most `k`
interval members of an intersecting family (the `n ≥ 2k` packing). Rearrange
to the choose bound.

Partial: when `n = 2k`, pick at most one of each complementary pair.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/ErdosKoRado.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**

## Canonical source

P. Erdős, C. Ko, R. Rado, *Intersection theorems for systems of finite sets*,
Quart. J. Math. Oxford Ser. (2) **12** (1961) 313–320.
