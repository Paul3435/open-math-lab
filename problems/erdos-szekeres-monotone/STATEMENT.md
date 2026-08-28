# Finite Erdős–Szekeres monotone subsequence theorem (formalize-only)

**id:** `erdos-szekeres-monotone`  
**ticket:** OPE-433 (wave prime from Scout OPE-430)  
**status target:** `formalized` (Lean zero-sorry) — **no novelty claim**

## Convention pin (mandatory)

**Weak** monotonicity only:

- increasing ≜ `List.Sorted (· ≤ ·)` (nondecreasing / weakly increasing)
- decreasing ≜ `List.Sorted (· ≥ ·)` (nonincreasing / weakly decreasing)

Subsequences are realized as value-lists of finite index-sets ordered by
`Finset.sort (· ≤ ·)` (strictly increasing indices). This matches Mathlib's
`List.Sorted` vocabulary (`Mathlib.Data.List.Sort`).

**Distinctness is not required** for the weak form: the classical
`(r-1)(s-1)+1` bound holds for arbitrary sequences in a linear order.
(When values are pairwise distinct, weak and strict coincide.)

Do **not** silently switch to strict `<` / `>` without a separate theorem and
proof; the strict form also holds classically under distinctness, but that is
out of scope for OPE-433.

## Informal statement

For integers `r, s ≥ 0` and any linear order `α`, every sequence
`f : Fin n → α` with

```text
n ≥ (r - 1) * (s - 1) + 1
```

admits either

- a weakly increasing subsequence of length `r`, or
- a weakly decreasing subsequence of length `s`.

Equivalent classical packaging (Erdős–Szekeres 1935): every sequence of more
than `a·b` distinct reals has a monotone increasing subsequence of length
`a+1` or a monotone decreasing subsequence of length `b+1`
(set `r = a+1`, `s = b+1`).

## Lean statement (ProofLab)

File: `proofs/lean-project/ProofLab/ErdosSzekeres.lean`  
Namespace: `ProofLab.ErdosSzekeres`

```lean
theorem erdosSzekeres_monotone {α : Type*} [LinearOrder α] {n r s : ℕ}
    (h : (r - 1) * (s - 1) + 1 ≤ n) (f : Fin n → α) :
    (∃ l : List α, r ≤ l.length ∧ l.Sorted (· ≤ ·)) ∨
      (∃ l : List α, s ≤ l.length ∧ l.Sorted (· ≥ ·))
```

Supporting API:

- `IsIncEnding` / `IsDecEnding` — index-set witnesses ending at a given position
- `incLen` / `decLen` — longest weak-inc / weak-dec ending lengths
- `erdosSzekeres_card_bound` — quantitative pigeonhole form
- `valuesOf` — `Finset.sort` then `map f` → `List.Sorted` subsequence

## Proof sketch

Classic length-labelling + pigeonhole (same profile as OPE-44 R(3,3)):

1. For each index `i`, let `a(i)` = length of a longest weakly increasing
   subsequence ending at `i`, `b(i)` dual for decreasing (via finite `Finset.sup`
   over ending index-sets).
2. Singleton `{i}` shows `a(i), b(i) ≥ 1`.
3. If `i < j` and `f i ≤ f j`, then `a(i) < a(j)` (extend an optimal ending set
   at `i` by inserting `j`). Dual for decreasing when `f j ≤ f i`.
4. Hence `i ↦ (a(i)-1, b(i)-1)` is injective into `Fin (r-1) × Fin (s-1)` under
   the assumption that no ending length reaches `r` / `s`.
5. `Fintype.card_le_of_injective` ⇒ `n ≤ (r-1)(s-1)`, contradicting the
   hypothesis `n ≥ (r-1)(s-1)+1`.

Zero witness search; no offline compute; no `native_decide` enumeration.

## References

- Erdős & Szekeres, "A combinatorial problem in geometry",
  *Compositio Mathematica* **2** (1935) 463–470.
- Mathlib pin v4.10.0: only **infinitary** ES content
  (`OrderIsoNat.lean` ~L182; `WellFoundedSet.lean` monotone-subsequence remark).
  Finite theorem is a genuine gap under `Mathlib/`.

## Novelty / claim policy

- `expected: known-classical` → **formalize-only**.
- Default **no claim**. Board gates any external communication.
- Value = Lean-checked Mathlib-gap formalization, not a research discovery.
