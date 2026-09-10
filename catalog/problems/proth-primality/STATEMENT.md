# Proth's theorem (primality of k·2ⁿ+1) — formalize-only

**id:** `proth-primality`
**ticket:** OPE-1294 Scout leftover slot #2 (parent OPE-1293;
post platonic-solids #147 + egyptian-fractions #148)
**expected:** known-classical (Proth 1878: if `N = k·2ⁿ+1` with
`k` odd and `k < 2ⁿ`, and some `a` satisfies
`a^{(N-1)/2} ≡ −1 (mod N)`, then `N` is prime) —
**no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory: a Proth number
`N = k·2ⁿ + 1` (`k` odd, `k < 2ⁿ`, `n > 0`) that admits a
Proth witness `a^{(N-1)/2} ≡ −1 (mod N)` is prime. Completely
classical (François Proth 1878; Pocklington-family sufficiency).

Not an open problem. Not a novelty claim.

**Not** Euler's criterion (`euler_criterion`
LegendreSymbol/Basic.lean L58: for *prime* `p`, nonzero `a` is
a square iff `a^{p/2} = 1` — **different direction**; **USE**
`ZMod` / `pow` glue, do **not** re-prove, do **not** cite as
Proth). **Not** Lucas–Lehmer (`LucasLehmer.lean`
`lucas_lehmer_sufficiency` L476 already-in; Mersenne `2^p−1` ≠
Proth `k·2ⁿ+1`). **Not** Korselt / Carmichael (consumed
`korselt-carmichael`; compositeness criterion ≠ Proth
sufficiency). **Not** Euclid–Euler even perfect / Mersenne
(consumed). **Not** Wantzel / Gauss–Wantzel constructible
regular polygons / Fermat numbers as namesake (consumed #133;
Fermat `2^{2^m}+1` is a *special* Proth number — residual of
*this* id; do **not** sorry Gauss–Wantzel / Pépin). **Not**
platonic-solids / egyptian-fractions (consumed #147+#148).
**Not** Frucht graph Aut (prime of this shortlist).

Mathlib v4.10.0 already has the **modular / primality infra
this theorem needs**:

- `ZMod` / `Nat.Prime` / `Nat.Odd`
- `Pow` on `ZMod`
- `euler_criterion` (Basic.lean L58) — **not** namesake
- `lucas_lehmer_sufficiency` (LucasLehmer.lean L476) —
  **different** Mersenne test; do **not** re-prove

There is **no** named Proth theorem, **no** `proth` /
`Proth` / `ProthWitness` / `prothPrime` / `Pépin` /
`Pocklington` anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names). Do **not**
import `Archive.*`.

OPE-1278 shortlist is **CONSUMED** (#147+#148). This is a
**fresh** catalog-audit leftover id, **not** an Egyptian
leftover continuation, **not** a Korselt leftover, **not** a
Lucas–Lehmer leftover, **not** a Wantzel leftover, **not** a
prize leftover, **not** a Formalist Level B revival, **not** a
third slot.

Mill NOW: finite Proth witnesses leftover beside Frucht graph
Aut. `ZMod` / `pow` are waiting the same way `Rat` waited for
Egyptian fractions. **Not a rubber-stamp of Euler's
criterion.** **Not a rubber-stamp of Lucas–Lehmer.**

Do **not** describe an attack as discovering Proth's theorem.
Do **not** expand into Pépin / Fermat numbers / Gauss–Wantzel
regular n-gons / Pocklington as extra namesakes (Pépin is
leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the Proth-form + witness predicate on named
integers: `3 = 1·2¹+1` witness `2`, `5 = 1·2²+1` witness `2`,
and `13 = 3·2²+1` witness `2`, not labelled Proth.** Odd `k`
and `k < 2ⁿ` are load-bearing. `ZMod` power `= -1` is
load-bearing.

Suggested pin:

```text
-- Level A (not labelled Proth):
-- 3 / 5 / 13 are Proth form with witness 2.

def IsProth (N k n : ℕ) : Prop :=
  N = k * 2 ^ n + 1 ∧ Odd k ∧ 0 < n ∧ k < 2 ^ n

def ProthWitness (N a : ℕ) : Prop :=
  0 < a ∧ ((a : ZMod N) ^ ((N - 1) / 2) = -1)

theorem proth_three :
    IsProth 3 1 1 ∧ ProthWitness 3 2

theorem proth_five :
    IsProth 5 1 2 ∧ ProthWitness 5 2

theorem proth_thirteen :
    IsProth 13 3 2 ∧ ProthWitness 13 2

-- optional extra: 9 = 1*2^3+1 is Proth *form* but ¬ Prime 9
-- (not the converse; do not claim unattested composites)

-- Level B namesake (sufficiency; residual OK)
theorem proth_primality {N k n a : ℕ}
    (h : IsProth N k n) (w : ProthWitness N a) :
    Nat.Prime N
```

Named Proth numbers are load-bearing.
`IsProth` arithmetic is load-bearing.
`ZMod` witness `= -1` is load-bearing.

**Level A may land only** `3` / `5` / `13` form+witness
(optional extra: `9` is Proth form and composite), **not**
labelled Proth. Reuse Mathlib `ZMod` / `pow` / `Odd` /
`Nat.Prime` — **do not re-prove** Euler's criterion /
Lucas–Lehmer.

**Level B** is the namesake: Proth form + witness ⇒ prime.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Pépin / Fermat numbers /
Gauss–Wantzel / Pocklington are residual.

## Landmines

1. **Do not re-prove** `ZMod` / `pow` / `Odd` / `Nat.Prime` /
   `euler_criterion` / `lucas_lehmer_sufficiency`.
   Already Mathlib. Use them if needed.
2. **This is not** Euler's criterion. Prime-modulus quadratic
   residuosity ≠ Proth sufficiency. Different direction.
   Do not cite as Proth.
3. **This is not** Lucas–Lehmer / Mersenne. Already-in
   different test. Do not cite as Proth.
4. **This is not** Korselt / Carmichael (consumed).
5. **This is not** Wantzel / Gauss–Wantzel / Fermat-prime
   regular polygons (consumed #133). Fermat numbers are a
   special Proth family — residual of this id. Do not sorry
   Pépin / Gauss–Wantzel.
6. **This is not** Euclid–Euler even perfect / Mersenne
   (consumed).
7. **This is not** `frucht-graph-aut` (OPE-1294 prime).
   Do not prove Frucht here.
8. **This is not** platonic-solids / egyptian-fractions
   (consumed #147+#148) / Farey / Kraft.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Proth namesake (form + witness ⇒ prime)
- Pépin's test / Fermat numbers as namesake
- Gauss–Wantzel constructible regular polygons
- Pocklington's theorem
- Prize claims / Millennium / Beal
