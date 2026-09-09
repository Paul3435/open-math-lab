# Fine–Wilf periodicity lemma — formalize-only

**id:** `fine-wilf`
**ticket:** OPE-1268 Formalist Level A (Scout OPE-1263 RECOMMENDED PRIME; Director OPE-1267)
**expected:** known-classical (Fine–Wilf 1965: a word with
periods `p` and `q` of length at least `p+q−gcd(p,q)`
also has period `gcd(p,q)`) — **no novelty claim**

## Why not classical / why formalize-only

Settled combinatorics on words: if a finite word `w`
has periods `p` and `q` (meaning `w[i] = w[i+p]`
whenever both indices are in range, and likewise for
`q`) and `|w| ≥ p + q − gcd(p,q)`, then `w` also has
period `gcd(p,q)`. Completely classical (Fine–Wilf
1965; the bound is sharp).

Not an open problem. Not a novelty claim.

**Not** Kraft's inequality (consumed #138; prefix-free
Kraft sum — **different theorem**; do **not** revive
`kraft_inequality` / McMillan / Huffman / Shannon).
**Not** `List.IsPrefix` / `<+:` as namesake (Kraft
glue; USE if needed; do **not** re-prove). **Not**
Calkin–Wilf (Farey leftover; different Wilf). **Not**
Greene–Nijenhuis–Wilf (hook-length leftover). **Not**
Wilf `χ ≤ 1+λ_max` (expander-mixing residual). **Not**
Lyndon–Schützenberger commuting words (residual of
*this* id; do **not** sorry LS). **Not** cyclic
`List.rotate` / `IsRotated` as namesake (Rotate.lean
glue; a linear period is not a rotation).

Mathlib v4.10.0 already has the **list / gcd infra
this theorem needs**:

- `List.get` / `GetElem` (`Data/List/Basic.lean`)
- `Nat.gcd` (`Data/Nat/GCD/Basic.lean` L12)
- `List.rotate` / `List.IsRotated` (`Rotate.lean` L18)
  — **not** namesake (cyclic vs linear period)
- `List.IsPrefix` / `<+:` (`Infix.lean` L12 / L23)
  — **not** namesake (Kraft glue)

There is **no** named Fine–Wilf theorem, **no**
`fineWilf` / `fine_wilf` / `FineWilf` / `IsPeriod`
(word period) anywhere under `Mathlib/` or `Archive/`
or `ProofLab/` (this run → ZERO on those names;
unrelated Calkin–Wilf / GNW / Wilf-χ hits only).
Do **not** import `Archive.*`.

OPE-1248 shortlist is **CONSUMED**
(#141 sherman-morrison Level A + #142 graham-pollak
Level A). This is a **fresh** catalog-audit id,
**not** a Sherman leftover continuation, **not** a
Graham–Pollak leftover, **not** a Kraft leftover,
**not** a prize leftover, **not** a Formalist Level B
revival, **not** a third slot.

Mill NOW: finite word-period gcd after Sherman–Morrison
(rank-one inverse) + Graham–Pollak (biclique
partition). `List.get` + `Nat.gcd` are waiting the
same way `Matrix.inv` waited for Sherman–Morrison.
**Not a rubber-stamp of Kraft.** **Not a rubber-stamp
of `List.rotate`.**

Do **not** describe an attack as discovering Fine–Wilf.
Do **not** expand into Lyndon–Schützenberger /
critical-factorization / Thue–Morse cube-free as extra
namesakes (LS is leftover-risk of *this* id).

## Pinned convention (exact)

**v1 Level A is the period predicate on named finite
lists: empty `[]`, a constant (period-1) word, and
the length-5 binary word `[0,1,0,1,0]` with periods
2 and 4, not labelled Fine–Wilf.** `p ≠ 0` is
load-bearing. Linear (not cyclic) period is
load-bearing.

Suggested pin:

```text
-- Level A (not labelled Fine–Wilf):
-- empty; constant period 1; [0,1,0,1,0] periods 2 and 4.

def List.IsPeriod {α} (w : List α) (p : ℕ) : Prop :=
  p ≠ 0 ∧ ∀ i, i + p < w.length → w[i]! = w[i + p]!

theorem isPeriod_nil (p : ℕ) (hp : p ≠ 0) :
    ([] : List ℕ).IsPeriod p

theorem isPeriod_replicate_one (n : ℕ) (a : ℕ) (hn : 0 < n) :
    (List.replicate n a).IsPeriod 1

def fineWilfBinary : List (Fin 2) := [0, 1, 0, 1, 0]

theorem isPeriod_fineWilfBinary_two : fineWilfBinary.IsPeriod 2
theorem isPeriod_fineWilfBinary_four : fineWilfBinary.IsPeriod 4
theorem isPeriod_fineWilfBinary_gcd :
    fineWilfBinary.IsPeriod (Nat.gcd 2 4)

-- Level B namesake (all finite words; residual OK)
theorem fine_wilf {α} [DecidableEq α] (w : List α) (p q : ℕ)
    (hp : w.IsPeriod p) (hq : w.IsPeriod q)
    (h : p + q - Nat.gcd p q ≤ w.length) :
    w.IsPeriod (Nat.gcd p q)
```

Finite empty / replicate / length-5 binary is
load-bearing. Linear `IsPeriod` is load-bearing.
`Nat.gcd` is load-bearing.

**Level A may land only** nil / constant period 1 /
`[0,1,0,1,0]` periods 2 and 4 with gcd 2 (optional
extra: a sharpness witness of length `p+q−gcd−1`
that fails the gcd period), **not** labelled Fine–Wilf.
Reuse Mathlib `List.get` / `Nat.gcd` / `List.replicate`
— **do not re-prove** gcd or list get.

**Level B** is the namesake: every finite word with
periods `p,q` long enough has period `gcd(p,q)`.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Lyndon–Schützenberger
is residual.

## Landmines

1. **Do not re-prove** `List.get` / `GetElem` /
   `Nat.gcd` / `List.replicate` / `List.rotate` /
   `List.IsPrefix`.
   Already Mathlib. Use them.
2. **This is not** Kraft / McMillan / Huffman /
   Shannon (consumed #138). Different theorem
   (prefix-free sum vs linear period). Do not cite
   as Fine–Wilf.
3. **This is not** cyclic `List.rotate` / `IsRotated`.
   A linear period is not a rotation. USE rotate only
   as optional extra glue. Do not cite as Fine–Wilf.
4. **This is not** Calkin–Wilf / GNW / Wilf-χ
   (Farey / hook-length / expander leftovers).
5. **This is not** Lyndon–Schützenberger. Residual of
   this id. Do not sorry LS. Do not take LS as
   namesake.
6. **This is not** `sherman-morrison` (#141) /
   Woodbury / SVD.
7. **This is not** `graham-pollak` (#142) / biclique
   cover / Zarankiewicz.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195
   leftover status alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Lyndon–Schützenberger commuting words
- Critical factorization theorem / Thue–Morse cube-free
- Kraft / McMillan / Huffman / Shannon (consumed leftover)
- Prize claims / Millennium / Beal
