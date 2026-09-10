# Binary reflected Gray code (length 1 / length 2 / length 3 a listing, formalize-only)

**id:** `gray-code`
**ticket:** OPE-1357 Scout leftover slot #2 (parent OPE-1356;
post langford-pairing #160 + legendre-three-squares #159)
**expected:** known-classical (Frank Gray 1953 / Baudot:
an ordering of all `n`-bit strings in which adjacent
strings differ in exactly one bit exists for every `n`) —
**no novelty claim**

## Why not classical / why formalize-only

Settled enumerative combinatorics / coding: a Gray code of
length `n` is a listing of all `2^n` functions `Fin n → Fin 2`
in which consecutive codewords have Hamming distance 1.
Completely classical (reflected binary Gray code). The
namesake “exists for every n” is a **different**, larger
residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** the Singleton bound (consumed #120; min-distance
cardinality bound ≠ adjacent-distance-1 listing of the
whole space; USE `hammingDist`, do **not** re-prove, do
**not** cite as Gray; do **not** revive Hamming-bound /
Plotkin / MDS). **Not** Ore Hamiltonian (consumed #111;
undirected degree-sum Ham cycle ≠ Hamming listing; do
**not** use `Walk.IsHamiltonian` as namesake; do **not**
revive Bondy–Chvátal). **Not** Kraft (consumed #138;
prefix-free codes ≠ Gray listings; do **not** revive
McMillan / Huffman / Shannon). **Not** Fine–Wilf (consumed
#144; periods ≠ adjacent bit-flips). **Not** Myhill–Nerode
(prime of this shortlist; Nerode classes ≠ Gray listings).
**Not** Langford pairing (consumed #160). **Not** a
hypercube Hamiltonian *graph* theorem (do **not** define
`cubeGraph` / do **not** sorry Ore on the cube).

Mathlib v4.10.0 already has the **Hamming / Pi infra this
theorem needs**:

- `hammingDist` (InformationTheory/Hamming.lean L38)
- `hammingDist_self` L43 / `hammingDist_comm` L52
- `Fin n → Fin 2` / `List` / `List.Nodup` / `Fintype.card`

There is **no** named Gray-code theorem, **no** `GrayCode` /
`grayCode` / `gray_code` / `binaryReflected` / `reflectedGray`
anywhere under `Mathlib/` or `Archive/` or `ProofLab/` (this
run → ZERO on those names; unrelated `gray` variables in
OpenMapping.lean are not this theorem). Do **not** import
`Archive.*`.

OPE-1342 shortlist is **CONSUMED** (#159+#160). This is a
**fresh** catalog-audit leftover id, **not** a Singleton
leftover continuation, **not** an Ore leftover, **not** a
Langford leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite Gray listings leftover beside Nerode
small-language witnesses. `hammingDist` is waiting the same
way `List` / `GetElem` waited for Langford. **Not a
rubber-stamp of Singleton.** **Not a rubber-stamp of Ore.**

Do **not** describe an attack as discovering Gray codes.
Do **not** expand into existence for every `n` as a sorry
(that is leftover-risk of *this* id — do **not** sorry it).
Do **not** label theorems `ore_*` / `hamiltonian_*` /
`singleton_*` as this listing.

## Pinned convention (exact)

**v1 Level A is named small-length Gray listings: length 1
is `![0], ![1]`, length 2 is `00,01,11,10`, and length 3
is the reflected listing, not labelled Gray / Ore /
Singleton.** Adjacent `hammingDist = 1` plus full cover of
`Fin n → Fin 2` is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Gray / Ore / Singleton):
-- named small-length listings.

def IsGrayCode {n : ℕ} (cs : List (Fin n → Fin 2)) : Prop :=
  cs.length = 2 ^ n ∧ cs.Nodup ∧
  (∀ x, x ∈ cs) ∧
  ∀ i, i + 1 < cs.length → hammingDist (cs[i]!) (cs[i+1]!) = 1

theorem gray_one :
    -- length-1 listing of the two functions Fin 1 → Fin 2
    -- adjacent hammingDist 1

theorem gray_two :
    -- 00, 01, 11, 10
    -- each adjacent step flips one bit; all four vectors appear

theorem gray_three :
    -- binary-reflected length-3 listing
    -- 000,001,011,010,110,111,101,100

-- optional extra: n=0 unique empty-domain function, list length 1

-- Level B namesake (exists for every n; residual OK)
theorem gray_code :
    ∀ n : ℕ, ∃ cs, IsGrayCode (n := n) cs
    -- do not sorry the namesake
```

Named small-length listings are load-bearing.
Cover + adjacent distance 1 are load-bearing
(so the theorem is **not** “some binary lists exist”).

**Level A may land only** the length-1 / length-2 /
length-3 listings (optional extra: `n=0`),
**not** labelled Gray / Ore / Singleton. Reuse Mathlib
`hammingDist` — **do not re-prove** Singleton bounds /
Ore cycles / Fine–Wilf periods.

**Level B** is the namesake existence for every `n`. Do
not sorry the namesake; honest partial is allowed (comment
residual, not `sorry`). Hypercube Hamiltonian extras are
residual.

## Landmines

1. **Do not re-prove** `hammingDist` / `hammingDist_self` /
   `List.Nodup`. Already Mathlib. Use them if needed.
2. **This is not** Singleton / Hamming-bound / Plotkin /
   MDS (consumed #120 residual). USE `hammingDist`; do not
   sorry those bounds.
3. **This is not** Ore / Dirac / Bondy–Chvátal (consumed
   #111 leftover). Do not use `Walk.IsHamiltonian` as
   namesake. Do not define `cubeGraph` as the theorem.
4. **This is not** Kraft / McMillan / Huffman / Shannon
   (consumed #138).
5. **This is not** Fine–Wilf / Lyndon–Schützenberger
   (consumed #144).
6. **This is not** `myhill-nerode` (prime of this
   shortlist). Do not prove Nerode here.
7. **This is not** Langford / Skolem (consumed #160).
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Gray namesake (exists for every `n`)
- Hypercube Hamiltonian / Ore on the cube / Beckett–Gray
- Prize claims / Millennium / Beal
