# Euler's partition theorem (odd parts = distinct parts) — formalize-only

**id:** `euler-odd-distinct`
**ticket:** OPE-553 Scout recommended prime (support OPE-552)
**expected:** known-classical (Euler 1748) — **no novelty claim**

## Why not classical / why formalize-only

Settled 18th-century identity, not an open problem. Mathlib v4.10.0
`Combinatorics/Enumerative/Partition.lean` already defines
`Nat.Partition.odds` and `Nat.Partition.distincts` and the module docstring
says the API exists **to show Euler's partition theorem** — but the file
ends at those `def`s with **no** card-equality theorem under `Mathlib/**`.

`Archive/Wiedijk100Theorems/Partition.lean` already proves
`Theorems100.partition_theorem` via **generating functions / PowerSeries**.
Archive is **not** Mathlib. ProofLab value is a **Glaisher bijection** on
`Nat.Partition` (combinatorial, matching the just-merged Schur–Glaisher
infra). Do **not** transcribe the Archive PowerSeries proof into ProofLab.

Do not describe an attack as discovering Euler's theorem.

## Pinned convention (exact)

Use Mathlib `Nat.Partition n` (multiset of **positive** parts summing to `n`).

```text
def odds (n)      := { p : Partition n | ∀ i ∈ p.parts, ¬ Even i }
def distincts (n) := { p : Partition n | p.parts.Nodup }
```

These are already `Nat.Partition.odds` / `Nat.Partition.distincts`.

**Claim (Euler):**

```text
∀ n : ℕ, (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card
```

**Encoding pin:** Mathlib `Nat.Partition` / `Finset.card`. Do not roll a
custom `List ℕ` partition type. Glaisher map may go through `Multiset ℕ`
then `Partition.ofSums` / `ofMultiset`.

## Landmines

1. **Not Schur partition.** Schur (1926) is distinct parts ≡ 1,2 (mod 3)
   vs parts ≡ ±1 (mod 6). That identity is **already** `theorem schur_partition`
   in `ProofLab/SchurGlaisher.lean`. This bet is the parent odd/distinct
   identity. Do not re-prime Schur.
2. **Do not transcribe Archive GF.** `Theorems100.partition_theorem` is
   generating functions. v1 is an explicit bijection
   (`Finset.card_bij'` / `card_congr`), same shape as SchurGlaisher.
3. **No zero parts.** Mathlib `parts_pos`. Empty partition of `0` is both
   odd and distinct (both cards = 1).
4. **Distinct = `parts.Nodup`**, not “distinct odd parts”
   (`oddDistincts` is a different Finset and is **not** the claim).
5. Glaisher grouping: write each part as `oddPart * 2^val2`; multiplicities
   of a fixed odd kernel on the odds side are the binary digits of the
   distinct-side parts with that kernel. Off-by-one / even-kernel landmines
   fail already at n=2,3,4 — keep a tiny `native_decide` n≤10 card check
   as a Level A guard, not as the proof.

## Proof sketch (classical, Glaisher)

- Distinct → odd: for each part `p = m · 2^k` with `m` odd, contribute
  `2^k` copies of `m`.
- Odd → distinct: for each odd part `m` with multiplicity `c`, expand `c`
  in binary and emit parts `m · 2^i` for bits that are set.
- These are inverse, preserve sum, send Nodup-parts to all-odd parts and
  conversely. Then `Finset.card_bij'`.

Partial: Level A reuse `oddPart`/`val2`/`expandPart` from
`ProofLab/SchurGlaisher.lean` without the mod-6 filter; Level B the
∀n bijection.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/EulerPartition.lean`
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*` / `Theorems100`

## Canonical source

L. Euler, generating-function identity for odd vs distinct parts
(Introductio in analysin infinitorum, 1748). Combinatorial bijection:
J. W. L. Glaisher, *A theorem in partitions*, Messenger of Math. **12**
(1883) 158–170. Type pin: Mathlib `Nat.Partition.odds` /
`Nat.Partition.distincts` (same statement as Archive
`Theorems100.partition_theorem`, different proof).
