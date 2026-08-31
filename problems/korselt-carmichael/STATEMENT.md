# Korselt's criterion for Carmichael numbers (formalize-only)

**id:** `korselt-carmichael`
**ticket:** OPE-804 Scout leftover slot #2 (support OPE-803; post Vosper #82 + Heron #83)
**expected:** known-classical (Korselt 1899 / Carmichael 1910) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary-NT characterization: a composite `n > 1`
is a **Carmichael number** (Fermat pseudoprime to every base
coprime to `n`) if and only if `n` is squarefree and
`p − 1 ∣ n − 1` for every prime `p ∣ n`. Not an open
problem.

Mathlib v4.10.0 already has the **arithmetic this theorem
needs**:

- `Nat.FermatPsp` / `Nat.ProbablePrime`
  (`NumberTheory/FermatPsp.lean`) — Fermat pseudoprime to a
  **single** base. File comment this pin: Carmichael numbers
  are **"not yet defined in this file"**. That comment **is**
  the gap.
- `Squarefree` / `Nat.squarefree_iff_nodup_primeFactorsList`
  (`Data/Nat/Squarefree.lean`)
- `ZMod.chineseRemainder` (`Data/ZMod/Basic.lean`) and
  `Nat.chineseRemainder` (`Data/Nat/ChineseRemainder.lean`)
- Fermat–Euler `Nat.ModEq.pow_totient` /
  `ZMod.pow_totient` (`FieldTheory/Finite/Basic.lean`)
- Fermat's little theorem (special case of totient)

There is **no** `IsCarmichael`, **no** Korselt criterion,
and **no** "pseudoprime to all bases" characterization
anywhere under `Mathlib/` or `Archive/` (word-regexp
`Carmichael` / `korselt` this run → **one** hit: the
FermatPsp comment that they are not yet defined). ProofLab
has Euclid–Euler even-perfect (`even_perfect_iff`) —
**different** theorem (consumed #80). This is **not** a
re-prime of Euclid–Euler, **not** odd-perfect / aliquot /
Lucas–Lehmer, **not** FLT `n=3`/`n=4` (already Mathlib
`NumberTheory/FLT/{Three,Four}.lean`).

OPE-788 / OPE-770 never considered this id. Fresh leftover
after the Euclid–Euler NT leftover was **CONSUMED** (#80)
and the geometry leftover Heron was **CONSUMED** (#83). Mill:
elementary NT characterization after a combinatorial prime
— **not** a third additive theorem (Mann/Heilbronn refused),
**not** a Heron-C Euclidean leftover.

Do **not** describe an attack as discovering Carmichael
numbers. Do **not** prove infinitude (Alford–Granville–
Pomerance 1994 is a **different**, much harder theorem —
**out of v1**). Do **not** expand into the Carmichael
function `λ(n)`.

## Pinned convention (exact)

**v1 is Korselt's iff**, not infinitude, not `λ(n)`.
Carmichael = composite + Fermat test to every coprime base.
Reuse `Nat.ProbablePrime` / `Nat.FermatPsp` rather than
re-stating the congruence.

```text
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → Nat.ProbablePrime n a

def Korselt (n : ℕ) : Prop :=
  Squarefree n ∧ ¬ n.Prime ∧ 1 < n ∧
    ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1

theorem korselt {n : ℕ} : IsCarmichael n ↔ Korselt n
```

`1 < n` and `¬ n.Prime` are load-bearing: primes satisfy
Fermat `a^{p-1} ≡ 1 (mod p)` for `p ∤ a`, so the composite
clause is what makes the namesake nontrivial. Squarefree is
load-bearing on the Korselt side (a prime-square fails the
Fermat test to a suitable base).

**Level A may land only one direction**, not labelled
Korselt: `IsCarmichael n → Squarefree n` (or the full
`IsCarmichael → Korselt` easy direction via order of
units / FermatPsp coprimeness). **Level B** is the converse
`Korselt → IsCarmichael` (CRT on the prime factors +
`pow_totient` / Fermat) and the bundled namesake `korselt`.

## Landmines

1. **Do not prove infinitude.** Alford–Granville–Pomerance
   1994 is out of v1. `Nat.exists_infinite_pseudoprimes`
   (FermatPsp to a **fixed** base) is already Mathlib —
   **different** theorem; do not re-prove it as this
   namesake.
2. **This is not the Carmichael function `λ(n)`.** Out of v1.
3. **This is not Euclid–Euler / even perfect.** Consumed
   PR **#80**. Do not re-prime. Odd-perfect / aliquot /
   Lucas–Lehmer stay banned.
4. **This is not FLT.** `NumberTheory/FLT/Three.lean` and
   `Four.lean` are already Mathlib. Never cite as a gap.
5. **This is not Fermat–Euler totient.** Already
   `Nat.ModEq.pow_totient`. Use it; do not re-prove it.
6. **This is not Wilson / Lucas binomial / Euler criterion /
   quadratic reciprocity.** Already Mathlib.
7. **Do not re-prime** vosper-cauchy-davenport / heron-formula
   / euclid-euler-perfect / bipartite-odd-cycle / moore /
   stirling / kst / pentagonal / sunflower /
   combinatorial-nullstellensatz / kruskal-katona / oddtown /
   cayley / mycielski / friendship / havel / menger / greedy /
   Brooks / Dilworth / Eulerian / König / Dirac / EKR.
8. **No `Archive.*` import.**
9. **Leave OPE-403 alone.**

## Proof sketch (classical, Korselt)

Level A: `IsCarmichael → Squarefree`. If `p^2 ∣ n`, a
suitable base coprime to `n` fails `a^{n-1} ≡ 1 (mod p^2)`
(lift Fermat / binomial). Easy `IsCarmichael → ∀ p∣n,
p−1 ∣ n−1` by taking a primitive root mod `p` (Mathlib
`IsCyclic (ZMod p)ˣ` / finite-field units — **already
upstream**; never cite as this gap) whose order `p−1` then
divides `n−1`. **Not** labelled Korselt.

Level B: converse. Write `n` as a product of distinct primes
(squarefree). CRT (`ZMod.chineseRemainder` iterated) reduces
`a^{n-1} ≡ 1 (mod n)` to the system `a^{n-1} ≡ 1 (mod p)`
for each `p∣n`. For `p ∤ a`, Fermat + `p−1 ∣ n−1` gives
the congruence. Cap two levels. No infinitude, no `λ(n)`,
no odd-perfect.

## Canonical source (pin in this STATEMENT)

A. Korselt, *Problème mathématique*, L'intermédiaire des
mathématiciens **6** (1899), 143. R. D. Carmichael, *Note
on a new number theory function*, Amer. Math. Monthly **17**
(1910), 132–136. Type pin: `Nat.ProbablePrime` /
`Nat.FermatPsp` + new `IsCarmichael` + `Squarefree` +
`p−1 ∣ n−1`. FermatPsp-to-a-fixed-base infinitude,
Fermat–Euler totient, Euclid–Euler even-perfect, FLT n=3/4,
and `λ(n)` are **different** statements, not this claim.

## Out of scope

- Infinitude of Carmichael numbers (AGP 1994)
- Carmichael function `λ(n)`
- Re-proving FermatPsp infinitude-to-a-base / totient / FLT
- Odd-perfect / aliquot / Lucas–Lehmer / Euclid–Euler re-prime
- Re-primes listed above
- Novelty / external claim
