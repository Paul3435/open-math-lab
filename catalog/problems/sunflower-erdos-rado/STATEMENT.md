# Erdős–Rado sunflower lemma — classical factorial bound (formalize-only)

**id:** `sunflower-erdos-rado`
**ticket:** OPE-717 Scout recommended prime (support OPE-716; post kruskal-katona #67 + oddtown #68)
**expected:** known-classical (Erdős–Rado 1960) — **no novelty claim**

## Why not classical / why formalize-only

Settled Δ-system / sunflower bound: an `r`-uniform family larger than
`r! (k-1)^r` contains a sunflower with `k` petals. Not an open problem.
The **sunflower conjecture** (Erdős–Rado: a `(k-1)^r poly(r)` bound)
is **open** and is **out of v1** — do not attack it; do not describe
this id as the conjecture.

Mathlib v4.10.0 has `Finset`, `SetFamily` compression / shadow / shatter
(Pajor–Sauer–Shelah `card_le_card_shatterer` is a **different** theorem,
already upstream). There is **no** sunflower / Δ-system / Erdős–Rado
sunflower ident anywhere under `Mathlib/` or `Archive/` (word-regexp
this run → ZERO files). ProofLab has EKR, Oddtown, Kruskal–Katona —
**different** theorems (intersecting families / GF(2) parity / colex
shadows). This is **not** a re-prime of those ids.

Do **not** describe an attack as discovering the sunflower lemma.
Do **not** expand into the 2021 Alweiss–Lovett–Wu–Zhang improved bound,
Eventown, Fisher / BIBD, Hilton–Milner, or Kruskal–Katona-C.

## Pinned convention (exact)

**Uniform pin:** every member has card `r`. Ground type `α` with
`DecidableEq`. Family `𝒜 : Finset (Finset α)`.

**Sunflower / Δ-system pin:** pairwise intersections equal a common
core. Empty core allowed (pairwise disjoint petals). `|𝒜| ≤ 1` is
vacuously a sunflower (no pairs).

```text
def IsSunflower {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) : Prop :=
  ∃ core : Finset α, ∀ ⦃s t⦄, s ∈ 𝒜 → t ∈ 𝒜 → s ≠ t → s ∩ t = core

theorem erdos_rado_sunflower {α : Type*} [DecidableEq α]
    {r k : ℕ} {𝒜 : Finset (Finset α)}
    (hr : ∀ s ∈ 𝒜, s.card = r)
    (hk : 1 ≤ k)
    (hcard : Nat.factorial r * (k - 1) ^ r < 𝒜.card) :
    ∃ 𝒮 ⊆ 𝒜, 𝒮.card = k ∧ IsSunflower 𝒮
```

**`1 ≤ k` is load-bearing** so `k - 1` is the predecessor in `ℕ`
(no underflow). `r = 0` is allowed (only `∅` has card 0).

**v1 is the classical factorial bound.** Tightness of `r! (k-1)^r`
is **not** required. The sunflower conjecture and the ALWZ bound
are stretches **out of v1**, not leftover re-primes.

## Landmines

1. **This is not the sunflower conjecture.** Conjecture is open.
   Formalizing a weaker classical bound is not a novelty claim
   and not a “near-miss” at the conjecture.
2. **This is not EKR.** EKR (`erdos_ko_rado` in ProofLab;
   non-uniform `Intersecting.card_le` in Mathlib) is intersecting
   families. Sunflowers are Δ-systems.
3. **This is not Oddtown / Eventown / Fisher / BIBD.** Linear
   algebra method and designs are consumed or banned leftovers.
4. **This is not Kruskal–Katona / Sperner / LYM / Sauer–Shelah.**
   Shadows, antichains, and shattering are different theorems
   (Sperner/LYM/Sauer–Shelah already upstream).
5. **This is not Hilton–Milner.** EKR uniqueness companion —
   do not invent as an `erdos-ko-rado` leftover.
6. **Petal count `k`, uniformity `r`.** Do not swap the letters
   silently. Canonical source uses `r`-sets and `k` petals.
7. **`ℕ` subtraction.** Always assume `1 ≤ k` before `k - 1`.
8. **Do not re-prime** kruskal-katona / oddtown / cayley-trees /
   mycielski-triangle-free / havel-hakimi / menger-vertex / greedy /
   Brooks A/B / Dilworth / Eulerian / König / Dirac.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Erdős–Rado 1960)

Level A: `k = 1` (any nonempty family; take a singleton subfamily);
`r = 0` (at most one empty set, so the strict inequality cannot
fire); `r = 1` (singletons: more than `k - 1` distinct singletons
gives `k` pairwise disjoint petals); empty family (vacuous).
Not labelled Erdős–Rado.

Level B: namesake `erdos_rado_sunflower`. Standard induction on
`r`. If some point `x` lies in more than `(r-1)! (k-1)^{r-1}`
members, the traces `{s \ {x} | x ∈ s ∈ 𝒜}` yield a sunflower
by IH; add `x` back. Otherwise greedily extract `k` pairwise
disjoint members (empty-core sunflower), using that each chosen
`r`-set “kills” few remaining sets.

Partial: **Level A** small `r`/`k`, zero sorry, not labelled
Erdős–Rado. **Level B** namesake bound. Cap two levels. No
conjecture, no ALWZ, no Eventown.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/Sunflower.lean`
- Reuse Mathlib `Finset`. Do **not** re-prove EKR / Oddtown /
  Kruskal–Katona / Sauer–Shelah / Sperner / LYM.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

P. Erdős and R. Rado, *Intersection theorems for systems of sets*,
J. London Math. Soc. 35 (1960) 85–90. Textbook pin: Jukna,
*Extremal Combinatorics*, sunflower / Δ-system chapter; Alon–Spencer,
*The Probabilistic Method*, sunflower lemma. Type pin: `Finset (Finset α)`
+ `IsSunflower` as pairwise-equal intersection. EKR, Oddtown, Kruskal–Katona,
Sauer–Shelah, and the sunflower **conjecture** are **different**
statements, not this claim.
