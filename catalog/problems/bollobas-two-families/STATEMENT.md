# Bollobás two-families theorem (uniform set-pairs) — formalize-only

**id:** `bollobas-two-families`
**ticket:** OPE-1125 Scout leftover slot #2 (parent OPE-1124; post schwartz-zippel #114 + hadamard-det #115)
**expected:** known-classical (Bollobás 1965) — **no novelty claim**

## Why not classical / why formalize-only

Settled extremal set theory: if `(A_i, B_i)_{i ∈ ι}`
is a finite family of pairs of finite sets with
`A_i ∩ B_i = ∅` and `A_i ∩ B_j ≠ ∅` for `i ≠ j`,
and every `|A_i| = a`, `|B_i| = b`, then
`|ι| ≤ C(a+b, a)`. Completely classical
(Bollobás, 1965; the uniform case of the
two-families / set-pairs theorem). The weighted
form `∑ 1/C(|A_i|+|B_i|, |A_i|) ≤ 1` is the
same engine and is residual of *this* id.

Not an open problem. Not a novelty claim.

**Not** Sperner's theorem (`IsAntichain.sperner`,
`Combinatorics/SetFamily/LYM.lean` L214) —
already Mathlib; that is an antichain bound
by the middle binomial. USE nothing as a
namesake; do **not** re-prove Sperner / LYM.
**Not** Kruskal–Katona (consumed #67; colex
shadows; USE `Finset` / `Nat.choose`; do **not**
re-prove `kruskal_katona`). **Not** EKR
(consumed #39+#41). **Not** Oddtown (consumed
#68). **Not** sunflower (consumed #70).
**Not** Sauer–Shelah (already
`SetFamily/Shatter.lean` L190). **Not**
Hilton–Milner (EKR leftover). **Not** Eventown
(Oddtown leftover). **Not** Fisher / BIBD
(Oddtown leftover).

Mathlib v4.10.0 already has the **set-family
infra this theorem needs**:

- `Finset` / `Disjoint` / `Finset.card`
- `Nat.choose` (`Data/Nat/Choose/Basic.lean` L45)
- `Nat.choose_pos` / `choose_symm` (L94 / L170)
- `Equiv.Perm` (Leibniz `Perm n` already used
  at `Determinant/Basic.lean` L59 — HIT as
  permutation type)
- `Fintype.card`

There is **no** Bollobás two-families theorem,
**no** named `bollobas`, and **no** set-pairs
bound `m ≤ C(a+b, a)` anywhere under
`Mathlib/` or `Archive/` (word-regexp
`bollobas` / `Bollobas` this run → book
citations only in `Data/{Set,Finset}/Sups.lean`,
ZERO named theorem). Do **not** import
`Archive.*`.

OPE-1110 shortlist is **CONSUMED** (#114+#115).
This is a **fresh** catalog-audit id, **not** a
KK leftover continuation, **not** an EKR /
Oddtown leftover, **not** a Hadamard leftover,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite extremal set-pairs leftover
beside Cauchy–Binet (rectangular det).
`Nat.choose` + `Perm` are waiting the same way
`shadow` waited for KK. **Not a rubber-stamp
of Sperner.**

Do **not** describe an attack as discovering
Bollobás. Do **not** expand into the weighted
`ℚ` form / skew pairs / threshold versions as
extra namesakes (leftover-risk of *this* id).
Do **not** re-prove Sperner / LYM / KK / EKR /
Oddtown.

## Pinned convention (exact)

**v1 is the uniform integer form only.**
Encoding: Mathlib `Finset` + `Nat.choose`.
Count in `ℕ` (no `ℚ` required on the namesake).

Suggested pin:

```text
-- Level A (not labelled Bollobás): empty ι;
-- singleton ι; a=0 (then each A_i empty, the
-- cross condition forces |ι|≤1, and C(b,0)=1);
-- b=0 symmetric; one pair with A∩B=∅.
-- Not labelled Bollobás.

def IsSetPairFamily
    {α ι : Type*} [DecidableEq α]
    (A B : ι → Finset α) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
  (∀ i j, i ≠ j → ((A i) ∩ (B j)).Nonempty)

-- Level B namesake
theorem bollobas
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (A B : ι → Finset α)
    (h : IsSetPairFamily A B)
    (a b : ℕ)
    (hA : ∀ i, (A i).card = a)
    (hB : ∀ i, (B i).card = b) :
    Fintype.card ι ≤ Nat.choose (a + b) a
```

`Disjoint (A i) (B i)` is load-bearing (without
it a pair can sit inside itself and the
permutation argument fails). The cross
condition `i ≠ j → A_i ∩ B_j ≠ ∅` is
load-bearing (without it one can take many
identical disjoint pairs). Uniform `a, b` is
load-bearing for *this* pin (weighted `ℚ`
form is residual). `Fintype α` is load-bearing
for the permutation universe.

**Level A may land only** empty / singleton /
`a=0` / `b=0` / one-pair glue, **not** labelled
Bollobás. Reuse Mathlib `choose` / `Finset` —
**do not re-prove** Sperner / LYM / `kruskal_katona`.

**Level B** is the namesake: permutation counting
on `A_i ∪ B_i` (or on `univ`). For a permutation
of the ground set, at most one pair has every
element of `A_i` before every element of `B_i`.
Each pair is counted in `a! b!` permutations of
its own `a+b` elements, hence
`|ι| · a! · b! ≤ (a+b)!`. Do not sorry the
namesake; honest partial is allowed (comment
residual, not `sorry`). Weighted `ℚ` form is
residual.

Optional cheap corollary (not labelled Bollobás,
not required): `a=1, b=1` recovers `|ι| ≤ |α|`
for a family of disjoint edges of a bipartite
incidence graph. Do **not** re-prove König /
EKR to “get” this.

## Landmines

1. **Do not re-prove** `Nat.choose` / Sperner /
   LYM / `kruskal_katona` / `erdos_ko_rado` /
   `oddtown` / `erdos_rado_sunflower`. Already
   Mathlib or consumed ProofLab. Use `choose`.
2. **This is not** Sperner / LYM (`LYM.lean`
   L214). Antichain middle-binomial bound.
   Different theorem.
3. **This is not** Kruskal–Katona (#67). Colex
   shadows. Different theorem.
4. **This is not** EKR / Oddtown / sunflower /
   Sauer–Shelah (already Shatter.lean L190).
5. **This is not** Hilton–Milner / Eventown /
   Fisher / BIBD (leftovers of consumed ids).
6. **`A_i ∩ B_i = ∅` is load-bearing.**
7. **Cross intersections `i ≠ j` are load-bearing.**
8. **This is not** Cauchy–Binet (the prime).
   **Not** Hadamard / Schwartz–Zippel Level B.
9. **This is not** Ore / `konig_edge_chromatic` /
   AES / ostrowski-q / krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
10. **Do not re-prime** the consumed mill list
    (schwartz-zippel / hadamard-det /
    ore-hamiltonian / bipartite-chromatic-index /
    ostrowski-q / andrasfai-erdos-sos /
    noether-normalization / frobenius-real-division /
    mason-stothers / expander-mixing / zsigmondy /
    erdos-ramsey-lower / e-irrational / descartes /
    n-fold-inclusion-exclusion / wolstenholme /
    lovasz-local-lemma / korselt-carmichael / vosper /
    heron / euclid-euler / bipartite / moore /
    stirling / kst / pentagonal / sunflower / CNS /
    kk / oddtown / cayley / mycielski / friendship /
    havel / menger / greedy / Brooks / Dilworth /
    Eulerian / König / Dirac / EKR / Ramsey
    r33/r35/r333 / frobenius-coin-problem).
11. **No `Archive.*` import.**
12. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: empty family `card = 0 ≤ C(a+b, a)`.
One pair: `1 ≤ C(a+b, a)` via `choose_pos`
once `a ≤ a+b`. If `a = 0` then each `A_i = ∅`;
the cross condition says `∅ ∩ B_j ≠ ∅` for
`i ≠ j`, which is false, so `|ι| ≤ 1 = C(b, 0)`.
**Not** labelled Bollobás.

Level B: for each `i`, among the `(a+b)!`
orderings of a fixed enumeration of `A_i ∪ B_i`,
exactly `a! b!` have all of `A_i` before all of
`B_i`. Globally, a permutation of `α` (or of
the relevant union) can “witness” at most one
pair — if it witnessed `i` and `j`, the first
element of `B_i` in the order cannot sit in
`A_j` without contradicting disjointness /
cross intersection. Hence
`|ι| · a! · b! ≤ (a+b)!`. Cap two levels.
No Sperner re-proof. No KK re-proof.

## Canonical source (pin in this STATEMENT)

B. Bollobás, *On generalized graphs*, Acta Math.
Acad. Sci. Hungar. 16 (1965) 447–452. Textbook:
Bollobás, *Combinatorics*, CUP. Compact form:
Wikipedia *Bollobás theorem (combinatorics)* /
two-families theorem — **v1 pins uniform
`|A_i|=a`, `|B_i|=b`, `A_i ∩ B_i = ∅`,
`i≠j ⇒ A_i ∩ B_j ≠ ∅`, `|ι| ≤ C(a+b, a)`.**
Type pin: Mathlib `Finset` / `Nat.choose`.
Sperner / LYM / KK / EKR / Oddtown are
**different** (already-in / consumed) theorems,
not this claim.

## Out of scope

- Weighted `∑ 1/C(|A_i|+|B_i|, |A_i|) ≤ 1` as an extra namesake
- Sperner / LYM / KK / EKR / Oddtown re-proof
- Hilton–Milner / Eventown / Fisher / Sauer–Shelah
- Cauchy–Binet (the prime) / Hadamard-B / SZ-B
- Ore Level B / `konig_edge_chromatic` / AES-B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
