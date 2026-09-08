# Farey sequence adjacency — formalize-only

**id:** `farey-sequence`
**ticket:** OPE-1173 Scout leftover slot #2 (parent OPE-1172; post birkhoff-von-neumann #123 + nash-williams-arboricity #124)
**expected:** known-classical (Farey 1816 / Cauchy 1816 / Hardy–Wright) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory: the *Farey
sequence of order `n`* is the ordered list of
reduced fractions `a/b` with `0 ≤ a ≤ b ≤ n`
and `gcd(a,b)=1`. Adjacent terms `a/b < c/d`
satisfy `bc − ad = 1` (Cauchy 1816 on Farey's
observation). Completely classical.

Not an open problem. Not a novelty claim.

**Not** `Nat.sum_totient` (`Data/Nat/Totient.lean`
L153: `n.divisors.sum φ = n`) — already Mathlib;
that is the **divisor-sum** identity, a
different totient theorem. USE `Nat.Coprime` /
`Nat.totient` as glue; do **not** re-prove
`sum_totient`; do **not** cite it as Farey.
The count `|F_n| = 1 + ∑_{k≤n} φ(k)` is
residual of *this* id. **Not** Pick's theorem
(no lattice-polygon area infra; previously
refused). **Not** Stern–Brocot / Calkin–Wilf
/ Ford circles as extra namesakes (leftover-risk
of *this* id). **Not** Gale–Shapley (the
OPE-1173 prime; different theorem).

Mathlib v4.10.0 already has the **coprime
fraction infra this theorem needs**:

- `Nat.Coprime` (used by `totient_eq_card_coprime`,
  Totient.lean L41; `coprime_iff_isRelPrime`
  `Data/Nat/GCD/Basic.lean` L278)
- `Nat.totient` (Totient.lean L28)
- `ℚ` reduced-fraction encoding
  (`Data/Rat/Denumerable.lean` L25:
  `{ x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 }`)
- `Rat.num` / `Rat.den`
- `Finset`

There is **no** Farey sequence theorem,
**no** named `Farey` / `fareySequence` /
`IsFarey` / `fareyAdjacent` anywhere under
`Mathlib/` or `Archive/` (word-regexp this
run → ZERO). Do **not** import `Archive.*`.

OPE-1157 shortlist is **CONSUMED** (#123+#124).
This is a **fresh** catalog-audit id, **not**
a totient leftover continuation, **not** a
BvN leftover, **not** a Nash–Williams leftover,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite coprime-fraction leftover
beside Gale–Shapley (stable matchings).
`Nat.Coprime` is waiting the same way
`Equiv.Perm` waits for Gale–Shapley. **Not a
rubber-stamp of `sum_totient`.**

Do **not** describe an attack as discovering
Farey adjacency. Do **not** expand into
Stern–Brocot mediants-as-tree / Calkin–Wilf
enumeration / Ford circles as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 is the adjacency determinant on reduced
fractions of order `n`.** Encoding: coprime
pairs, not a new `Rat` theory.

Suggested pin:

```text
-- Level A (not labelled Farey):
-- F_1 = {0/1, 1/1} adjacent with det 1;
-- mediant of 0/1 and 1/1 is 1/2;
-- F_2 = {0/1, 1/2, 1/1}.
-- Not labelled Farey.

structure FareyFrac (n : ℕ) where
  num : ℕ
  den : ℕ
  den_pos : 0 < den
  den_le : den ≤ n
  num_le : num ≤ den
  coprime : Nat.Coprime num den

def FareyLt {n : ℕ} (x y : FareyFrac n) : Prop :=
  x.num * y.den < y.num * x.den

def Adjacent {n : ℕ} (x y : FareyFrac n) : Prop :=
  FareyLt x y ∧
  ∀ z : FareyFrac n, ¬ (FareyLt x z ∧ FareyLt z y)

-- Level B namesake
theorem farey_adjacent {n : ℕ}
    (x y : FareyFrac n) (h : Adjacent x y) :
    y.num * x.den - x.num * y.den = 1
```

Finite `n` is load-bearing. Reduced
(`Nat.Coprime`) is load-bearing. The interval
is `[0,1]` (nonnegative numerators).

**Level A may land only** `F_1` two-term
adjacency / mediant of `0/1` and `1/1` /
`F_2` three-term list, **not** labelled Farey.
Reuse Mathlib `Nat.Coprime` — **do not re-prove**
`sum_totient` or `totient_eq_card_coprime`.

**Level B** is the namesake: adjacent ⇒
`bc − ad = 1` (equivalently, the first fraction
inserted between `a/b` and `c/d` is the
mediant). Do not sorry the namesake; honest
partial is allowed (comment residual, not
`sorry`). Count `|F_n|` / Stern–Brocot are
residual.

## Landmines

1. **Do not re-prove** `Nat.Coprime` /
   `Nat.totient` / `sum_totient` /
   `totient_eq_card_coprime` / `Rat.num`.
   Already Mathlib. Use them.
2. **This is not** `n.divisors.sum φ = n`
   (already-in). Different totient theorem.
   Do not cite as Farey.
3. **This is not** Pick's theorem (no area
   infra). Do not revive.
4. **This is not** Stern–Brocot / Calkin–Wilf
   / Ford circles. Residual of this id.
5. **This is not** Gale–Shapley (OPE-1173
   prime). Different theorem.
6. **This is not** Gale–Ryser / BvN (#123) /
   Nash–Williams (#124) Level B.
7. **This is not** Minkowski convex body
   (already-in) / Farey dissection of the
   modular surface as extra namesakes.
8. **This is not** Singleton (#120) /
   hook-length (#121) / `cauchy_binet` /
   `bollobas` / Ore / `konig_edge_chromatic` /
   AES / ostrowski / krenn-gu / hou-zeng-pfc /
   sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (nash-williams-arboricity /
   birkhoff-von-neumann / hook-length /
   singleton-bound / cauchy-binet /
   bollobas-two-families / schwartz-zippel /
   hadamard-det / ore-hamiltonian /
   bipartite-chromatic-index / ostrowski-q /
   andrasfai-erdos-sos / noether-normalization /
   frobenius-real-division / mason-stothers /
   expander-mixing / zsigmondy /
   erdos-ramsey-lower / e-irrational / descartes /
   n-fold-inclusion-exclusion / wolstenholme /
   lovasz-local-lemma / korselt-carmichael / vosper /
   heron / euclid-euler / bipartite / moore /
   stirling / kst / pentagonal / sunflower / CNS /
   kk / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth /
   Eulerian / König / Dirac / EKR / Ramsey
   r33/r35/r333 / frobenius-coin-problem).
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: order `1` is `{0/1, 1/1}`;
`1·1 − 0·1 = 1`. The mediant is
`(0+1)/(1+1) = 1/2`, strictly between, and
is the unique new term of order `2`. **Not**
labelled Farey.

Level B: if `a/b < c/d` are adjacent in `F_n`
and `bc − ad = k > 1`, the mediant
`(a+c)/(b+d)` has denominator `≤ n` once `n`
is large enough relative to a neighbour, or
induct by inserting mediants; equivalently,
unimodular identity for adjacent SL(2,ℤ)
pairs. Cap two levels. No Stern–Brocot tree.
No totient-sum re-proof.

## Canonical source (pin in this STATEMENT)

J. Farey, *On a curious property of vulgar
fractions*, Phil. Mag. 47 (1816) 385–386.
A.-L. Cauchy, *Démonstration d'un théorème
sur les nombres*, Bulletin de la Société
Philomathique (1816) 133–135. Textbook:
Hardy–Wright, *An Introduction to the Theory
of Numbers*, Ch. III. Compact form: Wikipedia
*Farey sequence*. Type pin: `Nat.Coprime` /
coprime pairs. `sum_totient` is a **different**
already-in theorem.

## Out of scope

- `|F_n| = 1 + ∑_{k≤n} φ(k)` as extra namesake
- Stern–Brocot tree / Calkin–Wilf / Ford circles
- Pick's theorem / lattice-polygon area
- Modular surface / Dedekind tessellation
- Gale–Shapley (the prime of this mill)
- Gale–Ryser / BvN Level B / Nash–Williams Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
