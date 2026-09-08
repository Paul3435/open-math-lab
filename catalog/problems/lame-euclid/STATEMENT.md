# Lamé's theorem on the Euclidean algorithm — formalize-only

**id:** `lame-euclid`
**ticket:** OPE-1189 Scout leftover slot #2 (parent OPE-1188; post gale-shapley #126 + farey-sequence #127)
**expected:** known-classical (Lamé 1844) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory: the number
of division steps in the Euclidean algorithm
on `a ≥ b > 0` is maximised by consecutive
Fibonacci numbers, and is at most a linear
function of the number of digits of `b`
(Gabriel Lamé 1844). Completely classical.

Not an open problem. Not a novelty claim.

**Not** `Nat.fib_gcd`
(`Data/Nat/Fib/Basic.lean` L235:
`fib (gcd m n) = gcd (fib m) (fib n)`) —
already Mathlib; that is the **strong
divisibility** identity for Fibonacci, a
different theorem. USE `Nat.fib` /
`Nat.gcd` / `gcd_rec` / `Nat.gcd.induction`
as glue; do **not** re-prove `fib_gcd`; do
**not** cite it as Lamé. **Not** Euclid–Euler
even perfect numbers (consumed #80) — a
different Euclid. **Not** Zeckendorf
(`Data/Nat/Fib/Zeckendorf.lean`, already-in).
**Not** Binet / `GoldenRatio.lean` (already-in).
Cassini `F_{n-1} F_{n+1} − F_n² = (−1)ⁿ` is
ZERO this pin and is residual of *this* id
— do **not** prove it as an extra namesake.

Mathlib v4.10.0 already has the **Fibonacci /
gcd infra this theorem needs**:

- `Nat.fib` (`Data/Nat/Fib/Basic.lean` L65;
  `fib_zero` L69 / `fib_one` L73 / `fib_two` L77)
- `Nat.gcd` / `gcd_rec` / `Nat.gcd.induction`
  (used at Fib/Basic.lean L236–L239;
  GCD/Basic.lean L34)
- `Nat.mod` / `%`
- `Nat.Coprime` (GCD/Basic.lean
  `coprime_iff_isRelPrime` L278) — optional

There is **no** Lamé theorem on Euclid
complexity, **no** named `lame_theorem` /
`Lame` / `euclidSteps` / `euclid_steps` /
`gcd_steps` anywhere under `Mathlib/` or
`Archive/` or `ProofLab/` (word-regexp this
run → ZERO). Do **not** import `Archive.*`.

OPE-1173 shortlist is **CONSUMED** (#126+#127).
This is a **fresh** catalog-audit id, **not**
a Farey leftover continuation, **not** a
Gale–Shapley leftover, **not** an
Euclid–Euler leftover, **not** a Fibonacci
`fib_gcd` re-proof, **not** a prize leftover,
**not** a Formalist Level B revival, **not**
a third slot.

Mill NOW: finite Euclid-step leftover beside
Schur product (PSD Hadamard). `Nat.fib` is
waiting the same way `Nat.Coprime` waited
for Farey. **Not a rubber-stamp of
`fib_gcd`.**

Do **not** describe an attack as discovering
Lamé. Do **not** expand into Cassini /
Catalan-Fibonacci / Zeckendorf uniqueness /
digit-count `5 * log10` as extra namesakes
(leftover-risk of *this* id).

## Pinned convention (exact)

**v1 is the Fibonacci worst-case bound on
the number of Euclidean division steps.**
Encoding: a well-founded step counter on
`Nat.mod`, not a new gcd theory.

Mathlib Fibonacci indexing (load-bearing):
`fib 0 = 0`, `fib 1 = 1`, `fib 2 = 1`,
`fib 3 = 2`, `fib 4 = 3`, `fib 5 = 5`,
`fib 6 = 8`.

Suggested pin:

```text
-- Level A (not labelled Lamé):
-- euclidSteps a 0 = 0;
-- 0 < a → euclidSteps a a = 1;
-- euclidSteps 2 1 = 1;
-- consecutive Fibonacci pairs for small n
-- (e.g. euclidSteps (fib 6) (fib 5) = 4,
--  fib 6 = 8, fib 5 = 5).
-- Not labelled Lamé.

def euclidSteps : ℕ → ℕ → ℕ
  | a, b => if b = 0 then 0 else euclidSteps b (a % b) + 1
-- well-founded on b (termination via mod_lt)

theorem euclidSteps_zero (a : ℕ) : euclidSteps a 0 = 0
theorem euclidSteps_self {a : ℕ} (ha : 0 < a) :
    euclidSteps a a = 1
theorem euclidSteps_two_one : euclidSteps 2 1 = 1
theorem euclidSteps_fib_six_five :
    euclidSteps (Nat.fib 6) (Nat.fib 5) = 4

-- Level B namesake
theorem lame {a b n : ℕ} (hba : b ≤ a) (hb : 0 < b)
    (h : euclidSteps a b = n) :
    Nat.fib (n + 2) ≤ a ∧ Nat.fib (n + 1) ≤ b
```

**Step-count pin (definition risk):**
`euclidSteps a 0 = 0`. Each `%` that sees
`b > 0` counts `+ 1`. The terminal `b = 0`
is **not** an extra step. With this pin,
`gcd(8,5)` takes 4 steps and saturates
`fib (4+2) = fib 6 = 8`. Do **not** flip
the off-by-one without restating the
Fibonacci index.

Finite `ℕ` is load-bearing. `b ≤ a` on the
namesake is a convenience (swap if needed
via `gcd_comm`); the step counter itself
does not require `b ≤ a`.

**Level A may land only** zero / self /
`2,1` / one or two explicit Fibonacci
pairs, **not** labelled Lamé. Reuse Mathlib
`Nat.fib` / `Nat.gcd` / `gcd_rec` —
**do not re-prove** Fibonacci, gcd
correctness, or `fib_gcd`.

**Level B** is the namesake: if the algorithm
takes `n` steps then `a ≥ F_{n+2}` and
`b ≥ F_{n+1}`. Do not sorry the namesake;
honest partial is allowed (comment residual,
not `sorry`). Digit-count form
(`n ≤ 5 * #decimal digits of b`) / Cassini
are residual.

## Landmines

1. **Do not re-prove** `Nat.fib` / `Nat.gcd` /
   `gcd_rec` / `Nat.gcd.induction` /
   `fib_gcd`. Already Mathlib. Use them.
2. **This is not** `fib_gcd` (already-in
   strong divisibility). Different Fibonacci
   theorem. Do not cite as Lamé.
3. **This is not** Euclid–Euler even perfect
   numbers (consumed). Different Euclid. Do
   not revive.
4. **This is not** Zeckendorf (already-in).
   Not Binet / GoldenRatio (already-in).
5. **This is not** Cassini / Catalan identity
   for Fibonacci. Residual of *this* id.
6. **This is not** Farey (#127) /
   `farey_adjacent` / Stern–Brocot /
   `sum_totient`. Not Gale–Shapley (#126).
7. **This is not** Schur product (the
   OPE-1189 prime). Different theorem.
8. **This is not** krenn-gu / hou-zeng-pfc /
   sun-135 / AES / ostrowski / wolstenholme
   Bernoulli residual.
9. **Do not re-prime** the consumed mill list
   (farey-sequence / gale-shapley /
   nash-williams-arboricity /
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

Level A: `b = 0` is 0 steps. `a = a > 0`
gives one step `a % a = 0`. `2,1` is one
step. The pair `(F_6, F_5) = (8,5)` expands
to four mods and hits 0. **Not** labelled
Lamé.

Level B: if a run is strictly decreasing in
the second argument and takes `n` steps,
the smallest possible inputs are consecutive
Fibonacci (induct backwards: a worst-case
predecessor of `(F_{k+1}, F_k)` is
`(F_{k+2}, F_{k+1})`). Cap two levels. No
`fib_gcd` re-proof. No Euclid–Euler. No
Cassini as extra namesake. No digit-count
form unless it falls out of `fib n ≥ φ^{n}/√5`
(Binet already-in — do not re-prove).

## Canonical source (pin in this STATEMENT)

G. Lamé, *Note sur la limite du nombre des
divisions dans la recherche du plus grand
commun diviseur*, Comptes rendus 19 (1844)
867–870. Textbook: Knuth TAOCP vol. 2,
Euclidean algorithm analysis; Hardy–Wright
on Fibonacci worst case. Compact form:
Wikipedia *Euclidean algorithm* / *Lamé's
theorem*. Type pin: `Nat.fib` / `euclidSteps`
via `%`. `fib_gcd` is a **different**
already-in theorem. Euclid–Euler is a
**different** consumed theorem.

## Out of scope

- Digit-count form `n ≤ 5 * (#digits of b)`
- Cassini / Catalan-Fibonacci identities
- Subtractive Euclidean algorithm (worse
  bound)
- Binary GCD / Stein
- Complexity of `xgcd` coefficients
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
