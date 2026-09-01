# Erdős probabilistic Ramsey lower bound (formalize-only)

**id:** `erdos-ramsey-lower`
**ticket:** OPE-858 Formalist Level A+B (Scout OPE-853 prime; Director OPE-857; post Descartes #91 + e-irrational #92)
**expected:** known-classical (Erdős 1947 first-moment / union bound) — **no novelty claim**

## Why not classical / why formalize-only

Settled Ramsey-theory counting: if
`n.choose k * 2 < 2^(k.choose 2)`, then there exists a
red/blue colouring of `K_n` with no monochromatic `K_k`
(so `R(k,k) > n`). The textbook corollary is
`R(k,k) > 2^(k/2)` for `k ≥ 3`.

Not an open problem. Not a novelty claim. **Not** the
specific numbers `R(3,3)=6` / `R(3,4)=9` / `R(4,4)=18` /
`R(3,5)=14` / `R(3,3,3)=17` already in ProofLab. **Not**
`R(4,6)=41` (no hand proof). **Not** infinite Ramsey
(Wiedijk 100.yaml #31 has only an external Bhavik Mehta
link — **do not import**, **do not prove** the infinite
statement). **Not** the finite *existence* wrap
`∀ k l, ∃ n, RamseyUpper k l n` — that is a Cassini-class
induction on already-landed `ramseyUpper_add` +
`ramsey_two_right`, and is **not** this bet.

Mathlib v4.10.0 already has the **graph encoding this
theorem needs**:

- `SimpleGraph` / `IsNClique` / `cliqueFinset`
  (`Combinatorics/SimpleGraph/{Basic,Clique}.lean`)
- `Fintype (SimpleGraph V)` for finite `V`
  (`SimpleGraph.Basic` — enumerate graphs)
- `Nat.choose` / `Nat.pow` / `Finset.card`
- Hindman / Hales–Jewett /
  `exists_mono_homothetic_copy` (homothetic VdW) —
  **already upstream. Different theorems. Never cite as
  this gap.**
- Turán `isTuranMaximal_iff_nonempty_iso_turanGraph` —
  **negative control. Already upstream.**

There is **no** graph-Ramsey number, **no** `RamseyUpper`,
**no** diagonal lower bound `R(k,k) > 2^(k/2)`, and **no**
named Erdős first-moment Ramsey theorem anywhere under
`Mathlib/` or `Archive/` (word-regexp `ramsey` this run in
`Mathlib/Combinatorics` → only Hindman / Hales–Jewett
comments and author names; `SimpleGraph/` → ZERO Ramsey).
Wiedijk 100.yaml #31 lists only an **external** infinite
Ramsey file — **no Mathlib decl**. Do **not** treat that
external file as upstream. Do **not** import `Archive.*`.

ProofLab already has `RamseyUpper` / `HasClique` /
`ramseyUpper_add` / `ramsey_two_right` and the small
numbers. Those are **infra to use**, **not** a re-prime of
`ramsey-r33` / `ramsey-r35` / `ramsey-multicolor-r333`.
This id is a **new proof layer**: counting / first moment,
not a new small Ramsey number.

OPE-838 considered-not-slotted listed `ramsey-r46` (no hand
upper / no certified witness) and did **not** slot a
diagonal counting bound. Descartes #91 + e-irrational #92
are now **CONSUMED**. This is a **fresh** combinatorics
prime after an algebra+analysis wave, **not** a Descartes
leftover, **not** an e-irrational leftover, **not** a
third slot, **not** LLL-B (union bound is the *engine*,
not the Lovász Local Lemma).

Mill NOW: probabilistic combinatorics counting after
polynomial algebra (Descartes, **CONSUMED** #91) and
analysis (e-irrational, **CONSUMED** #92). ProofLab
`RamseyUpper` is waiting, the same way `Polynomial.coeff`
waited for Descartes and `exp_eq_tsum_div` waited for e.
**Not a rubber-stamp of R(3,3)=6.**

Do **not** describe an attack as discovering Ramsey
numbers. Do **not** expand into `R(4,6)`, infinite Ramsey,
canonical Ramsey, or LLL-from-this-bound.

## Pinned convention (exact)

**v1 is the union-bound / first-moment criterion**, plus
the textbook `2^(k/2)` corollary. Encoding is ProofLab
`RamseyUpper` (red graph `G : SimpleGraph (Fin n)`, blue
`Gᶜ`).

Suggested pin:

```text
-- Level A (not labelled Erdős): union-bound criterion
theorem ramsey_union_bound {k n : ℕ} (hk : 2 ≤ k)
    (h : n.choose k * 2 < 2 ^ (k.choose 2)) :
    ¬ RamseyUpper k k n

-- Level B namesake
theorem erdos_ramsey_lower (k : ℕ) (hk : 3 ≤ k) :
    ¬ RamseyUpper k k (2 ^ (k / 2))
```

`RamseyUpper` is ProofLab (`ProofLab/Ramsey.lean`).
`n.choose k` is Mathlib `Nat.choose`. `2 ^ (k / 2)` is
`Nat` power of `Nat` division (so `2 ^ ⌊k/2⌋`). That is
the classical elementary bound, **not** the
`(√2)^k / e` sharpening.

**Level A may land only the counting criterion**, not
labelled `erdos_ramsey_lower`. Engine: if every colouring
had a mono `K_k`, then counting pairs
`(G, s)` with `s.card = k` and `s` a clique in `G` or
`Gᶜ` would force
`2^(n.choose 2) ≤ n.choose k * 2 * 2^(n.choose 2 - k.choose 2)`,
contradicting `h`. `Fintype (SimpleGraph (Fin n))` is
already Mathlib — **use it**. A `Fintype.card
(SimpleGraph (Fin n)) = 2^(n.choose 2)` glue lemma is
in-scope (not labelled Erdős).

**Level B** is the namesake: check the binomial criterion
at `n = 2^(k/2)` for `k ≥ 3` (standard `n^k / k!`
estimate, or `choose_le_pow`).

Empty/small `n < k` is allowed (`n.choose k = 0` makes
the criterion fire and there is no `k`-set).

## Landmines

1. **Do not re-prove** `IsNClique` / `cliqueFinset` /
   `Fintype (SimpleGraph V)` / `Nat.choose` /
   Hindman / Hales–Jewett / homothetic VdW / Turán.
   Already Mathlib. Use them.
2. **This is not** `ramsey-r33` / `R(3,4)` / `R(4,4)` /
   `ramsey-r35` / `ramsey-multicolor-r333`. Those numbers
   **CONSUMED**. Do **not** re-prime. Reuse
   `RamseyUpper` as encoding only.
3. **This is not** `R(4,6)=41`. Still no hand proof.
   Reject.
4. **This is not** infinite Ramsey / Wiedijk #31 external.
   Out of v1. No `Archive.*`.
5. **This is not** finite Ramsey *existence*
   `∀ k l, ∃ n, RamseyUpper k l n`. Cassini-class wrap of
   already-landed `ramseyUpper_add` + `ramsey_two_right`.
   Not this bet.
6. **This is not LLL / Chernoff / Markov / Azuma.**
   Union bound is the engine, not the Local Lemma
   (consumed #85). Do **not** invent LLL-B.
7. **This is not** Descartes (consumed #91 honest Level A)
   / e-irrational (consumed #92 namesake) /
   n-fold PIE (#88) / Wolstenholme (#89 honest partial).
8. **Do not re-prime** n-fold-inclusion-exclusion /
   wolstenholme-theorem / lovasz-local-lemma /
   korselt-carmichael / vosper / heron / euclid-euler /
   bipartite / moore / stirling / kst / pentagonal /
   sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski /
   friendship / havel / menger / greedy / Brooks /
   Dilworth / Eulerian / König / Dirac / EKR /
   descartes-rule-of-signs / e-irrational.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Erdős 1947)

Level A: there are `2^(n.choose 2)` red/blue colourings of
`K_n`. For a fixed `k`-set `s`, the number of colourings
in which `s` is monochromatic is
`2 * 2^(n.choose 2 - k.choose 2)`. If every colouring had
at least one mono `K_k`, then
`2^(n.choose 2) ≤ n.choose k * 2 * 2^(n.choose 2 - k.choose 2)`,
i.e. `2^(k.choose 2) ≤ n.choose k * 2`. The hypothesis
is the negation. **Not** labelled Erdős.

Level B: `n = 2^(k/2)` satisfies the criterion for
`k ≥ 3` via `n.choose k ≤ n^k / k!` (or weaker
`n.choose k ≤ n^k`). Cap two levels. No random-graph
sharpening, no Lovász Local Lemma, no `R(3,k)` off-diagonal
Spencer bound.

## Canonical source (pin in this STATEMENT)

Erdős, *Some remarks on the theory of graphs*, Bull. AMS
53 (1947). Compact form: Alon–Spencer, *The Probabilistic
Method*, the first-moment / counting proof that
`R(k,k) > 2^(k/2)`. Wikipedia *Ramsey's theorem* —
lower bounds via counting. Type pin: ProofLab
`RamseyUpper k k n` as `¬` under the binomial hypothesis.
Wiedijk #31 infinite Ramsey external Lean is **not** this
claim and **not** Mathlib. Small Ramsey numbers in
`ProofLab/Ramsey.lean` are **different** statements.

## Out of scope

- `R(3,3)=6` / `R(3,4)=9` / `R(4,4)=18` / `R(3,5)=14` /
  `R(3,3,3)=17` re-primes
- `R(4,6)` / other specific numbers without hand proofs
- Infinite Ramsey / canonical Ramsey / Graham–Rothschild
- Finite Ramsey existence wrap of `ramseyUpper_add`
- LLL / Chernoff / Spencer off-diagonal
- `(√2)^k * k / e` sharpening
- Re-primes listed above
- Novelty / external claim
