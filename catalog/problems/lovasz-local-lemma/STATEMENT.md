# Symmetric Lovász Local Lemma (formalize-only)

**id:** `lovasz-local-lemma`
**ticket:** OPE-804 Scout RECOMMENDED PRIME (support OPE-803; post Vosper #82 + Heron #83)
**expected:** known-classical (Erdős–Lovász 1975) — **no novelty claim**

## Why not classical / why formalize-only

Settled probabilistic-method lemma: if a finite family of
"bad" events each has probability at most `p`, and each is
mutually independent of all but at most `d` others (`d ≥ 1`),
and `4 d p ≤ 1`, then the probability that none occur is
strictly positive (equivalently: the intersection of the
complements is nonempty). Not an open problem.

Mathlib v4.10.0 already has the **counting / independence
this theorem needs**:

- `Fintype.card` / `Finset.card` / `Finset.biUnion`
- `SimpleGraph.degree` / `maxDegree` / `Adj`
- `ProbabilityTheory.condCount` (classical counting measure
  on a finite set) and `iIndepSet` / `IndepSet`
  (`Probability/Independence/Basic.lean`) — **optional glue**,
  not required. **v1 pins a Finset counting form** so Formalist
  does not have to build MeasureTheory LLL.
- Chernoff tails `measure_ge_le_exp_cgf` /
  `measure_ge_le_exp_mul_mgf` (`Probability/Moments.lean`) —
  **already upstream. Do not re-prove. Never cite Chernoff
  as this gap.**
- Markov / Chebyshev:
  `MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean`
  — **already upstream. Never cite as this gap.**

There is **no** Lovász Local Lemma, **no** `LocalLemma`,
**no** dependency-graph LLL, and **no** symmetric-LLL
theorem anywhere under `Mathlib/` or `Archive/` (word-regexp
`local lemma` / `LocalLemma` / `lovasz` this run → ZERO
theorem files; Jacobian.lean "Local lemmas" is a section
title, not LLL). ProofLab has no probabilistic-method
artifact. This is **not** a re-prime of Chernoff, **not**
Azuma / Hoeffding (also ZERO this pin — out of v1), **not**
Borel–Cantelli (already Mathlib), **not** a Ramsey / Schur
application of LLL.

OPE-788 / OPE-770 never considered this id. Fresh mill:
probabilistic combinatorics after an additive prime
(Vosper, **CONSUMED** #82) and a geometry leftover
(Heron, **CONSUMED** #83). **Not a rubber-stamp.**

Do **not** describe an attack as discovering the Local
Lemma. Do **not** expand into lopsided LLL / Shearer /
Moser–Tardos / algorithmic LLL / list-colouring
applications.

## Pinned convention (exact)

**v1 is finite uniform counting**, not a general measure
space. Bad events are `Finset`s of a finite `Ω`. Dependency
is a `SimpleGraph` on the index type. Mutual independence of
`B i` from a family `J` is the counting identity

```text
|Ω| * |B i ∩ rest| = |B i| * |rest|
where rest = {ω | ∀ j ∈ J, ω ∉ B j}
```

Suggested pin (ℕ-friendly **4d** form, not `e(d+1)p`):

```text
def IndepOfOthers {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq ι] (B : ι → Finset Ω) (G : SimpleGraph ι)
    (i : ι) : Prop :=
  ∀ J : Finset ι, (∀ j ∈ J, ¬ G.Adj i j ∧ j ≠ i) →
    let rest := Finset.univ.filter (fun ω => ∀ j ∈ J, ω ∉ B j)
    Fintype.card Ω * (B i ∩ rest).card = (B i).card * rest.card

theorem lovasz_local_lemma
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (B : ι → Finset Ω) (G : SimpleGraph ι) {d : ℕ}
    (hd : 1 ≤ d) (hdeg : ∀ i, G.degree i ≤ d)
    (hdep : ∀ i, IndepOfOthers B G i)
    (hp : ∀ i, 4 * d * (B i).card ≤ Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ B i
```

`1 ≤ d` is load-bearing (the `4d` form degenerates at
`d = 0`). Singletons / empty `ι` are allowed: empty index
⇒ any `ω` works (`Fintype.card Ω > 0` follows from
`hp` + `1 ≤ d` unless `Ω` is empty, in which case the
empty-index case should be handled as Level A glue, not a
namesake).

**Level A may land only:** (i) the union bound
`∑ |B i| < |Ω| ⇒ complements nonempty`, and (ii) the
**fully independent** case `G = ⊥` (product / counting
identity with `J = univ \ {i}`). **Not** labelled LLL.
**Level B** is the namesake `4d` dependency form.

Do **not** require `condCount` / `iIndepSet` in the
namesake. Those are optional transcriptions of the same
counting identity.

## Landmines

1. **This is not Chernoff.** Already
   `measure_ge_le_exp_cgf` / `measure_ge_le_exp_mul_mgf`.
   Never cite Chernoff as a gap (OPE-25 class).
2. **This is not Markov / Chebyshev.** Already
   `ChebyshevMarkov.lean`.
3. **This is not Borel–Cantelli.** Already
   `Probability/BorelCantelli.lean`.
4. **This is not Azuma / Hoeffding / McDiarmid.** ZERO this
   pin; concentration mill is **out of v1**. Do not expand.
5. **Do not build a general MeasureTheory LLL.** Counting
   form only. `condCount` is optional glue, not a licence
   to develop kernels.
6. **This is not a Ramsey / Schur / VdW application.**
   Those theorems are already in ProofLab. Do not re-prove
   them "via LLL".
7. **This is not Moser–Tardos / algorithmic LLL / Shearer /
   lopsided LLL.** Out of v1.
8. **Do not re-prime** vosper-cauchy-davenport / heron-formula
   / euclid-euler-perfect / bipartite-odd-cycle / moore /
   stirling / kst / pentagonal / sunflower /
   combinatorial-nullstellensatz / kruskal-katona / oddtown /
   cayley / mycielski / friendship / havel / menger / greedy /
   Brooks / Dilworth / Eulerian / König / Dirac / EKR.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Erdős–Lovász / Alon–Spencer)

Level A: union bound by `card_biUnion_le`. Fully independent
`G = ⊥`: the counting identity with `J` the other indices
gives `|∩ B_i^c| / |Ω| = ∏ (1 - |B i|/|Ω|)`; the product is
positive when each `|B i| < |Ω|`. **Not** labelled LLL.

Level B: namesake `lovasz_local_lemma`. Standard inductive
bound on the conditional counting probability
`P(B i | ∩_{j∈S} B_j^c) ≤ 2p` under `4 d p ≤ 1` (or the
equivalent product `∏ (1-2p)` lower bound on
`P(∩ B_i^c)`). Cap two levels. No lopsided, no Shearer,
no Moser–Tardos, no Chernoff re-proof.

## Canonical source (pin in this STATEMENT)

P. Erdős and L. Lovász, *Problems and results on 3-chromatic
hypergraphs and some related questions*, in Hajnal–Rado–Sós
(eds.), *Infinite and Finite Sets* vol. II, North-Holland,
1975, pp. 609–627. Textbook: Alon–Spencer, *The Probabilistic
Method*, the **symmetric** Local Lemma; v1 uses the
ℕ-friendly `4d` form rather than `e(d+1)p ≤ 1`. Type pin:
`Fintype Ω` + `ι → Finset Ω` + `SimpleGraph ι` + counting
`IndepOfOthers`. Chernoff, Markov/Chebyshev, Borel–Cantelli,
and Ramsey/Schur applications are **different** statements,
not this claim.

## Out of scope

- Chernoff / Markov / Chebyshev re-proofs (already Mathlib)
- Azuma / Hoeffding / McDiarmid
- Lopsided LLL / Shearer / Moser–Tardos
- Measure-theoretic LLL on general spaces
- Re-proving Ramsey / Schur / VdW "via LLL"
- Re-primes listed above
- Novelty / external claim
