# Ostrowski’s theorem for ℚ (formalize-only)

**id:** `ostrowski-q`
**ticket:** OPE-1078 Scout leftover slot #2 (parent OPE-1077; post noether-normalization #106 + frobenius-real-division #105)
**expected:** known-classical (Ostrowski 1916, absolute values on ℚ) — **no novelty claim**

## Why not classical / why formalize-only

Settled elementary number theory / valuations: every
nontrivial absolute value on `ℚ` is equivalent either
to the usual archimedean absolute value `|·|∞` or to
a p-adic absolute value `|·|_p` for a unique prime
`p`. Completely classical (Ostrowski 1916).

Not an open problem. Not a novelty claim.

**Not** the non-archimedean *half already in Mathlib*
(`mulRingNorm_equiv_padic_of_bounded` in
`NumberTheory/Ostrowski.lean` L187 — bounded nontrivial
`MulRingNorm` on `ℚ` is equivalent to a padic norm).
That is **infra**, the easy direction once
`∀ n, f n ≤ 1`; **USE, do not re-prove; never cite
as this gap.** **Not** Ostrowski for number fields
(the file header TODO; **out of v1**). **Not**
Gelfand–Mazur (already Mathlib; complex Banach;
**different** theorem). **Not** π-irrational /
Niven cosine (analysis-API / intervalIntegral sink;
**not** this valuation classification). **Not**
e-irrational (#92). **Not** padic Hensel (already
Mathlib `hensels_lemma`). **Not**
frobenius-real-division Level B. **Not**
noether-normalization Level B.

Mathlib v4.10.0 already has the **valuation infra this
theorem needs**:

- `MulRingNorm` / `MulRingNorm.equiv`
  (`Analysis/Normed/Ring/Seminorm.lean`)
- `mulRingNorm_padic` / `padicNorm`
  (`NumberTheory/Ostrowski.lean`,
  `NumberTheory/Padics/PadicNorm.lean`)
- `mulRingNorm_equiv_padic_of_bounded` — **already
  upstream. The bounded/non-archimedean half.
  Different from the namesake. USE, never cite as
  this gap.**
- Real `log` / `rpow` (already used in that file)

There is **no** full Ostrowski classification
(archimedean ∨ padic), **no** unbounded/archimedean
engine `f n = n^α`, and **no** `mulRingNorm_real`
construction packaged as the namesake anywhere under
`Mathlib/` or `Archive/` (the Ostrowski.lean header
still says the theorem is TODO; the file **ends**
after the `Non_archimedean` section). Do **not**
import `Archive.*`.

OPE-1062 shortlist is **CONSUMED** (#105+#106).
This is a **fresh** leftover, **not** a Frobenius
leftover, **not** a Noether leftover, **not** a
prize leftover, **not** a π-irrational leftover,
**not** a third slot.

Mill NOW: elementary-valuation leftover after a
finite extremal-graph prime (`andrasfai-erdos-sos`)
— `MulRingNorm` + the bounded padic theorem are
waiting the same way `IsIntegral.finite` waited for
Noether. **Not a rubber-stamp of the already-in
non-archimedean half.** **Not π-irrational**
(no `intervalIntegral`).

Do **not** describe an attack as discovering
Ostrowski. Do **not** expand into number fields /
Ostrowski for `k(t)` / product formula as extra
namesakes (leftover-risk of *this* id). Do **not**
re-prove Hensel / Gelfand–Mazur / π-irrational.

## Pinned convention (exact)

**v1 is Ostrowski for `MulRingNorm ℚ` only.**
The already-upstream bounded theorem is the
non-archimedean half; the gap is the unbounded
(archimedean) half plus the disjunction.

Suggested pin:

```text
-- Level A (not labelled Ostrowski): if f is
-- unbounded on ℕ, then f is equivalent to the
-- usual absolute value on ℚ. Construct
-- mulRingNorm_real : MulRingNorm ℚ from |·|.
-- Not labelled Ostrowski.

-- Level B namesake
theorem ostrowski
    (f : MulRingNorm ℚ) (hf : f ≠ 1) :
    MulRingNorm.equiv f mulRingNorm_real ∨
    ∃ p, ∃ (_ : Fact p.Prime),
      MulRingNorm.equiv f (mulRingNorm_padic p)
```

`f ≠ 1` (nontrivial) is load-bearing. The split
`∀ n, f n ≤ 1` vs unbounded is load-bearing.
`MulRingNorm.equiv` (some positive real power) is
the equivalence pin, already in Mathlib.

**Level A may land only** the unbounded engine
(`∃ α > 0, ∀ n, f n = n^α` on `ℕ`, then package
as `equiv mulRingNorm_real`), **not** labelled
Ostrowski. Use
`mulRingNorm_equiv_padic_of_bounded` — **do not
re-prove the bounded half**.

**Level B** is the namesake disjunction. Do not
sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Number fields
out of v1.

## Landmines

1. **Do not re-prove** `mulRingNorm_equiv_padic_of_bounded`
   / `mulRingNorm_padic` / `padicNorm` /
   `MulRingNorm.equiv` / Hensel / Gelfand–Mazur.
   Already Mathlib. Use them.
2. **This is not** the bounded half already in
   Ostrowski.lean. That is infra. Citing it as
   the gap is the OPE-25 failure mode.
3. **This is not** Ostrowski for number fields
   (file-header TODO). Out of v1.
4. **This is not** π-irrational / Niven cosine /
   e-transcendental. No `intervalIntegral`.
5. **This is not** e-irrational (#92) / Descartes /
   Mason / Noether / Frobenius Level B.
6. **This is not** `andrasfai-erdos-sos` (the prime).
   Do **not** assign first unless Director swaps.
7. **This is not** krenn-gu / hou-zeng-pfc / sun-135.
   Do not revive.
8. **Do not re-prime** the consumed mill list
   (frobenius-real-division / noether-normalization /
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
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, ℚ)

Level A: if `f` is unbounded on `ℕ`, then
`f(n) ≥ 1` for all `n ≥ 1` and `f(2) = 2^α` for
some `α > 0`; sandwich `f(n)` between powers of 2
to get `f(n) = n^α`. Package as
`MulRingNorm.equiv f mulRingNorm_real`. **Not**
labelled Ostrowski.

Level B: if `f` is bounded, apply already-upstream
`mulRingNorm_equiv_padic_of_bounded`. Cap two
levels. No number fields. No Hensel re-proof.

## Canonical source (pin in this STATEMENT)

A. Ostrowski, *Über einige Lösungen der
Funktionalgleichung φ(x)·φ(y)=φ(xy)*, Acta Math. 41
(1916) 271–284. Textbook: Cassels, *Local Fields*;
K. Conrad, *Ostrowski's theorem for ℚ*. Compact
form: Wikipedia *Ostrowski's theorem* —
**v1 pins nontrivial `MulRingNorm ℚ`, equivalent
to usual abs or some `mulRingNorm_padic p`.**
Type pin: Mathlib `MulRingNorm` / `equiv` /
`mulRingNorm_padic`.
`mulRingNorm_equiv_padic_of_bounded` is infra, not
this claim. Number-field Ostrowski is out of v1.

## Out of scope

- Ostrowski for number fields / function fields
- Product formula / adeles
- Hensel re-proof (already Mathlib)
- π-irrational / Niven / e-transcendental
- Frobenius / Noether Level B revival
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
