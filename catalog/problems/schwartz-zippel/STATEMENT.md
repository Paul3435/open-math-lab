# Schwartz–Zippel lemma (finite-box zeros of a polynomial) — formalize-only

**id:** `schwartz-zippel`
**ticket:** OPE-1110 Scout RECOMMENDED PRIME (parent OPE-1109; post ore-hamiltonian #111 + bipartite-chromatic-index #112)
**expected:** known-classical (DeMillo–Lipton 1978 / Zippel 1979 / Schwartz 1980) — **no novelty claim**

## Why not classical / why formalize-only

Settled combinatorial algebra: a nonzero polynomial
`f ∈ F[x₁,…,xₙ]` of `totalDegree ≤ d` over a field `F`
vanishes on at most `d |S|^{n-1}` points of a finite
box `Sⁿ ⊆ Fⁿ`. Completely classical (DeMillo–Lipton
1978; Zippel 1979; Schwartz, J. ACM 27 (1980)).

Not an open problem. Not a novelty claim.

**Not** combinatorial Nullstellensatz
(`combinatorial-nullstellensatz`, PR **#71**,
`combinatorial_nullstellensatz` already in ProofLab —
a **different** named theorem, leading-monomial
nonvanishing on a box; USE `MvPolynomial` encoding;
do **not** re-prove `combinatorial_nullstellensatz`;
do **not** revive CNS as a leftover). **Not**
Chevalley–Warning (already Mathlib
`FieldTheory/ChevalleyWarning.lean`
`char_dvd_card_solutions` — a **different** theorem:
characteristic divides the number of zeros when
`totalDegree < #vars`). **Not** Alon–Füredi (box
nonvanishing quantitative bound; out of v1). **Not**
Schwartz–Zippel over non-domains. **Not** polynomial
identity testing as an algorithm.

Mathlib v4.10.0 already has the **polynomial infra
this theorem needs**:

- `MvPolynomial.eval` (`Basic.lean` L1050)
- `MvPolynomial.totalDegree` (`Degrees.lean` L310)
- `MvPolynomial.degreeOf` (`Degrees.lean` L209)
- `MvPolynomial.finSuccEquiv` (`Equiv.lean` L303) —
  peel the last variable as a `Polynomial` over
  `MvPolynomial (Fin n)`
- `Polynomial.card_roots'` (`Roots.lean` L70) —
  `Multiset.card p.roots ≤ natDegree p`

There is **no** Schwartz–Zippel lemma, **no** Zippel
lemma, and **no** named `totalDegree * |S|^{n-1}`
zero-set bound anywhere under `Mathlib/` or `Archive/`
(word-regexp `zippel` / `SchwartzZippel` /
`schwartz_zippel` this run → ZERO). Do **not** import
`Archive.*`.

OPE-1095 shortlist is **CONSUMED** (#111+#112).
This is a **fresh** catalog-audit id, **not** a CNS
leftover continuation, **not** an Ore leftover,
**not** a König line-colouring leftover, **not** a
prize leftover, **not** a Formalist Level B revival,
**not** a third slot.

Mill NOW: finite polynomial-zero bound after Ore
(Hamiltonian sufficient condition) + König
line-colouring (edge-colour). `totalDegree` is
waiting the same way `IsHamiltonian` waited for Ore.
**Not a rubber-stamp of CNS.**

Do **not** describe an attack as discovering
Schwartz–Zippel. Do **not** expand into Alon–Füredi /
PIT / non-domain versions as extra namesakes
(leftover-risk of *this* id). Do **not** re-prove
CNS / Chevalley–Warning / Ore Level B /
`konig_edge_chromatic`.

## Pinned convention (exact)

**v1 is the finite-box counting form over a field, `n ≥ 1` only.**
Encoding: Mathlib `MvPolynomial.eval` + `totalDegree` + `Finset`.
Count in `ℕ` (no `ℚ`, no probabilities required).

Suggested pin:

```text
-- Level A (not labelled Schwartz–Zippel): n=1;
-- identify MvPolynomial (Fin 1) with Polynomial;
-- Finset of roots in S has card ≤ natDegree via
-- Polynomial.card_roots'. Nonzero constants never
-- vanish. Not labelled Schwartz–Zippel.

-- Level B namesake
theorem schwartz_zippel
    {F : Type*} [Field F] [DecidableEq F]
    {n : ℕ} (hn : 1 ≤ n)
    (f : MvPolynomial (Fin n) F) (hf : f ≠ 0)
    (S : Finset F) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun x => (∀ i, x i ∈ S) ∧ eval x f = 0)).card
      ≤ f.totalDegree * S.card ^ (n - 1)
```

`1 ≤ n` is load-bearing (`n = 0` is constants;
`Nat` power `S.card ^ (n-1)` is the wrong shape).
`f ≠ 0` is load-bearing (the zero polynomial vanishes
everywhere). `totalDegree` is load-bearing (CNS used
**per-variable** `degreeOf` — do **not** swap).
`Field F` is load-bearing (`card_roots'` needs an
integral domain). `DecidableEq F` is load-bearing
for `Finset` membership.

**Level A may land only** `n=1` / constants /
`card_roots'` glue, **not** labelled Schwartz–Zippel.
Reuse Mathlib `eval` / `totalDegree` / `finSuccEquiv`
and the *idea* of peeling a variable from consumed
CNS — **do not re-prove** `combinatorial_nullstellensatz`.

**Level B** is the namesake: induction on `n` via
`finSuccEquiv`. Write `f` as a polynomial in the last
variable whose coefficients live in
`MvPolynomial (Fin (n-1)) F`. For each tail in `S^{n-1}`
either the leading coefficient vanishes (IH) or the
univariate in the last variable has at most `deg`
roots in `S`. Do not sorry the namesake; honest
partial is allowed (comment residual, not `sorry`).
Alon–Füredi is residual.

Optional cheap corollary (not labelled Schwartz–Zippel,
not required): if `S` is a finite field and
`f.totalDegree < |S|` then `f` is not identically
zero as a function `Sⁿ → S`. Do **not** re-prove
Chevalley–Warning to “get” this.

## Landmines

1. **Do not re-prove** `MvPolynomial.eval` /
   `totalDegree` / `degreeOf` / `finSuccEquiv` /
   `Polynomial.card_roots'` /
   `combinatorial_nullstellensatz` /
   `char_dvd_card_solutions`. Already Mathlib or
   consumed ProofLab. Use them.
2. **This is not** combinatorial Nullstellensatz
   (#71). Different theorem. Do not revive CNS
   Level C / SZ as a CNS leftover.
3. **This is not** Chevalley–Warning (already
   Mathlib). Different theorem (`char ∣ |zeros|`
   when `deg < n`).
4. **`f ≠ 0` is load-bearing.** Zero polynomial
   vanishes on the whole box.
5. **`n ≥ 1` is load-bearing.** Constants / `Nat`
   power landmine at `n=0`.
6. **`totalDegree`, not `degreeOf`.** CNS used
   per-variable degree. Swapping the pin is a
   different (false, or Alon–Füredi-shaped) theorem.
7. **This is not** Alon–Füredi / PIT / Schwartz–Zippel
   over rings that are not domains.
8. **This is not** Ore (#111) / König line-colouring
   (#112) / AES / ostrowski-q Level B /
   `hadamard-det` (the leftover).
9. **This is not** ostrowski-q Level B /
   andrasfai-erdos-sos Level B /
   frobenius-real-division Level B /
   noether-normalization Level B / krenn-gu /
   hou-zeng-pfc / sun-135. Do not revive.
10. **Do not re-prime** the consumed mill list
    (ore-hamiltonian / bipartite-chromatic-index /
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

Level A: `n=1` is a univariate polynomial. The
`Finset` of roots in `S` injects into `p.roots`
(forgetting multiplicity), and
`card_roots'` gives `≤ natDegree ≤ totalDegree`.
A nonzero constant (`totalDegree = 0`) never
vanishes. **Not** labelled Schwartz–Zippel.

Level B: peel `xₙ` via `finSuccEquiv`. The leading
coefficient `g` is a nonzero polynomial in `n-1`
variables of `totalDegree ≤ d - k` if the last
degree is `k ≥ 0`. Split the box: tails where
`g` vanishes (IH) plus, for the other tails, at
most `k` roots in the last coordinate. Cap two
levels. No Alon–Füredi. No CNS re-proof.

## Canonical source (pin in this STATEMENT)

J. T. Schwartz, *Fast probabilistic algorithms for
verification of polynomial identities*, J. ACM 27
(1980) 701–717. R. Zippel, *Probabilistic algorithms
for sparse polynomials*, EUROSAM 1979. DeMillo–Lipton
1978. Compact form: Wikipedia *Schwartz–Zippel lemma*
— **v1 pins `n ≥ 1`, `f ≠ 0`, finite `S`, zeros in
`Sⁿ` ≤ `totalDegree * |S|^{n-1}`.** Type pin:
Mathlib `MvPolynomial.eval` / `totalDegree`. CNS
and Chevalley–Warning are **different** (consumed /
already-in) theorems, not this claim.

## Out of scope

- Alon–Füredi / combinatorial Nullstellensatz re-proof
- Chevalley–Warning re-proof
- Non-domain / PIT / algorithmic versions
- Ore Level B / `konig_edge_chromatic` / AES-B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
