# Hook-length formula (standard Young tableaux) — formalize-only

**id:** `hook-length`
**ticket:** OPE-1142 Scout leftover slot #2 (parent OPE-1141; post cauchy-binet #117 + bollobas-two-families #118)
**expected:** known-classical (Frame–Robinson–Thrall 1954) — **no novelty claim**

## Why not classical / why formalize-only

Settled enumerative combinatorics: if `μ` is a
Young diagram with `n` cells, the number of
standard Young tableaux of shape `μ` is

`n! / ∏_{c ∈ μ} hook(c)`

where the hook of cell `(i, j)` is
`(μ.rowLen i - j) + (μ.colLen j - i) - 1`
(arm + leg + 1). Completely classical
(Frame–Robinson–Thrall 1954). The hook-content
formula for *semi*standard tableaux is a
different theorem and is residual of *this* id.

Not an open problem. Not a novelty claim.

**Not** `YoungDiagram` / `rowLen` / `colLen`
(`Combinatorics/Young/YoungDiagram.lean` L60 /
L271 / L319) — already Mathlib; that is the
**shape**. USE them as glue; do **not**
re-prove Young diagrams. **Not**
`SemistandardYoungTableau`
(`Young/SemistandardTableau.lean` L52) — already
the SSYT filling; SYT is the bijective-`1..n`
special case, to be encoded, **not** a
re-proof of SSYT. **Not** Catalan numbers
(`Combinatorics/Enumerative/Catalan.lean`) —
already Mathlib (`catalan_eq_centralBinom_div`).
The 2-row shape `(n,n)` corollary *is* Catalan
and is **out of v1** (leftover-risk of the
already-in Catalan theorem and of the demoted
catalog row `catalan-recurrence`). Do **not**
re-prove Catalan. **Not** RSK / Schensted /
Littlewood–Richardson / Jacobi–Trudi.

Mathlib v4.10.0 already has the **Young
infra this theorem needs**:

- `YoungDiagram` (L60) / `YoungDiagram.card` (module doc L28)
- `rowLen` (L271) / `colLen` (L319)
- `SemistandardYoungTableau` (SSYT L52)
- `Nat.factorial` (`Data/Nat/Factorial/Basic.lean` L29)

There is **no** hook-length formula, **no**
named `hookLength` / `hook_length`, and **no**
SYT cardinality identity anywhere under
`Mathlib/` or `Archive/` (word-regexp
`hookLength` / `hook_length` / `HookLength`
this run → ZERO). Do **not** import
`Archive.*`.

OPE-1125 shortlist is **CONSUMED** (#117+#118).
This is a **fresh** catalog-audit id, **not**
a Catalan leftover continuation, **not** a
Bollobás leftover, **not** a Stirling leftover,
**not** a prize leftover, **not** a Formalist
Level B revival, **not** a third slot.

Mill NOW: finite tableau count leftover beside
Singleton (coding). `rowLen` / `colLen` are
waiting the same way `hammingDist` waits for
Singleton. **Not a rubber-stamp of Catalan.**

Do **not** describe an attack as discovering
the hook-length formula. Do **not** expand
into Catalan / RSK / hook-content as extra
namesakes (leftover-risk of Catalan **and**
of this id).

## Pinned convention (exact)

**v1 is the SYT hook-length identity only.**
Encoding: Mathlib `YoungDiagram` + `factorial`.
Count in `ℕ`.

Suggested pin:

```text
-- Level A (not labelled FRT / hook-length):
-- empty diagram (0! / empty product = 1);
-- one cell (1! / 1 = 1); one-row (n)
-- (hooks n,n-1,…,1 so n!/n! = 1, unique
-- increasing filling); one-column symmetric.
-- Not labelled hook-length.

def hook (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc : c ∈ μ) : ℕ :=
  (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

-- SYT = SSYT whose entries on μ.cells are
-- a bijection onto Finset.Icc 1 μ.card
-- (encode; do not re-prove SSYT).

-- Level B namesake
theorem hook_length (μ : YoungDiagram) :
    Fintype.card (SYT μ) * ∏ c : μ.cells, hook μ c.1 c.2
      = Nat.factorial μ.card
```

`c ∈ μ` is load-bearing for the hook
(otherwise `ℕ` subtraction underflows).
`rowLen` / `colLen` anti-monotonicity is
load-bearing for `hook ≥ 1` on cells.
Finite `μ.card` is load-bearing.

**Level A may land only** empty / one-cell /
one-row / one-column glue, **not** labelled
hook-length. Reuse Mathlib `YoungDiagram` /
`factorial` — **do not re-prove** Catalan /
SSYT.

**Level B** is the namesake FRT identity.
Engine classically: hook-walk / probabilistic
(Greene–Nijenhuis–Wilf) / RSK. Do not sorry
the namesake; honest partial is allowed
(comment residual, not `sorry`). Catalan /
hook-content / RSK are residual.

## Landmines

1. **Do not re-prove** `YoungDiagram` /
   `rowLen` / `colLen` / `SemistandardYoungTableau`
   / `Nat.factorial` / `catalan`. Already
   Mathlib.
2. **This is not** Catalan
   (`catalan_eq_centralBinom_div`). 2-row
   `(n,n)` is residual. Do **not** re-prime
   `catalan-recurrence`.
3. **This is not** SSYT (already the filling
   type). SYT is the standard special case.
4. **This is not** RSK / Schensted /
   Littlewood–Richardson / Jacobi–Trudi /
   hook-content (SSYT generating function).
5. **This is not** Stirling second kind
   (consumed #77 informal leftover namesake).
6. **`c ∈ μ` is load-bearing** for hooks.
7. **This is not** Singleton (the prime).
   **Not** Cauchy–Binet (#117) / Bollobás (#118).
8. **This is not** Ore / `konig_edge_chromatic`
   / AES / ostrowski / krenn-gu / hou-zeng-pfc
   / sun-135. Do not revive.
9. **Do not re-prime** the consumed mill list
   (cauchy-binet / bollobas-two-families /
   schwartz-zippel / hadamard-det /
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
   r33/r35/r333 / frobenius-coin-problem /
   catalan-recurrence).
10. **No `Archive.*` import.**
11. **Leave OPE-403 alone.**

## Proof sketch (classical)

Level A: empty `μ`, `0! = 1`, empty product
`1`, one empty tableau. One cell: hook `1`,
`1!/1 = 1`. One-row `(n)`: cells `(0,j)` have
hook `n-j`; product `n!`; unique SYT is
`1,2,…,n` left to right. One-column symmetric.
**Not** labelled hook-length.

Level B: FRT / hook-walk / GNW probabilistic
proof that the number of SYT is `n! / ∏ hook`.
Cap two levels. No Catalan corollary. No RSK.
No hook-content.

## Canonical source (pin in this STATEMENT)

J. S. Frame, G. de B. Robinson, R. M. Thrall,
*The hook graphs of the symmetric group*,
Canad. J. Math. 6 (1954) 316–324. Textbook:
Stanley, *Enumerative Combinatorics* vol. 2,
§7.21. Compact form: Wikipedia *Hook length
formula*. Type pin: Mathlib `YoungDiagram` /
`rowLen` / `colLen` / `factorial`. Catalan is
a **different** already-in theorem, not this
claim.

## Out of scope

- Catalan 2-row corollary / `catalan-recurrence` re-prime
- RSK / Schensted / Littlewood–Richardson / Jacobi–Trudi
- Hook-content formula (SSYT)
- Singleton (the prime) / Hamming-bound
- Cauchy–Binet (#117) / Bollobás (#118) Level B
- Prize leftovers (krenn-gu / hou-zeng / sun-135)
- Novelty / external claim
