# n-fold inclusion-exclusion (formalize-only)

**id:** `n-fold-inclusion-exclusion`
**ticket:** OPE-821 Scout RECOMMENDED PRIME (support OPE-820; post LLL #85 + Korselt #86)
**expected:** known-classical (de Moivre / Whitney; Wiedijk 100 #96) — **no novelty claim**

## Why not classical / why formalize-only

Settled enumerative identity: for a finite family of finite
sets `A i`, `i ∈ s`,

```text
|⋃_{i ∈ s} A i| = ∑_{∅ ≠ t ⊆ s} (-1)^{|t|+1} |⋂_{j ∈ t} A j|
```

Not an open problem. Two-set special case is already Mathlib
(`card_union` / `card_union_add_card_inter`). The **named n-fold
theorem** is the gap.

Mathlib v4.10.0 already has the **counting this theorem needs**:

- `Finset.card` / `union` / `inter` / `biUnion`
- two-set `card_union_add_card_inter` / `card_union`
  (`Data/Finset/Card.lean`) — **already upstream. Use it.
  Never re-prove. Never cite two-set union as this gap.**
- disjoint `card_biUnion` (pairwise-disjoint hypothesis) and
  `card_biUnion_le` (union bound) — **different** theorems.
  Disjoint-sum is not PIE.
- `Finset.powerset` / `erase`
- `Finset.inf'` on a nonempty index (`Data/Finset/Lattice.lean`)
  — intersection of `{A j | j ∈ t}` without needing `Fintype α`
  / `univ`
- `ℤ` / `zpow` for the sign `(-1)^{|t|+1}`

There is **no** n-fold inclusion-exclusion, **no**
`inclusion_exclusion`, **no** named PIE identity anywhere under
`Mathlib/` or `Archive/` (word-regexp `inclusion.exclusion` /
`InclusionExclusion` this run → ZERO). Wiedijk 100.yaml #96
lists only an **external Lean 3** link (Neil Strickland
`lean_lib` matching.lean) — **not** a Mathlib `decl`. Do **not**
treat that external file as upstream. Do **not** import
`Archive.*` (birthday / ballot are Archive-only and **different**
theorems).

OPE-804 considered this id and **benched it** only because the
leftover cap went to `korselt-carmichael`. Korselt is now
**CONSUMED** (#86). This is a **fresh** candidate, **not** a
Korselt leftover, **not** a third slot, **not** a Stirling
second-kind leftover (OPE-754 banned "inclusion-exclusion" as a
Stirling-B invention; that ban does not apply to a named Wiedijk
identity after the mill is consumed).

Mill NOW: enumerative combinatorics after a probabilistic prime
(LLL, **CONSUMED** #85) and an NT leftover (Korselt, **CONSUMED**
#86). **Not a rubber-stamp.**

Do **not** describe an attack as discovering PIE. Do **not**
expand into Bonferroni / truncated PIE / generating-function
forms / derangement re-proof (already Mathlib
`numDerangements`).

## Pinned convention (exact)

**v1 is the signed n-fold card identity**, not two-set, not a
measure-space PIE. Events are `Finset`s. Intersection over a
**nonempty** index uses `inf'` (no `Fintype α`). Empty index:
`biUnion` is empty, the nonempty-powerset sum is empty, both
sides `0`.

Suggested pin:

```text
def interOver {ι α : Type*} [DecidableEq α]
    (t : Finset ι) (A : ι → Finset α) (h : t.Nonempty) : Finset α :=
  t.inf' h A

theorem inclusion_exclusion {ι α : Type*}
    [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    ((s.biUnion A).card : ℤ) =
      ∑ t ∈ s.powerset.erase ∅,
        (-1 : ℤ)^(t.card + 1) * (interOver t A (by ...)).card
```

`s.powerset.erase ∅` is load-bearing: the empty intersection
would otherwise need a top `univ` that `Finset α` does not have
without `Fintype α`. v1 does **not** assume `[Fintype α]`.

**Level A may land only the three-set identity**, not labelled
PIE:

```text
|(A ∪ B ∪ C)|
  = |A|+|B|+|C| − |A∩B| − |A∩C| − |B∩C| + |A∩B∩C|
```

via two-set `card_union` twice. **Level B** is the n-fold
namesake `inclusion_exclusion` by induction on `s.card`
(insert + two-set split of the signed sum).

A ℕ two-sided rewrite (odd-cardinality sum = even-cardinality
sum + `|⋃|`) is acceptable as an equivalent namesake; do not
ship both as separate theorems.

## Landmines

1. **Do not re-prove two-set `card_union` /
   `card_union_add_card_inter`.** Already Mathlib. Use them.
2. **Disjoint `card_biUnion` is not this theorem.** Pairwise
   disjoint is a special case with one surviving term.
3. **This is not Bonferroni / truncated PIE / sieve remainder.**
   Out of v1.
4. **This is not derangement / Catalan.** Already Mathlib
   (`numDerangements`, `catalan`). PIE may be *used* in a
   derangement proof; do not re-prove those namesakes.
5. **This is not Stirling second kind.** Consumed PR **#77**
   (honest `informal`; namesake residual is a comment). Do not
   invent stirling-B / first-kind / Bell EGF as this leftover.
6. **This is not ballot / birthday.** Archive-only Wiedijk 67/93.
   Do not import `Archive.*`.
7. **This is not LLL / Korselt.** Consumed #85 / #86. Do not
   re-prime.
8. **Do not re-prime** lovasz-local-lemma / korselt-carmichael /
   vosper / heron / euclid-euler / bipartite / moore / stirling /
   kst / pentagonal / sunflower / combinatorial-nullstellensatz /
   kruskal-katona / oddtown / cayley / mycielski / friendship /
   havel / menger / greedy / Brooks / Dilworth / Eulerian /
   König / Dirac / EKR.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, PIE)

Level A: three-set. Write `A ∪ B ∪ C = (A ∪ B) ∪ C` and apply
`card_union` twice; expand intersections. **Not** labelled PIE.

Level B: induction on `s`. Empty: `0 = 0`. Insert `a ∉ s`:
`(insert a s).biUnion A = A a ∪ s.biUnion A`. Two-set formula
reduces the left side to `|A a| + |⋃_s| − |A a ∩ ⋃_s|`. The
right-hand signed sum splits into subsets not containing `a`
(IH) and subsets containing `a` (IH on the family
`j ↦ A a ∩ A j`). Cap two levels. No Bonferroni, no
derangement re-proof.

## Canonical source (pin in this STATEMENT)

Wiedijk 100 theorems, #96 "Principle of Inclusion/Exclusion".
Compact form: Wikipedia *Inclusion–exclusion principle*,
`|⋃ A_i| = ∑_{∅≠J⊆I} (-1)^{|J|+1} |⋂_{j∈J} A_j|`. Type pin:
`Finset.biUnion` + `powerset.erase ∅` + `inf'` intersections +
`ℤ` signs. Two-set `card_union`, disjoint `card_biUnion`,
derangement, Catalan, ballot, birthday, LLL, and Korselt are
**different** statements, not this claim. Strickland's external
Lean 3 file is **not** Mathlib.

## Out of scope

- Two-set union (already Mathlib)
- Bonferroni inequalities / truncated PIE
- Re-proving derangement / Catalan
- Stirling-B / first-kind / Bell EGF
- Ballot / birthday Archive imports
- Re-primes listed above
- Novelty / external claim
