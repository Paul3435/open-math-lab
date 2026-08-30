# Problem ledger — Open Math Lab

Source of truth for **which mathematical bets we have touched**, their disposition,
and pointers to artifacts. Update this file whenever a problem changes lifecycle
status. Catalog index: `catalog/problems.json`. Feasibility dossiers live under
`catalog/problems/<id>/` and/or `problems/<id>/`.

**Last updated:** 2026-08-30 (OPE-729 Formalist: combinatorial Nullstellensatz Alon 1999 non-vanishing Level A+B namesake landed, zero-sorry; Scout OPE-717 leftover slot #2 / Director OPE-728. Prior: OPE-722 sunflower #70.)

## Lifecycle labels

| Label | Meaning |
|-------|---------|
| `seed` | Placeholder / demo only — not a research bet |
| `candidate` | Scouted; not yet under active attack |
| `shortlisted` | Director approved for attack |
| `in_progress` | Attack or formalization running |
| `in_review` | Adversarial review gate |
| `heuristic` | Bounded compute / informal evidence only — **not** a proof |
| `informal` | Correct classical math + process artifacts; Lean incomplete or absent |
| `vetoed` | Claim or definition rejected (keep artifacts as calibration) |
| `formalized` | Lean-checked statement+proof (or certified compute) green |
| `archived` | Superseded, already-in-Mathlib, or intentionally dropped |

## Handled so far (touched by tickets)

| Problem ID | Domain | Tickets | Disposition | Novelty | Primary artifacts |
|------------|--------|---------|-------------|---------|-------------------|
| `combinatorial-nullstellensatz` | combinatorial algebra | OPE-717 Scout leftover slot #2; **OPE-728** Director assign leftover; **OPE-729** Formalist Level A+B | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/CombinatorialNullstellensatz.lean`. **Level A LANDED:** `n=0` nonzero constant (`combinatorial_nullstellensatz_zero`); univariate `Polynomial` root-cardinality glue (`univariate_nonvanishing`, **not** labelled CNS); `n=1` via `finSuccEquiv` (`combinatorial_nullstellensatz_one`); constants `C c` (`combinatorial_nullstellensatz_C`). **Level B namesake LANDED:** `theorem combinatorial_nullstellensatz` — per-variable `degreeOf i f ≤ t i`, `t i < (S i).card`, `coeff (Finsupp.equivFunOnFinite.symm t) f ≠ 0` ⇒ `∃ x, (∀ i, x i ∈ S i) ∧ eval x f ≠ 0`. Engine: induction on `n`; peel `x₀` via `finSuccEquiv`; leading-coefficient polynomial inherits tail `degreeOf` bounds; IH in `n` variables; univariate evaluation in `x₀`. `#print axioms combinatorial_nullstellensatz` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake build ProofLab.CombinatorialNullstellensatz` + `lake build ProofLab` green. **No novelty claim.** Finite boxes in a field. Per-variable `degreeOf`, **not** `totalDegree`. **Not Hilbert Nullstellensatz** (already upstream). **Not Chevalley–Warning** (already upstream). **Not EGZ.** Not Alon–Füredi / cap sets. **Not sunflower** (consumed OPE-722 / #70). Not Kruskal–Katona / Oddtown / EKR. Do **not** re-prime sunflower-erdos-rado / kruskal-katona / oddtown / cayley-trees / mycielski-triangle-free / havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Alon 1999, Theorem 1.2); Mathlib v4.10.0 has `MvPolynomial.coeff`/`degreeOf`/`eval`; ZERO combinatorial Nullstellensatz theorem | `catalog/problems/combinatorial-nullstellensatz/STATEMENT.md`, Lean `ProofLab/CombinatorialNullstellensatz.lean` |
| `sunflower-erdos-rado` | extremal set theory | OPE-717 Scout prime; **OPE-721** Director approve; **OPE-722** Formalist Level A+B; PR **#70** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Sunflower.lean`. **Level A LANDED:** `IsSunflower` (pairwise intersections = common core; empty core allowed; `card ≤ 1` vacuous); empty family; singleton family; `k=1` (`sunflower_k_one`); `r=0` (`r_zero_bound_unsat` — `0! (k-1)^0 = 1` cannot fire); `r=1` singletons (`sunflower_r_one`, pairwise disjoint petals). **Not labelled Erdős–Rado.** **Level B namesake LANDED:** `theorem erdos_rado_sunflower` — `r`-uniform family with `r! (k-1)^r < \|𝒜\|` and `1 ≤ k` contains a `k`-petal sunflower. Engine: induction on `r`; popular point `x` (degree `> (r-1)! (k-1)^{r-1}`) → traces `{s \\ {x}}` + lift; otherwise a maximum pairwise-disjoint subfamily of size `≥ k`, or else degree-sum `≤ r! (k-1)^r` contradicts the strict bound. `#print axioms erdos_rado_sunflower` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake build ProofLab.Sunflower` + `lake build ProofLab` green. **No novelty claim.** Finite only. **Not the sunflower conjecture** (open, out of v1). **Not ALWZ 2021.** **Not EKR** (`erdos_ko_rado` already in ProofLab). Not Oddtown / Eventown / Fisher / BIBD / Hilton–Milner. **Not Kruskal–Katona** (consumed OPE-707). Not Sperner / LYM / Sauer–Shelah. **Not combinatorial Nullstellensatz** (OPE-717 leftover, consumed OPE-729). Petal count `k`, uniformity `r`. `ℕ` subtraction load-bearing via `1 ≤ k`. Do **not** re-prime kruskal-katona / oddtown / cayley-trees / mycielski-triangle-free / havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Erdős–Rado 1960); Mathlib v4.10.0 has `Finset`/`Nat.factorial` only; ZERO sunflower / Δ-system theorem | `catalog/problems/sunflower-erdos-rado/STATEMENT.md`, Lean `ProofLab/Sunflower.lean` |
| `oddtown` | extremal set theory | OPE-702 Scout leftover slot #2; **OPE-711** Director approve leftover; **OPE-712** Formalist Level A+B; PR **#68 MERGED** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Oddtown.lean`. **Level A LANDED:** empty family `card ≤ n`; `n=0` no odd subset / odd family empty; `n=1` odd subset is `{0}` so family ⊆ `{{0}}` and `card ≤ 1`; `n` singletons odd, pairwise empty (even) intersection, card `n` (tightness). **Not labelled Oddtown.** **Level B namesake LANDED:** `theorem oddtown` — `Oddtown 𝒜 → 𝒜.card ≤ n`. Engine: `charVec s : Fin n → ZMod 2`; Gram `∑ i, charVec s i * charVec t i = |s ∩ t|` in `ZMod 2` is identity (`⟨v_s,v_s⟩=1`, `⟨v_s,v_t⟩=0` for `s≠t`); `LinearIndependent (ZMod 2)` of `{charVec s | s ∈ 𝒜}` then `fintype_card_le_finrank` + `finrank_pi` ⇒ `m ≤ n`. `#print axioms oddtown` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/Oddtown.lean` EXIT=0; `lake build ProofLab` green. **No novelty claim.** Finite only. **Not EKR** (`erdos_ko_rado` already in ProofLab). Not Eventown / Fisher / BIBD / Hilton–Milner. Not Sperner / LYM. **Not Kruskal–Katona** (consumed OPE-707). Characteristic vectors over `ZMod 2`, not `ℝ`. Graph `incMatrix` not used. Do **not** re-prime kruskal-katona / cayley-trees / mycielski-triangle-free / havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Berlekamp 1969 / Babai–Frankl); Mathlib v4.10.0 has `LinearIndependent`/`ZMod`/`Finset` only; ZERO Oddtown / Eventown / Berlekamp | `catalog/problems/oddtown/STATEMENT.md`, Lean `ProofLab/Oddtown.lean` |
| `kruskal-katona` | extremal set theory | OPE-702 Scout prime; **OPE-706** Director approve; **OPE-707** Formalist Level A+B; PR **#67 MERGED** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/KruskalKatona.lean`. **Level A LANDED:** empty family; singleton `r`-set (`(shadow {s}).card = s.card`); `r=0` shadow empty; nonempty `r=1` ⇒ `shadow = {∅}`; UV glue `card_shadow_uv_compression_le` (Mathlib `UV.card_shadow_compression_le`, **not** labelled KK). **Level B namesake LANDED:** `theorem kruskal_katona` — `(𝒜 : Set (Finset (Fin n))).Sized r` vs colex `IsInitSeg 𝒞 r` of equal card ⇒ `(shadow 𝒞).card ≤ (shadow 𝒜).card`. Engine: useful UV-compressions (`max U < max V`) until fully compressed; a fully compressed `r`-uniform family is a colex initial segment (`isInitSeg_of_compressed`); compression does not increase `|∂|`. Named existence lemma `exists_initSeg` (Mathlib `IsInitSeg.exists_initSeg`), not a second theorem. `#print axioms kruskal_katona` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake build ProofLab.KruskalKatona` + `lake build ProofLab` green. **No novelty claim.** Finite only. Colex, not lex. Uniform `Sized r` load-bearing. **Not Sperner / LYM** (already upstream). Not Dilworth / EKR / Hilton–Milner / Oddtown / Eventown. Lovász-ℝ binomial out of v1. Do **not** re-prime cayley-trees / mycielski-triangle-free / havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Kruskal 1963 / Katona 1968); Mathlib v4.10.0 has `shadow`/`IsInitSeg`/`UV.card_shadow_compression_le` only; ZERO KruskalKatona theorem | `catalog/problems/kruskal-katona/STATEMENT.md`, Lean `ProofLab/KruskalKatona.lean` |
| `mycielski-triangle-free` | graph theory | OPE-683 Scout #2; **OPE-694** Director approve leftover slot; **OPE-695** Formalist Level A+B; PR **#65** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Mycielski.lean`. **Level A LANDED:** `C5` on `Fin 5` is `CliqueFree 3` and `¬ Colorable 2` via Mathlib `Walk.three_le_chromaticNumber_of_odd_loop` on the length-5 closed walk (odd-loop glue, **not** labelled Mycielski). Corollary `mycielski_unbounded_of_le_two`. **Level B namesake LANDED:** `theorem mycielski_unbounded` — ∀ `k`, ∃ finite labelled `G : SimpleGraph (Fin n)` with `G.CliqueFree 3 ∧ ¬ G.Colorable k`. Engine: `μ(G)` on `V ⊕ V ⊕ Unit` (Lean right-assoc: first copy `inl`, shadow `inr ∘ inl`, extra `u = inr (inr ())` — copies not identified). Named facts: triangle-freeness preserved; `¬ Colorable k` ⇒ `μ` not `Colorable (k+1)` (recolour first copy by shadow colour when it used `u`'s class). Iterate from `K₂`; transport via `SimpleGraph.map` along `Fintype.equivFin`. `#print axioms mycielski_unbounded` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/Mycielski.lean` EXIT=0; `lake build ProofLab` green. **No novelty claim.** Finite only. **Not Brooks** (`χ` vs `Δ`). Not greedy. Not Grötzsch / Hajós / Kneser / Vizing / 4CT/5CT. Do **not** re-prime cayley-trees / havel-hakimi / menger-vertex / greedy / Brooks A/B / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Mycielski 1955); Mathlib v4.10.0 has `CliqueFree`/`Colorable`/`chromaticNumber`/`three_le_chromaticNumber_of_odd_loop` only; ZERO `Mycielski` | `catalog/problems/mycielski-triangle-free/STATEMENT.md`, Lean `ProofLab/Mycielski.lean` |
| `cayley-trees` | graph theory | OPE-683 Scout prime; **OPE-687** Director approve; **OPE-688** Formalist Level A; PR **#64** | **`informal`** (formalize-only, honest partial). Lean **zero-sorry** `ProofLab/CayleyTrees.lean`. **Level A LANDED:** encoding `LabelledTree n := { s : Finset (Sym2 (Fin n)) // (∀ e ∈ s, ¬ e.IsDiag) ∧ (fromEdgeSet ↑s).IsTree }` (nodiag conjunct is load-bearing: `fromEdgeSet` drops loops). Glue `labelledTree_card_edges` (`|E| = n-1` via `IsTree.card_edgeFinset`). `n=1` empty/`⊥` (`cayley_formula_one`, `1^(1-2)=1`); `n=2` `K₂` (`cayley_formula_two`); `n=3` three labelled paths (`cayley_formula_three`); bundled `cayley_formula_of_le_three`. `#print axioms` on Level A theorems = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/CayleyTrees.lean` EXIT=0; `lake build ProofLab` green. **Namesake residual:** `cayley_formula` (`Fintype.card (LabelledTree n) = n^(n-2)` for all `n≥1`) needs Prüfer bijection `LabelledTree n ≃ Fin (n-2) → Fin n` for `n≥2` (or equivalent induction); **not** sorry-ed. **No novelty claim.** Not group Cayley. Not Cayley–Hamilton. Not Cayley graphs. Not Kirchhoff / matrix-tree. Not Tutte / Whitney / unlabelled A000055. Do **not** re-prime havel-hakimi / menger-vertex / greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Cayley 1889 / Prüfer 1918); Mathlib v4.10.0 has `IsTree`/`fromEdgeSet`/`card_edgeFinset` only; ZERO Prüfer / labelled-tree count | `catalog/problems/cayley-trees/STATEMENT.md`, Lean `ProofLab/CayleyTrees.lean` |
| `menger-vertex` | graph theory | OPE-666 Scout #2; **OPE-677** Director approve remaining slot after Havel; **OPE-678** Formalist Level A; PR **#62 MERGED** (`abf60474`, 2026-08-29T23:05:43Z) | **`informal`** (formalize-only, honest partial). Lean **zero-sorry** `ProofLab/Menger.lean`. **Level A LANDED:** Diestel A–B path / `IsABSeparator` / `HasPack` / `p` / `s` (global form, fully vertex-disjoint including ends). Easy `p ≤ s` (`packingNumber_le_separatorNumber`). `A ∩ B` load-bearing: trivial `Walk.nil` packing + every separator contains the intersection (`packingNumber_ge_inter`, `separatorNumber_ge_inter`, `inter_nonempty_bounds`). Singleton `A={a}`, `B={b}` joined by an edge ⇒ `p = s = 1` (`menger_vertex_singletons_adj`). No A–B path (hence `A ∩ B = ∅`) ⇒ `p = s = 0` (`menger_vertex_no_path`). Diestel `|E|=0` base `menger_bot`: `p = s = |A ∩ B|` on `⊥`. `#print axioms` on Level A theorems = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/Menger.lean` EXIT=0; `lake build ProofLab` green. **Namesake residual:** `menger_vertex` (`s = p`) needs Diestel induction on `card G.edgeFinset` (critical-edge / separator-split + glue); **not** sorry-ed. Named engine this heartbeat. Optional König split-graph reduction not attacked. **No novelty claim.** Finite only. Global form, not local `κ(u,v)`. Not König `ν=τ`. Not edge-Menger. Not max-flow. Not infinite Erdős–Menger. Not Tutte / Whitney. Do **not** re-prime greedy / Brooks / Dilworth / Eulerian / Dirac / König / Havel–Hakimi. Leave OPE-403 alone. | Known classical (Menger 1927 / Diestel 3.3.1); Mathlib v4.10.0 has `Walk`/`IsPath`/`Reachable` only; ZERO `Menger` / graph `IsSeparator` | `catalog/problems/menger-vertex/STATEMENT.md`, Lean `ProofLab/Menger.lean` |
| `havel-hakimi` | graph theory | OPE-666 Scout prime; **OPE-670** Director approve; **OPE-671** Formalist Level A + reverse; PR **#61 MERGED** (`9dab9a5`, 2026-08-29T22:06:24Z) | **`informal`** (formalize-only, honest partial). Lean **zero-sorry** `ProofLab/HavelHakimi.lean`. **Level A LANDED:** empty / all-zeros (`⊥`) / complete (`⊤`) / `K₂=(1,1)` / non-graphic `(1)` on `n=1` and `(2,2,0,0)` landmine + `d i < n` glue + handshaking necessary (`graphic_even_sum`, not sufficient). **Reverse-reduction LANDED:** `isGraphic_of_reduce` — `ReduceOK d` + `IsGraphic (reduce d h)` ⇒ `IsGraphic d` by inserting a vertex adjacent to the first `s = d 0` of the remainder (unsorted) after unsorting via `isGraphic_sortNoninc`. Failed reduction ⇒ `¬ IsGraphic` (`not_graphic_of_not_reduceOK`). Encoding: labelled `SimpleGraph (Fin n)`; `reduce` only on `ReduceOK` (failed reduction is not passed to `IsGraphic`). Re-sort after reduction is load-bearing (`sortNoninc`). `#print axioms isGraphic_of_reduce` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/HavelHakimi.lean` EXIT=0; `lake build ProofLab` green. **Namesake residual:** `havel_hakimi` iff forward (`IsGraphic d → IsGraphic (reduce d h)`) needs Havel switching so vertex `0` is adjacent to the next `s` vertices, then delete; **not** sorry-ed. **No novelty claim.** Not Erdős–Gállai. Not Gale–Ryser. Not Tutte. Do **not** re-prime greedy / Brooks / Dilworth / Eulerian / König / Dirac. Leave OPE-403 alone. | Known classical (Havel 1955 / Hakimi 1962); Mathlib v4.10.0 has `degree`/`handshaking` only; ZERO `IsGraphic`/`Havel`/`Hakimi` | `catalog/problems/havel-hakimi/STATEMENT.md`, Lean `ProofLab/HavelHakimi.lean` |
| `brooks-coloring` | graph theory | OPE-640 Scout #2; **OPE-650** Director approve unused slot; **OPE-651** Formalist Level A; **OPE-658** Formalist Level B Δ≤2; PR **#59 MERGED** (`ea69b7b`) | **`informal`** (formalize-only, honest partial). Lean **zero-sorry** `ProofLab/Brooks.lean`. Level A consumed (PR **#58**): `IsOddCycle` pin; `⊤` / odd-cycle exceptions `χ=Δ+1`; greedy reused not labelled Brooks. **Level B Diestel first family LANDED:** `brooks_colorable_of_maxDegree_le_two` — connected, `G ≠ ⊤`, `¬ IsOddCycle`, `Δ ≤ 2` ⇒ `Colorable Δ`. Named: even 2-regular along Hierholzer circuit (index mod 2); paths by deleting a degree-1 vertex and extending a 2-colouring; `Δ ≤ 1` vacuous (those connected graphs are complete). Cheap corollary `chromaticNumber_le_maxDegree_of_maxDegree_le_two`. `#print axioms brooks_colorable_of_maxDegree_le_two` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake build ProofLab.Brooks` + `lake build ProofLab` green. **Namesake residual:** `brooks_colorable` (no Δ bound) not proved — remaining family is Δ-regular Δ≥3 not-complete (Kempe / Lovász contraction sink); **not** sorry-ed. **No novelty claim.** Not greedy. Not Vizing. Not 4CT/5CT. Do **not** re-prime greedy / Dilworth / Eulerian / König / Dirac / Level A. Do **not** expand into list-colouring Brooks. | Known classical (Brooks 1941 / Diestel); Mathlib v4.10.0 has `Colorable`/`maxDegree`/`chromaticNumber_top`/`three_le_chromaticNumber_of_odd_loop` defs only; ZERO `brooks` | `catalog/problems/brooks-coloring/STATEMENT.md`, Lean `ProofLab/Brooks.lean` |
| `greedy-chromatic` | graph theory | OPE-640 Scout prime; **OPE-644** Director approve; **OPE-645** Formalist Level A+B | **`formalized`** (formalize-only, PR **#57**). Lean **zero-sorry** `ProofLab/GreedyChromatic.lean`: Level A empty / edgeless (`maxDegree = 0`) / complete (`⊤`) / `card = 1` + `degree_le_maxDegree` glue. **Level B namesake LANDED:** `theorem greedy_colorable` — `G.Colorable (G.maxDegree + 1)` by induction on `Fintype.card V` (delete `v`; IH colours `G−v`; `degree v ≤ Δ` neighbours leave one colour in `Fin (Δ+1)`). Encoding Mathlib `Coloring.mk` on `Fin (G.maxDegree + 1)`. Cheap corollary `chromaticNumber_le_maxDegree_add_one`. Stretch tightness `χ = Δ+1` on nonempty `⊤` (reuse `chromaticNumber_top`). `#print axioms greedy_colorable` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake build ProofLab.GreedyChromatic` + `lake build ProofLab` green. **No novelty claim.** Finite only. `DecidableRel G.Adj` load-bearing. **Not Brooks** (`χ ≤ Δ` except `⊤` / odd cycles). Not Vizing. Not 4CT/5CT. **Do not re-prime. Do not expand into Brooks / list-colouring.** | Known classical (Diestel / greedy folklore); Mathlib v4.10.0 has `Colorable`/`chromaticNumber`/`maxDegree` defs only | `catalog/problems/greedy-chromatic/STATEMENT.md`, Lean `ProofLab/GreedyChromatic.lean` |
| `dilworth-poset` | order theory / combinatorics | OPE-613 Scout prime; **OPE-618** Director assign; **OPE-619** Formalist Level A (PR **#53 MERGED**, `5e81caf`); **OPE-626** Formalist Level B (PR **#54 MERGED**, `622d076`); Adversarial **OPE-628 APPROVE** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Dilworth.lean`: Level A consumed (`width_le_chainPartition` + empty/chain/antichain/2-element + Fulkerson `splitGraph`). **Level B namesake LANDED:** `theorem dilworth` — ∀ finite `PartialOrder` there is a chain partition of `univ` of size `width`, via matching successors in `splitGraph` (strict `<` on `α ⊕ α`) + König `ν=τ` as *engine* (`konig_bipartite`, not cited as Dilworth). `#print axioms dilworth` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/Dilworth.lean` EXIT=0; `lake build ProofLab` green. **No novelty claim.** Not König A/B. Not Hall. Not Mirsky. Not comparability graph. Finite only. **Do not re-prime Level A, Level B, or invent Level C / Mirsky / Greene.** Director OPE-632 DECLINED Dilworth residual — residual EMPTY. | Known classical (Dilworth 1950 / Fulkerson 1956); Mathlib v4.10.0 has `IsChain`/`IsAntichain` defs only | `catalog/problems/dilworth-poset/STATEMENT.md`, Lean `ProofLab/Dilworth.lean` |
| `eulerian-hierholzer` | graph theory | OPE-574 Scout prime; **OPE-579** Formalist Level A; **OPE-591** Scout Level B re-score (#2); **OPE-597** Formalist Level B circuit (PR **#51 MERGED**, `396e2a6`); **OPE-613** Scout trail residual #2; **OPE-633** Formalist trail (PR **#55 MERGED**, `6c32a467`); Adversarial **OPE-634 APPROVE**; PRG **OPE-637** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Eulerian.lean`: Level A reused (`eulerian_k1` / `eulerian_cycle` / `eulerian_k2`). Level B circuit consumed (`eulerian_hierholzer_circuit` + `eulerian_complete_odd`). **Trail clause LANDED:** `theorem eulerian_hierholzer_trail` — finite connected `SimpleGraph`, `card oddDeg = 2` → open Eulerian trail between the two odd-degree vertices. Encoding: longest trail **starting at an odd-degree vertex**; Hierholzer splice of a closed unused even-degree detour. **No dummy-edge.** `#print axioms eulerian_hierholzer_trail` = `propext` / `Classical.choice` / `Quot.sound` (no `sorryAx`). `lake env lean ProofLab/Eulerian.lean` EXIT=0; `lake build ProofLab` green. **No novelty claim.** Do **not** import `Archive.*`. Not Königsberg. Not Dirac. **Do not re-prime Level A, Level B circuit/complete-odd, or this trail theorem.** | Known classical (Euler 1736 / Hierholzer 1873); Mathlib v4.10.0 has `IsEulerian` + necessary `card_odd_degree` only; Trails.lean L26–29 existence TODO is the Mathlib gap this theorem fills on the 2-odd side | `catalog/problems/eulerian-hierholzer/STATEMENT.md`, Lean `ProofLab/Eulerian.lean` |
| `konig-bipartite` | graph theory | OPE-574 Scout #2; **OPE-580** Formalist Level A; **OPE-591** Scout Level B re-score (PRIME); **OPE-596** Formalist Level B (PR **#50 MERGED**, `684316b`) | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/Konig.lean`: Level A predicates reused; **`konig_bipartite`** (`G.Colorable 2 → matchingNumber = vertexCoverNumber`) via Hall deficiency / dummy-vertex reduction of the *graph* min-max (not citing `hall_hard_inductive` as König). `complete_three_ne` remains the load-bearing `K_3` landmine. Encoding Mathlib `Subgraph.IsMatching` + `Colorable 2` + ProofLab `IsVertexCover`. `lake env lean ProofLab/Konig.lean` EXIT=0. **No novelty claim.** Not `χ'=Δ`. Not König's lemma. Not Tutte. **Do not re-prime Level A/B.** Dilworth is a *separate consumed* id (`dilworth-poset`, PRs **#53+#54 MERGED**), not this row. | Known classical (Kőnig 1931); Mathlib v4.10.0 has `IsMatching`, no vertex cover / no `ν=τ` | `catalog/problems/konig-bipartite/STATEMENT.md`, Lean `ProofLab/Konig.lean` |
| `dirac-hamiltonian` | graph theory | OPE-553 Scout #2; OPE-559 Level A; **OPE-568** Level B | **`formalized`** (formalize-only). PRs **#44** (Level A) and **#45 MERGED** (`3723b07`, 2026-08-28). Lean **zero-sorry** `ProofLab/Dirac.lean`: `dirac_hamiltonian` (`3 ≤ n → 2 * minDegree ≥ n → IsHamiltonian`) via longest-path / cycle-closing. Reuses Level A `connected_of_dirac`, `isHamiltonian_complete`, `dirac_hamiltonian_card_eq_three`. `lake build ProofLab.Dirac` + `lake build ProofLab` green. **No novelty claim.** n≥3 load-bearing. Cycle, not path. Ore stretch not attacked — not a Scout leftover re-prime. Do **not** re-prime Level A/B. | Known classical (Dirac 1952); Mathlib v4.10.0 has Hamiltonian defs only | `catalog/problems/dirac-hamiltonian/STATEMENT.md`, Lean `ProofLab/Dirac.lean` |
| `euler-odd-distinct` | partition theory | OPE-553 Scout prime; **OPE-558** Formalist | **`formalized`** (formalize-only). PR **#43 MERGED**. Lean **zero-sorry** `ProofLab/EulerPartition.lean`: `euler_odd_eq_distinct` (`Finset.card_bij'` Glaisher, no mod-6 filter) + Level A `n≤10` `native_decide` guard. `lake env lean` EXIT=0; `lake build ProofLab` green. Axioms: ∀n = propext/Classical.choice/Quot.sound only (no `sorryAx`, no `ofReduceBool` on the identity). **No novelty claim.** Do **not** import Archive/Theorems100. Do **not** re-prime `schur_partition`. | Known classical (Euler 1748 / Glaisher 1883); Mathlib v4.10.0 has `odds`/`distincts` defs only — card equality was Archive GF, not Mathlib | `catalog/problems/euler-odd-distinct/STATEMENT.md`, Lean `ProofLab/EulerPartition.lean` |
| `erdos-ko-rado` | extremal set theory | OPE-533 Scout prime; **OPE-534** Level A; **OPE-541** Katona Level B | **`formalized`** (formalize-only). PRs **#39** and **#41 MERGED**. Lean zero-sorry `ProofLab/ErdosKoRado.lean` (`erdos_ko_rado`). Do **not** re-prime. | Known classical (1961); Mathlib gap was k-uniform (non-uniform `Intersecting.card_le` only) | `problems/erdos-ko-rado/STATEMENT.md`, Lean `ProofLab/ErdosKoRado.lean` |
| `friendship-windmill` | graph theory | OPE-533 Scout #2; **OPE-535** | **`formalized`** (formalize-only). PR **#40 MERGED**. Lean zero-sorry `ProofLab/Friendship.lean`. Finite graphs only. Do **not** re-prime. | Known classical (ERS 1966); Mathlib gap (defs `commonNeighbors`/`IsSRGWith`; theorem was Archive-only) | `problems/friendship-windmill/STATEMENT.md`, Lean `ProofLab/Friendship.lean` |
| `schur-partition-full-glaisher` | partitions | OPE-458 bench; OPE-440/445/447 ladder; **OPE-463** | **`formalized`** (formalize-only). `theorem schur_partition` in `ProofLab/SchurGlaisher.lean` (`Finset.card_bij'` Glaisher, zero-sorry) on merged main. Unbench criteria met (PRs #30/#31/#32 MERGED) **and** ∀n identity landed — treat as CONSUMED. Do **not** re-prime. | Known classical (Schur 1926 / Glaisher); Mathlib still has no Schur-partition theorem | `ProofLab/SchurGlaisher.lean`, `catalog/problems/schur-partition-full/` |
| `ramsey-multicolor-r333` | graph theory / combinatorics | OPE-458 Scout prime; **OPE-461 Formalist** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/RamseyMulticolor.lean`: `r333_gt_16` (GG F₂⁴ cert on Fin 16, `native_decide`); `r333_le_17` (pigeonhole deg≥6 + `ramsey33_clique_inside_finset` pullback); `r333_eq_17`. `lake env lean` EXIT=0; `lake build ProofLab` green. Axioms: propext/Quot.sound/Classical.choice/`Lean.ofReduceBool` only. **No novelty claim**. PR **#36 MERGED**. | Known classical (Greenwood–Gleason 1955); Mathlib gap (no multicolour Ramsey) | `problems/ramsey-multicolor-r333/STATEMENT.md`, Lean `ProofLab/RamseyMulticolor.lean`, `attacks/ramsey-multicolor-r333-20260825-ope461/`, cert `catalog/problems/ramsey-multicolor-r333/witness16_certificate.txt` |
| `erdos-woods` | elem. number theory | OPE-12 attack; OPE-15 hygiene veto; OPE-334 dossier refresh; **OPE-391 Formalist** | **formalize-only, Lean ZERO-sorry** (`ProofLab/ErdosWoodsCorrect.lean`): literature predicate open interval `(a,a+k)`; `isErdosWoodsWitness_16_2184` + `erdos_woods_16` via `interval_cases`+`native_decide` on 15 interiors; `lake env lean ProofLab/ErdosWoodsCorrect.lean` EXIT=0; `ProofLab.lean` EXIT=0. Vetoed wrong draft renamed `ErdosWoodsVetoed.lean` (not imported). Minimality of a=2184 **not** proven (literature/OEIS). **No novelty claim**. Prior OPE-12 claim remains vetoed. | Known (1980) | `problems/erdos-woods/`, Lean `ProofLab/ErdosWoodsCorrect.lean`, `attacks/erdos-woods-20260730-125506/` (+ BOARD_VETO) |
| `sum-free-subsets` | additive combinatorics | OPE-14 (board may still be open); children OPE-23/32/33/34 | **Classical Erdős (1965)** process demo. **Lean ZERO-sorry** (`sum_free_subset_bound`, wired via `erdos_sum_free_bound`; `lake env lean ProofLab/SumFree.lean` exit 0); Erdős computational verify 200/200. Adversarial veto (2026-07-31, 3 sorries + strategy mismatch) **lifted** by Adversarial Reviewer 2026-08-07. Known theorem — **`informal` / process fuel, not a discovery claim**. `lake build ProofLab` OK | Known theorem | `problems/sum-free-subsets/`, `attacks/sum-free-subsets-20260730-221216/`, Lean `ProofLab/SumFree.lean` (+ `ErdosSumFree.lean`) |
| `graceful-tree-conjecture` (bounded caterpillars n≤12) | graph theory | OPE-13 attack; OPE-18 review; OPE-20 re-review | **`heuristic`** bounded verify: 560 distinct non-iso caterpillars, 0 search failures after dedup. Family already known graceful for all n (Rosa/Golomb). **Not** full GTC; **not** Lean-gated | Sanity check, not new math | `problems/graceful-tree-conjecture/`, `attacks/graceful-tree-conjecture-20260731-094627/` |
| `schur-partition` | partitions | OPE-2 seed; OPE-25 shortlist; OPE-21 Director approve; OPE-26 Level A+B; **OPE-424 partial ladder**; **OPE-447/463 Glaisher ∀n** | **OPE-424 finite-certificate scope remains `heuristic`** (n≤24 DP / n≤12 Finset; PR #27). **∀n identity CONSUMED** as `theorem schur_partition` in `ProofLab/SchurGlaisher.lean` (zero-sorry Glaisher bijection). Do **not** re-prime either scope. STATEMENT pin 2026-08-04 held. | Known (1926); Mathlib still has no Schur-partition theorem | `problems/schur-partition/`, `ProofLab/Schur.lean`, `ProofLab/SchurGlaisher.lean` |
| `frobenius-coin-problem` | number theory | OPE-21/22; OPE-25 | **process-fuel** (not gap prime). Mathlib already has `frobeniusNumber_pair`. Level A/B artifacts under attack dir + `ProofLab/Frobenius.lean` | Known textbook; already-in-Mathlib | `problems/frobenius-coin-problem/`, `attacks/frobenius-coin-problem-20260804-222513/` |
| `ramsey-r35` | graph theory / combinatorics | OPE-390 scout prime; **OPE-393** attack | **`formalized`** (formalize-only). Lean **zero-sorry** `ramsey35_eq_14` in `ProofLab/Ramsey.lean`: lower circulant C13({±1,±5}) `native_decide`; upper `R(2,5)+R(3,4)=5+9` via `ramsey_two_right` + `ramsey34_le_9` + `ramseyUpper_add`. `lake build ProofLab` green. Default **no claim**. | Known classical (Greenwood–Gleason 1955); Mathlib gap remains for upstream packaging | `problems/ramsey-r35/`, Lean `ProofLab/Ramsey.lean`, `attacks/ramsey-r35-20260824/` |
| `ramsey-r33` | graph theory / combinatorics | OPE-40 scout keep-fresh; OPE-43 shortlist+prime; OPE-44 attack | **`formalized`** (formalize-only). Lean **zero-sorry**, `lake build ProofLab` green: `ramsey33_eq_6`, `ramsey34_eq_9`, `ramsey44_eq_18` (`ProofLab/Ramsey.lean`). Hand pigeonhole R(3,3)≤6; degree-parity R(3,4)≤9; recurrence R(4,4)≤18; lower bounds via C5 / 8-vtx witness / Paley-17. Default **no claim**. Board 2026-08-24: independent `lake env lean ProofLab/Ramsey.lean` EXIT=0. | Known classical; **genuine Mathlib gap** (no Ramsey theorem in v4.10.0) | `problems/ramsey-r33/`, Lean `ProofLab/Ramsey.lean` |
| `erdos-szekeres-monotone` | combinatorics / order theory | OPE-430 scout prime; **OPE-433 attack**; OPE-437 re-verify; OPE-438 adversarial APPROVE (PR #29) | **CLOSED — formalize-only, Lean ZERO-sorry.** Full finite ES monotone theorem: every sequence on a linear order of length ≥ (r−1)(s−1)+1 has a weakly increasing subsequence of length r or weakly decreasing of length s (`ProofLab/ErdosSzekeres.lean`: `erdosSzekeres_monotone`; incLen/decLen pigeonhole; weak mono + `List.Sorted` pin). Do not re-prime this scope. | Known (1935); genuine gap at attack time (only infinitary lemma upstream) | `problems/erdos-szekeres-monotone/`, `attacks/erdos-szekeres-monotone-20260825/`, Lean `ProofLab/ErdosSzekeres.lean`, PR #29 |
| `van-der-waerden-w24` | additive combinatorics | OPE-430 bench; Director OPE-454; **OPE-455 Attack Lead**; OPE-456 adversarial APPROVE (PR #33) | **PARTIAL ladder closed:** STATEMENT pinned (HasMono4: exists a d, 0<d, a+3d<n, all four equal); `vdw24_gt_34` via witness34 colouring `0010001110100100011101001000111011` on Fin 34, native_decide, zero sorry. **Upper W(2,4)≤35 OPEN** (Chvátal 1979 computer-assisted; no hand certificate named → only eligible as bench with concrete case-split strategy per OPE-458 commission). No novelty/claim. | Known classical; Mathlib finitary VdW TODO (HalesJewett.lean L53) | `problems/van-der-waerden-w24/`, `attacks/van-der-waerden-w24-20260825-ope455/`, Lean `ProofLab/VanDerWaerden.lean`, PR #33 |
| `ramsey-r35` | graph theory / combinatorics | OPE-390 scout; OPE-393 attack; OPE-410 finish | **`formalized`** (formalize-only). R(3,5)=14 Lean **zero-sorry**: upper bound hand degree-counting; lower bound 13-vtx witness via decidable clique check. Gate-approved PRs #22/#23/#24/#25. Known-classical, no claim. | Known classical; genuine Mathlib gap (no Ramsey theorem in v4.10.0) | `problems/ramsey-r35/`, `ProofLab/Ramsey*.lean` |
| `happy-ending-es3` | discrete geometry | OPE-403 attack; OPE-410 finish | **`formalized`** (formalize-only). ES(3)=5: any 5 points in general position contain a convex 4-gon. Lean **zero-sorry** with new orientation/order-type plumbing (reusable infra). ES(4)=9 stretch **not** attacked. Gate-approved PRs #23/#24/#25. Known-classical, no claim. | Known classical (Erdős–Szekeres 1935); genuine Mathlib gap (no happyEnding/ErdosSzekeres content v4.10.0) | `problems/happy-ending-es3/`, `ProofLab/` ES files |
| `van-der-waerden-w23` | additive combinatorics | OPE-45 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/VanDerWaerden.lean`): `vdw_le_9` (every 2-colouring of `Fin 9` has a mono 3-AP, `native_decide`) + `vdw_gt_8` (witness `11001100` on `Fin 8` with none). ⇒ W(2,3)=9. `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/VanDerWaerden.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — finitary VdW still an explicit TODO in the pinned `Mathlib/Combinatorics/HalesJewett.lean` (~L51) | Known classical; genuine Mathlib TODO (HalesJewett.lean) | `proofs/lean-project/ProofLab/VanDerWaerden.lean`, `problems/van-der-waerden-w23/` |
| `van-der-waerden-w24` | additive combinatorics | Scout OPE-430 bench; Director OPE-454; **OPE-455 Attack Lead** | **PARTIAL ladder (formalize-only)**: STATEMENT pinned; Lean `HasMono4` + `vdw24_gt_34` (`¬ HasMono4 witness34` on Fin 34 colouring `0010001110100100011101001000111011`, `native_decide`) ⇒ **W(2,4)>34**, zero sorry. **Upper `W(2,4)≤35` NOT proved** (Chvátal 1979 computer-assisted; no brute force in Lean; timebox). Exact equality open in Lean. `lake env lean` + `lake build ProofLab` green. **No novelty / no claim.** | Known classical; Mathlib finitary VdW TODO | `problems/van-der-waerden-w24/`, `attacks/van-der-waerden-w24-20260825-ope455/`, Lean `ProofLab/VanDerWaerden.lean` |
| `schur-number` | additive combinatorics | OPE-46 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/SchurNumber.lean`): `schur2_lower`/`schur2_le_4` ⇒ S(2)=4 (classes {1,4}/{2,3}, least-forcing N=5); `schur3_lower`/`schur3_le_13` ⇒ S(3)=13 (classes {1,4,7,10,13}/{2,3,11,12}/{5,6,8,9}, least-forcing N=14). Convention pinned (x=y allowed, standard). `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/SchurNumber.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — no SchurNumber/additive-Schur content anywhere in the v4.10.0 Mathlib pin | Known classical; genuine Mathlib gap (no SchurNumber content) | `proofs/lean-project/ProofLab/SchurNumber.lean`, `problems/schur-number/` |
| `weak-schur-ws2` | additive combinatorics | OPE-458 Scout #2; Director OPE-460; **OPE-462 Attack Lead** | **CLOSED — formalize-only, Lean ZERO-sorry.** `ProofLab/WeakSchur.lean`: `HasMonoWeakSchur` (x≠y pin; Fin n ↔ {1..n}); `ws2_gt_7` via witness `00101110` classes `{1,2,4,8}`/`{3,5,6,7}`; `ws2_le_8` exhaustive `native_decide` on all `2^9=512` colourings of Fin 9; `ws2_eq_8` ⇒ **WS(2)=8**. `lake env lean ProofLab/WeakSchur.lean` EXIT=0; `lake build ProofLab` green; axioms = propext/choice/ofReduceBool/Quot.sound only. STATEMENT pin distinguishes weak vs strong Schur and vs schur-partition. **No novelty claim.** | Known classical (Abbott–Wang / Exoo); Mathlib gap (no weak-Schur) | `problems/weak-schur-ws2/STATEMENT.md`, `attacks/weak-schur-ws2-20260825-ope462/`, Lean `ProofLab/WeakSchur.lean` |
| `erdos-szekeres-monotone` | combinatorics / order theory | OPE-430 scout prime; **OPE-433 attack** | **`formalized`** (formalize-only). Lean **zero-sorry**, `lake build ProofLab` green: `erdosSzekeres_monotone` + `erdosSzekeres_card_bound` (`ProofLab/ErdosSzekeres.lean`). Weak mono pin (`List.Sorted (· ≤ ·)` / `(· ≥ ·)`); classic (a_i,b_i) labelling + `Fintype.card_le_of_injective`. `lake env lean ProofLab/ErdosSzekeres.lean` EXIT=0. Default **no claim**. | Known classical (1935); **genuine Mathlib gap** (only infinitary ES in v4.10.0) | `problems/erdos-szekeres-monotone/`, Lean `ProofLab/ErdosSzekeres.lean`, `attacks/erdos-szekeres-monotone-20260825/` |
| `happy-ending-es3` | discrete geometry | OPE-390 scout; OPE-402 ratify PRIME; OPE-403 partial; **OPE-410 finish**; **OPE-413 review APPROVED** | **`formalized`** (formalize-only). Full `es_three_eq_five : EsThreeEqFiveStatement` zero-sorry in `ProofLab/HappyEndingES3.lean`: F1 `InConvexPosition4 ↔ ConvexIndependent`, `hullVertices_card_ge_three_of_gp`, hull≥4 case, separating-line interior case (`es_three_eq_five_of_hull_card_eq_three`). OPE-413 adversarial: lake env lean EXIT=0, lake build ProofLab green, axiom audit no `sorryAx` (propext/Classical.choice/Quot.sound only). PR #25 head `d46ca64` (base still PR #24 / F2). **No novelty claim** (classical 1935). ES(4)=9 out of scope. Board merge order #23→#24→#25. | Known classical (1935); Mathlib gap (orientation glue) | `problems/happy-ending-es3/STATEMENT.md`, Lean `ProofLab/HappyEndingES3.lean`, `attacks/happy-ending-es3-20260824-ope410/`, PR #25 |


## Pipeline / infrastructure (not math bets)

| Work | Tickets | Notes |
|------|---------|-------|
| mathforge scaffold, rubric, catalog, CLI | OPE-1…OPE-11, OPE-9 | Tooling for triage + attack logs |
| Lean 4 + elan + lake build | OPE-17 (board OK) | Toolchain green; claims still board-gated |
| Workspace SoT + GitHub PR workflow | OPE-16, docs | Git SoT: `Documents/VSCode/open-math-lab` |
| Review checklist + claim gates | OPE-10, OPE-5 | `docs/REVIEW_CHECKLIST.md`, `docs/CLAIM_POLICY.md` |

## Untouched / catalog candidates (Scout refreshed — OPE-25)

**OPE-21 process breach corrected by OPE-25.** Only genuine Mathlib-gap scores survive.
`frobenius`, `derangement`, `catalan` were scored on false "Mathlib gap" assumptions and are
already covered upstream; `schur-partition` is the only confirmed gap among prior candidates.

| Problem ID | Status | Domain | Notes |
|------------|--------|--------|-------|
| **`schur-partition`** | **`heuristic` — OPE-424 partial ladder reviewer-approved (OPE-426); full ∀n open** | partition theory | OPE-25 recommended; Director approved; STATEMENT pinned 2026-08-04 (distinct ≡1,2 mod 3 vs parts ≡±1 mod 6). **OPE-26** Level A+B. **OPE-424** closed as partial ladder: finite certs n≤24 computable / n≤12 Finset + bridge, zero sorry (PR #27); Adversarial approval partial-only in OPE-426. Finite-certificate scope CLOSED — full-statement continuation tracked as new candidate `schur-partition-full` (OPE-430). |
| `frobenius-coin-problem` | shortlisted (process-fuel only) / done (OPE-22 complete) | number theory | **SUPERSEDED as gap prime** — already in Mathlib. OPE-22 = compute cert + Lean practice completed (no contribution claim). |
| `derangement-formula` | candidate (demoted) | enum. combinatorics | ALREADY in Mathlib (`numDerangements` + sum/recurrence/asymp). Dossier gap claim false. Lean-practice only. |
| `catalan-recurrence` | candidate (demoted) | enum. combinatorics | ALREADY in Mathlib (`catalan`, recurrence, centralBinom closed form). Lean-practice only. |
| `bertrand-postulate-computational` | candidate (demoted) | computational NT | General theorem already in Mathlib; certificate-only value, low contribution. |

Placeholders: `demo-collatz-bound-toy` (demo only). **Seed placeholders `oeis-finite-check-candidate` and
`mathlib-gap-candidate` REPLACED by Scout 2026-08-07** with two novelty-pre-screened, finitary, decidable,
Mathlib-gap candidates: **`ramsey-r33`** (finite graph Ramsey R(3,3)=6 / R(4,4)=18) and **`schur-number`**
(Schur S(2)/S(3)). Both `expected: known-classical` → **formalize-only** (genuine Mathlib contribution; do NOT
re-fund as novel). Dossiers + feasibility under `catalog/problems/<id>/` and `problems/<id>/`.
`erdos-woods` correct-formalization (k=16,a=2184) **done OPE-391** (Lean witness; minimality still literature-only).
Previous Scout keep-fresh: **`van-der-waerden-w23`** — finitary Van der Waerden W(2,3)=9, explicit Mathlib TODO
(HalesJewett.lean L50-53), `formalize-only` (overall 5.0).

**OPE-43 update (2026-08-08):** `ramsey-r33` (PRIME, OPE-44), `van-der-waerden-w23` (OPE-45), and
`schur-number` (OPE-46) are now **shortlisted / Director-approved** — catalog + ledger updated, attacks
assigned to Attack Lead in wake-order chain.

**OPE-430 update (2026-08-25, Scout): fresh formalize-only shortlist after Schur partition partial close.**

The OPE-423 shortlist is consumed. Its recommended prime `schur-partition` (full statement) was
attacked in OPE-424 and closed as a **partial ladder** (finite certificates n≤24 computable /
n≤12 Finset + bridge; zero sorry) with Adversarial Reviewer approval in OPE-426; full ∀n A(n)=B(n)
remains OPEN and the finite-certificate scope is closed — do not re-prime it. The two OPE-423 bench
candidates are not fundable as-is: Ramsey-for-pairs compactness has low marginal contribution over
the closed ramsey-r33/r35 infra, and `bertrand-postulate-computational`'s theorem already exists in
Mathlib.

Fresh shortlist (≤3, known-classical / formalize-only, no novelty claims):

1. **`erdos-szekeres-monotone` — CLOSED OPE-433 (`formalized`).** Was RECOMMENDED PRIME (91).
   Finite weak Erdős–Szekeres landed zero-sorry in `ProofLab/ErdosSzekeres.lean`
   (`erdosSzekeres_monotone`); STATEMENT weak-mono pin held. Do not re-prime.
2. **`schur-partition-full` (78).** Continuation of schur-partition to the full ∀n identity,
   scoped as a Glaisher-style explicit bijection between distinct-parts ≡1,2-mod-3 and parts
   ≡±1-mod-6 families at fixed n, lifted to the universal statement. Highest infra-build value:
   Mathlib has `Nat.Partition`/`odds`/`distincts` but no Euler bijection and no partition
   generating-function infrastructure at all (no PowerSeries usage under `Combinatorics/`,
   no pentagonal-number theorem). Also highest budget risk (Multiset-bijection proofs are verbose);
   cap at two levels. Reuse STATEMENT pin 2026-08-04 verbatim — swapped-pairing landmine fails at
   n=2. Dossier: `catalog/problems/schur-partition-full/DOSSIER.json`.
3. *(bench)* **`van-der-waerden-w24` (79):** W(2,4)=35 via direct carry-over of closed
   `ProofLab/VanDerWaerden.lean` vocabulary to 4-term APs over `Fin 34`/`Fin 35`. Lower bound =
   certified 34-colouring witness (Ramsey-wave pattern: offline search, decidable Lean check).
   Upper bound is the budget sink: the literature value rests on computer assistance (Chvátal 1979),
   so `native_decide` cannot scale to 2^35 colourings — hand case-analysis transcription or
   certificate import required; timebox and fall back to a partial ladder if it explodes.
   Dossier: `catalog/problems/van-der-waerden-w24/DOSSIER.json`.

Negative control recorded per OPE-25 discipline: `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` exists upstream (Turán's theorem proved), so Turán
is never citable as a gap; frobenius/derangement/catalan demotions reconfirmed by the same grep.
Considered and rejected: `ramsey-r46` R(4,6)=41 (no hand upper-bound proof, no certified witness in
repo).

## Active sprint (from OPE-21)

| Bet | Issue | Owner role | Intent |
|-----|-------|------------|--------|
| `frobenius-coin-problem` | **OPE-22** (child of OPE-21) | Attack Lead | Process-fuel only (OPE-25): Level A/B practice; **no claim**. Close when Attack Lead finishes PR + residual risks; optional Reviewer only if someone proposes claim language (they should not). |
| Scout shortlist / ratify | **OPE-25** (child of OPE-21) | Problem Scout | **DONE** — Mathlib-gap audit; frobenius superseded as gap prime; schur recommended. |
| `schur-partition` | **OPE-26** (child of OPE-21; blockedBy OPE-22 wake-order) | Attack Lead | **Approved prime.** Queue `todo`; wake **after OPE-22** completes (one-specialist discipline) unless board raises concurrency. |
| OPE-21 control | **OPE-21** | Research Director | Approve shortlist, pin STATEMENT, open Schur attack, keep ledger — then **done**. |

**OPE-390 update (2026-08-24, Scout):** fresh post-Ramsey shortlist produced on branch
`scout/ope-390-next-shortlist` (PR pending). Gaps re-grepped against pinned Mathlib v4.10.0:
still no Ramsey theorem and no happy-ending/Erdős–Szekeres content anywhere under `Mathlib/`.
**Mid-flight development:** OPE-391 (Formalist) closed `erdos-woods` (k=16, a=2184) with a
zero-sorry Lean witness while this shortlist was being prepared; Scout independently re-verified
the gate (`lake env lean ProofLab/ErdosWoodsCorrect.lean` EXIT=0; no real `sorry`). It therefore
drops OUT of the shortlist as an attack candidate. Remaining shortlist (≤3, formalize-only,
known-classical, no claims):
1. **`ramsey-r35` R(3,5)=14 — RECOMMENDED PRIME (86) → CLOSED OPE-393.** Attack Lead formalized zero-sorry `ramsey35_eq_14` (circulant C13 lower + `R(2,5)+R(3,4)` upper). formalize-only, no claim. PR pending board merge.
2. **`happy-ending-es3` ES(3)=5** (78). Highest infra risk (orientation/order-type glue is new);
   ES(4)=9 stretch only.
3. *(bench)* `schur-partition` full statement (parts ≡ ±1 mod 6) remains a fallback gap if the
   Director prefers number-theory continuity over graph-theory carry-over.

**OPE-423 update (2026-08-25, Scout): fresh post-ES(3)=5 formalize-only shortlist.**
The OPE-390 shortlist is fully consumed: `ramsey-r35` R(3,5)=14 CLOSED (OPE-393, PR #22
merged) and `happy-ending-es3` ES(3)=5 CLOSED (OPE-403/OPE-410, PRs #23/#24/#25 merged).
Catalog rows flipped to `formalized` (see `catalog/problems.json`). Fresh shortlist
(≤3, formalize-only / known-classical only, no novelty claims):

1. **`schur-partition` FULL statement — RECOMMENDED PRIME.** Parts congruent ±1 mod 6
   (repetitions allowed) = distinct parts ≡ 1,2 mod 3. STATEMENT already pinned 2026-08-04
   (`problems/schur-partition/STATEMENT.md`) including the swapped-pairing landmine note;
   literature risk therefore LOW vs fresh pins. Genuine Mathlib gap re-grepped this run:
   no Schur-partition / partition-congruence content under `Mathlib/Combinatorics/Young/`
   or elsewhere in the v4.10.0 snapshot. Natural carry-over: OPE-26 Level A cert (N≤1000,
   DP + brute force agree) + small-n Lean already exist; the full statement is the
   generating-function identity remaining to be formalized.
2. **`ramsey-r46` R(4,6)=18? — NO; excluded.** R(4,6)=41 is a different beast (no hand proof,
   no certified witness in repo); recorded here only to document it was considered and rejected.
2'. **Mathlib-gap candidate: finitary infinite Ramsey for pairs on `Fin`-indexed graphs**
    (`SimpleGraph` compactness flavour). Gap confirmed (only HalesJewett/Hindman mention Ramsey);
    but infra overlap with closed ramsey-r33/r35 makes marginal contribution low — bench only.
3. *(bench)* `bertrand-postulate-computational`: general theorem already in Mathlib; certificate-only,
   low value — unchanged from prior demotion.

Recommended prime: **schur-partition full statement**. Needs a Director approval + attack issue;
STATEMENT pin already exists (2026-08-04), so no re-pin needed unless Director orders one.

## Active sprint (from OPE-402 — post-Ramsey formalize-only wave)

**OPE-402 (Director, 2026-08-24): ratified the OPE-390 shortlist (PR #21 merged).**
Wave order after R(3,5)=14 closed (OPE-393, PR #22 merged):

| Order | Bet | Role | Disposition |
|-------|-----|------|-------------|
| **PRIME** | `happy-ending-es3` (ES(3)=5, score 78) | Attack Lead | Director-approved. STATEMENT pinned `problems/happy-ending-es3/STATEMENT.md` (distinct + general position explicit; convex-position pin; ES(4)=9 out of scope except labeled stretch). Formalize-only, no claim. Highest infra risk: orientation/order-type Mathlib plumbing is new work and itself a genuine contribution. |
| BENCH | `schur-partition` full statement (parts ≡ ±1 mod 6) | Attack Lead | Fallback if Director prefers number-theory continuity over graph/geometry carry-over. STATEMENT already pinned 2026-08-04. |
| CLOSED | `ramsey-r35` R(3,5)=14 | Attack Lead | DONE OPE-393. Zero-sorry `ramsey35_eq_14`; PR #22 merged. |

Wake discipline: one specialist at a time; prime attack fires first.

## Active sprint (from OPE-390 / OPE-393)

| Bet | Issue | Owner role | Intent |
|-----|-------|------------|--------|
| `ramsey-r35` (R(3,5)=14) | **OPE-393** (Scout prime OPE-390) | Attack Lead | **DONE formalized.** Zero-sorry Lean `ramsey35_eq_14`; `lake build ProofLab` green. formalize-only, no claim. |

**OPE-458 update (2026-08-25, Scout): fresh formalize-only shortlist after the OPE-430 wave closes.**

Consumption check against the OPE-430 shortlist (all three slots now spent): `erdos-szekeres-monotone`
closed green (OPE-433/437/438, PR #29); `schur-partition-full` partial via the Glaisher ladder
(OPE-440/445/447 + reviews 441/448; finite certificates only — do NOT re-prime that scope);
`van-der-waerden-w24` partial ladder W(2,4)>34 (OPE-455/456, PR #33; upper ≤35 still open and
computer-assisted in literature). NOTE for Director: main is behind — PRs #28–#33 are all still OPEN;
merge or retire them before assigning new attacks.

Fresh shortlist (≤3, known-classical / formalize-only, no novelty claims):

1. **`ramsey-multicolor-r333` R(3,3,3)=17 — RECOMMENDED PRIME (84).** Multicolour Ramsey: every
   3-colouring of the edges of K₁₇ has a monochromatic triangle; certificate on K₁₆ shows sharpness.
   Rationale: genuinely NEW proof layer over the closed ramsey-r33/r35 infrastructure — multicolour
   edge colourings replace graph/complement pairs, but the upper bound reuses exactly the same two
   moves at larger scale: (a) if some vertex has ≥6 same-coloured edges, pull back
   `ramsey33_on_finset`/`ramsey33_clique_inside_finset` into that neighbourhood (already proved in
   `ProofLab/Ramsey.lean` on unmerged ope/393); (b) otherwise every vertex has degree ≤5 in each
   colour ⇒ sum of degrees = 16·5 = 80 is odd, contradicting the handshaking lemma — the same
   parity vocabulary as the OPE-44 R(3,4)≤9 argument. Lower bound: explicit 120-edge certificate
   over Fin 16 from the Greenwood–Gleason F₂⁴ construction (Scout-built and independently verified
   offline this run: zero monochromatic triangles; naive random search FAILS to find one —
   deterministic construction required), checked in Lean by decidable enumeration — the exact
   witness-check pattern of `vdw24_gt_34`. GENUINE GAP re-grepped v4.10.0 this run: `RamseyNumber`,
   `multicolor`, `MColoring` → ZERO hits anywhere under `Mathlib/`; "ramsey" appears only in
   HalesJewett/Hindman prose and RingTheory false positives.
   Definition risk (pin in STATEMENT.md): edge k-colouring as symmetric irreflexive
   `f : Fin n → Fin n → Fin k` vs Sym2 encoding — pin ONE; diagonal default irrelevant to
   off-diagonal extraction; certificate edge order lexicographic (i,j), i<j (same as witness34).
   Canonical source: Greenwood & Gleason, *Combinatorial relations and chromatic graphs*, Canadian
   J. Math. 7 (1955) 1–7. Dossier: `catalog/problems/ramsey-multicolor-r333/DOSSIER.json`
   (+ `witness16_certificate.txt`).
2. **`weak-schur-ws2` WS(2)=8 (81).** Weak Schur number: largest n admitting a 2-colouring of
   {1..n} with NO monochromatic x+y=z where x,y,z are DISTINCT. Eligibility per commission rule:
   genuinely new proof layer — the distinctness requirement changes the forcing structure entirely,
   WS(2)=8 vs S(2)=4, so nothing from the closed S(2)/S(3) certificates transfers; NOT a re-warm of
   the schur-partition finite-certificate scope either. Scout probe this run: exhaustive scan
   confirms [1..8] colourable, [1..9] not ⇒ boundary pre-verified before recommendation. Lean shape
   mirrors `ProofLab/SchurNumber.lean` (class predicates + least-forcing witness + native_decide at
   trivially small scale). Gap grep clean v4.10.0: zero additive-Schur content of any kind.
   Definition risk: pin x≠y suffices (z=x+y automatically distinct since x,y≥1); domain {1..n}
   vs Fin-n offset landmine. Canonical source: Abbott–Wang / Exoo weak Schur survey definition.
   Dossier: `catalog/problems/weak-schur-ws2/DOSSIER.json`.
3. *(bench)* **`schur-partition-full-glaisher` (76):** forall-n lift of the closed finite-certificate
   identity via an explicit Glaisher bijection (card equality by `Finset.card_congr`). Eligible only
   as a new proof layer (universal bijection vs finite certs). Highest infra value in the pool (no
   partition generating-function infra upstream) but highest budget sink (verbose Multiset proofs) —
   cap at two levels. HARD DEPENDENCY: Levels A/B/C live on UNMERGED branches ope/440/445/447;
   merge or retire them first. Reuse STATEMENT pin 2026-08-04 verbatim (swapped-pairing landmine
   fails at n=2). Dossier: `catalog/problems/schur-partition-full/DOSSIER.json`.

Negative control re-recorded per OPE-25 discipline: `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` exists upstream ⇒ never citable as gap (reconfirmed
this run). Considered and rejected: W(2,4)≤35 hand case-analysis (no concrete human-scale case-split
strategy nameable — stays bench/skip per commission guidance); ramsey-r46 (no witness, no hand
upper bound); happy-ending ES(4)/ES(5) lifts (ES(3)=5 already closed in the OPE-402 wave; higher ES
values have no hand-scale proof in scope).

**OPE-533 update (2026-08-27, Scout, support OPE-475):** catalog audit + fresh ≤2 shortlist.
OPE-458 shortlist is fully consumed or still benched — do not re-prime those rows.

Consumption (live `gh pr list` this run; main still at merge of PR #21, 15 PRs open #22–#36):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `ramsey-multicolor-r333` | OPE-461 DONE; PR #36 OPEN / MERGEABLE / gate APPROVE | yes |
| `weak-schur-ws2` | OPE-462 DONE; PR #35 OPEN / MERGEABLE / gate APPROVE | yes |
| `schur-partition-full-glaisher` | OPE-463 still **benched** on unmerged PRs #30→#31→#32 | yes until unbench |
| `ramsey-r35` | OPE-393 PR #22 OPEN | yes |
| `happy-ending-es3` | OPE-403/410 PRs #24/#25 OPEN | yes |

Catalog hygiene: leftover seeds `mathlib-gap-candidate` / `oeis-finite-check-candidate` marked
`archived` (README claimed replacement 2026-08-07; rows were still `needs-scout`).

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Already in Mathlib (never cite as
gap):** Cauchy–Davenport, Erdős–Ginzburg–Ziv, Sperner/LYM, Hall marriage, Wilson, Lucas,
Zeckendorf, Beatty/Rayleigh, Pythagorean triples classification, Turán, non-uniform
`Intersecting.card_le` (2^{n−1} only). **Gaps confirmed zero-hit:** EKR (k-uniform), friendship
theorem, Dilworth, combinatorial Nullstellensatz.

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`erdos-ko-rado` — RECOMMENDED PRIME (87).** Why-not-classical: EKR 1961 is settled; star
   extremal `C(n-1,k-1)` for intersecting k-subsets when `n≥2k`. Why still a bet: Mathlib has
   only the *non-uniform* intersecting bound; Katona cycle is a new uniformity layer, not a
   re-warm of Sperner/Ramsey/Schur. STATEMENT pin: `catalog/problems/erdos-ko-rado/STATEMENT.md`.
2. **`friendship-windmill` (84).** Why-not-classical: Erdős–Rényi–Sós 1966; finite graphs only
   (infinite counterexamples exist). Why still a bet: `commonNeighbors` + `IsSRGWith` exist,
   theorem does not; common-neighbour layer ≠ clique-Ramsey. STATEMENT pin:
   `catalog/problems/friendship-windmill/STATEMENT.md`.

Considered, not shortlisted (slot cap 2): finite Dilworth (Hall exists; comparability matching is
a larger budget than EKR/Friendship); combinatorial Nullstellensatz (algebra-heavy; Hilbert NS
is a different theorem and already upstream); Dirac (Hamiltonian *defs* exist, theorem does not);
W(2,4)≤35 / ES(4) / ramsey-r46 unchanged rejects; Glaisher forall-n stays benched.

Director assigns after approval. Scout opened **no attack issues**. Merge backlog (#34 then
#36/#35, plus #22–#33) is still a board problem; this shortlist does not require those merges
to *start* (new modules), but stacking more unmerged Lean still deepens the PR pile.

**OPE-553 update (2026-08-28, Scout, support OPE-552):** catalog audit + fresh ≤2 shortlist.
OPE-533 shortlist is **fully consumed on merged main**. Zero open PRs at scout start
(`origin/main` = merge of PR #41). Director does not invent primes.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `erdos-ko-rado` | OPE-534 PR #39 MERGED; OPE-541 PR #41 MERGED; `erdos_ko_rado` on main | yes |
| `friendship-windmill` | OPE-535 PR #40 MERGED | yes |
| `schur-partition-full-glaisher` / OPE-463 | unbench criteria met **and** `theorem schur_partition` already on main | yes (consumed, not a new prime) |
| ramsey-r33 / r35 / r333; WS(2); S(2)/S(3); W(2,3); ES monotone; ES(3)=5; EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage, Wilson, Lucas, Zeckendorf, Beatty, Pythagorean triples,
Turán, non-uniform `Intersecting.card_le`, Hilbert Nullstellensatz
(`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form), Hamiltonian
*definitions* (not Dirac), `Nat.Partition.odds`/`distincts` *definitions* (not Euler).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`euler-odd-distinct` — RECOMMENDED PRIME (87).** Why-not-classical: Euler 1748
   odd-parts = distinct-parts is settled. Why still a bet: Mathlib
   `Combinatorics/Enumerative/Partition.lean` defines `odds`/`distincts` and the module
   docstring says the API exists to show Euler's theorem, but **no** card equality lives
   under `Mathlib/**` (`partition_theorem`/`Theorems100` → ZERO in Mathlib). Archive
   `Wiedijk100Theorems/Partition.lean` already has `Theorems100.partition_theorem` via
   **generating functions** — disclose; ProofLab value is a **Glaisher bijection**
   (`Finset.card_bij'`), a new proof layer vs Archive PowerSeries and a **different
   identity** vs consumed `theorem schur_partition`. STATEMENT pin:
   `catalog/problems/euler-odd-distinct/STATEMENT.md`.
2. **`dirac-hamiltonian` (84).** Why-not-classical: Dirac 1952 `δ ≥ n/2 ⇒` Hamiltonian
   (n≥3) is settled. Why still a bet: `SimpleGraph.IsHamiltonian` exists; no degree
   sufficient-condition (graph `dirac` hits are analysis measures). New proof layer vs
   Friendship/EKR/Ramsey. STATEMENT pin: `catalog/problems/dirac-hamiltonian/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-533 leftovers):

- **Dilworth:** gap still holds (ZERO hits Mathlib+Archive). Hall + antichains exist;
  `Matching.lean` still has no König/vertex-cover. Comparability-matching construction
  remains a larger first bite than Euler (defs waiting) or Dirac (defs waiting). Bench.
- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO
  combinatorial hits). Algebra-heavy `MvPolynomial` surface unused in ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-574 update (2026-08-28, Scout, support OPE-573):** catalog audit + fresh ≤2 shortlist.
OPE-553 shortlist **plus** OPE-567 Dirac Level B continuation is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #45, `3723b07`). Director does not invent primes.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `euler-odd-distinct` | OPE-558 Formalist; Reviewer APPROVE; PR **#43 MERGED**. `euler_odd_eq_distinct` on main | yes |
| `dirac-hamiltonian` | OPE-559 Level A PR **#44 MERGED**; OPE-568 Level B PR **#45 MERGED**. Full v1 `dirac_hamiltonian` on main, zero-sorry | yes (not Level A/B; Ore is not a leftover re-prime) |
| `erdos-ko-rado` / friendship-windmill / schur_partition / schur-partition-full-glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage (`HallMarriageTheorem`), Wilson, Lucas, Zeckendorf, Beatty,
Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert Nullstellensatz
(`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form), Chevalley–Warning,
Burnside's lemma (group actions), Lagrange four squares, quadratic reciprocity, Möbius
inversion, Hamiltonian *definitions* (Dirac theorem now in ProofLab, not Mathlib),
`Walk.IsEulerian` + necessary `card_odd_degree` (existence TODO remains),
`Subgraph.IsMatching` (no König / no vertex cover).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`eulerian-hierholzer` — RECOMMENDED PRIME (88).** Why-not-classical: Euler 1736 /
   Hierholzer 1873 is settled. Why still a bet: `Trails.lean` has `IsEulerian` and the
   **necessary** 0-or-2 odd-degree theorem; the module TODO is the **existence**
   direction. New proof layer vs closed Dirac (edges-once trail ≠ vertices-once cycle).
   Archive Königsberg is a negative custom-graph instance, not this theorem.
   STATEMENT pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md`.
2. **`konig-bipartite` (84).** Why-not-classical: Kőnig 1931 `ν=τ` for bipartite graphs
   is settled. Why still a bet: Matching defs exist; no vertex-cover predicate and no
   min-max. Hall SDR is a different upstream theorem. Atomic matching primitive —
   Dilworth still a gap but is **not** rubber-stamped (needs this layer).
   STATEMENT pin: `catalog/problems/konig-bipartite/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-553 leftovers):

- **Dilworth:** gap still holds (ZERO hits Mathlib+Archive). Hall + antichains exist;
  `Matching.lean` still has no König/vertex-cover. Comparability-matching remains a
  larger first bite than Eulerian (defs+TODO waiting) or König (the primitive). Bench
  until König lands.
- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO
  combinatorial hits). Chevalley–Warning already upstream, so the finite-field
  corollary motivation is weaker. Algebra-heavy `MvPolynomial` unused in ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore
  hits are localization, not Ore's theorem). Proof shape is a re-warm of the just-closed
  Dirac longest-path argument. **Not slotted** — not a Dirac leftover; slot cap used
  by fresher bets with explicit TODOs / missing predicates.
- **Cayley `n^{n-2}`:** gap holds (IsTree exists; no labelled-tree count). Encoding
  landmine: `SimpleGraph` is a large type, so the claim must go through edge-Finsets /
  Prüfer codes, not `Fintype.card {G // G.IsTree}`. Bench (definition risk).
- **Brooks:** gap holds (Colorable / chromaticNumber exist; no greedy `χ ≤ Δ+1` even).
  Longer critical-graph proof; slot cap used.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-591 update (2026-08-28, Scout, support OPE-590):** catalog audit + fresh ≤2 shortlist.
OPE-574 shortlist **plus** OPE-578 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #48, `9198aa5`). Director does not invent primes.
This is **not** a Director-invented Eulerian-B / König-B continuation: STATEMENT v1 residuals were independently re-scored as new proof layers.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `eulerian-hierholzer` Level A | OPE-579 Formalist; Adversarial OPE-582; PR **#47 MERGED**. Honest partial `eulerian_k1` / `eulerian_cycle` / `eulerian_k2` on main. STATEMENT v1 ∀G **not** closed | yes (Level A). Level B independently re-scored below |
| `konig-bipartite` Level A | OPE-580 Formalist; Adversarial OPE-584; rebase OPE-587; PR **#48 MERGED** (`9198aa5`). Honest partial `IsVertexCover` / `ν≤τ` / `K_{m,n}` / `K_3` landmine on main. STATEMENT v1 `Colorable 2 → ν=τ` **not** closed | yes (Level A). Level B independently re-scored below |
| `euler-odd-distinct` | PR **#43 MERGED** | yes |
| `dirac-hamiltonian` Level A/B | PRs **#44** / **#45 MERGED**. Ore is not a leftover re-prime | yes |
| Scout shortlist PR **#46** | MERGED | yes |
| `erdos-ko-rado` / friendship-windmill / schur_partition / schur-partition-full-glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas,
Zeckendorf, Beatty, Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert
Nullstellensatz (`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form),
Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange
four squares, quadratic reciprocity, Möbius inversion, Hamiltonian *definitions* (Dirac theorem
now in ProofLab, not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence TODO
L26–29 remains), `Subgraph.IsMatching` (no König / no vertex cover — ZERO
`vertexCover`/`matchingNumber` hits), cardinal König (`SetTheory.Cardinal`, unrelated).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`konig-bipartite` Level B — RECOMMENDED PRIME (87).** Independent re-score, **not** an
   OPE-574 leftover rubber-stamp. Why-not-classical: Kőnig 1931 `ν=τ` for bipartite graphs is
   settled. Why still a bet / why a new layer: Level A closed predicates + easy `ν≤τ` + special
   cases; STATEMENT v1 `Colorable 2 → matchingNumber = vertexCoverNumber` is the namesake min-max
   and still open. Mathlib v4.10.0 still has ZERO vertex-cover / ZERO König-graph theorem (Hall
   SDR is a different upstream statement). Proof shape: alternating paths from unsaturated
   vertices, or Hall reduction on neighbourhoods — both human-scale; Hall already in
   `Combinatorics/Hall/`. Formalizability rose vs original 84 because `IsVertexCover` /
   `matchingNumber` / `vertexCoverNumber` now live in `ProofLab/Konig.lean`. Dilworth remains a
   genuine gap (ZERO Mathlib+Archive) and **still should not skip this min-max**. STATEMENT pin:
   `catalog/problems/konig-bipartite/STATEMENT.md`.
2. **`eulerian-hierholzer` Level B (83).** Independent re-score, **not** an OPE-574 leftover
   rubber-stamp. Why-not-classical: Euler 1736 / Hierholzer 1873 is settled. Why still a bet /
   why a new layer: Level A closed `K_1` / `C_n` / `K_2`; STATEMENT v1 ∀G existence is circuit-
   merging / induction on `edgeSet.card`. Mathlib `Trails.lean` L26–29 existence TODO still
   open. Archive Königsberg is a negative custom-graph instance, not this theorem. Score dropped
   vs original 88 because Walk-induction budget is the known sink (Dirac took two levels) and
   special cases already landed. STATEMENT pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-574 leftovers):

- **Dilworth:** gap still holds (ZERO hits Mathlib+Archive). Hall + antichains exist;
  `Matching.lean` still has no König min-max in Mathlib (ProofLab has the easy inequality only).
  Comparability-matching remains a larger first bite **and the König `Colorable 2 → ν=τ` layer
  is still blocking**. Not slotted.
- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  hits). Chevalley–Warning already upstream, so the finite-field corollary motivation is weaker.
  Algebra-heavy `MvPolynomial` unused in ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore hits in
  Mathlib are localization, not Ore's theorem). Proof shape is a re-warm of closed Dirac
  longest-path. **Not slotted.**
- **Cayley `n^{n-2}`:** gap holds (`IsTree` exists, including `card_edgeFinset`; no labelled-tree
  count / no Prüfer). Encoding landmine: `SimpleGraph` is a large type, so the claim must go
  through edge-Finsets / Prüfer codes, not `Fintype.card {G // G.IsTree}`. Bench (definition risk).
- **Brooks:** gap holds (`Colorable` / `chromaticNumber` exist; ZERO Brooks; Coloring.lean TODO
  is gather-material / trees / planar / chromatic polynomials, not Brooks). No greedy `χ ≤ Δ+1`
  either. Longer critical-graph proof; slot cap used by König B + Eulerian B (better carry-over).

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-613 update (2026-08-29, Scout, support OPE-612):** catalog audit + fresh ≤2 shortlist.
OPE-591 shortlist **plus** the OPE-595 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #51, `396e2a6`). Director does not invent primes.
This is **not** a Director-invented Eulerian-C / Dilworth / Ore continuation: Dilworth and the Eulerian trail residual were independently re-scored as new proof layers.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `konig-bipartite` Level B | OPE-596 Formalist; Adversarial OPE-599; PR **#50 MERGED** (`684316b`). `konig_bipartite` on main, zero-sorry | yes (Level A **and** Level B) |
| `eulerian-hierholzer` Level B circuit | OPE-597 Formalist; PR **#51 MERGED** (`396e2a6`). Honest partial `eulerian_hierholzer_circuit` + `eulerian_complete_odd` on main. STATEMENT trail clause **not** closed | yes (Level A **and** Level B circuit / complete-odd). Trail independently re-scored below |
| `euler-odd-distinct` | PR **#43 MERGED** | yes |
| `dirac-hamiltonian` Level A/B | PRs **#44** / **#45 MERGED**. Ore is not a leftover re-prime | yes |
| Scout shortlist PRs **#46** / **#49** | MERGED | yes |
| Eulerian Level A PR **#47**; König Level A PR **#48** | MERGED | yes |
| `erdos-ko-rado` / friendship-windmill / schur_partition / schur-partition-full-glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24). Duplicate planning ticket **OPE-605** is not a second Scout commission.

Catalog hygiene this run: Eulerian note stamped **PR #51 MERGED** + honest-partial trail residual (was “PR pending”). König B stamped `formalized` / PR #50 / do-not-reprime A/B.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas,
Zeckendorf, Beatty, Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert
Nullstellensatz (`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form),
Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange
four squares, quadratic reciprocity, Möbius inversion, Hamiltonian *definitions* (Dirac theorem
now in ProofLab, not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence TODO
L26–29 remains for the 2-odd trail), `Subgraph.IsMatching` (no König / no vertex cover in
Mathlib — ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated), `IsChain` /
`IsAntichain` *definitions* (not Dilworth), `Colorable` / `chromaticNumber` / `maxDegree`
(no Brooks, no greedy `χ ≤ Δ+1`).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`dilworth-poset` — RECOMMENDED PRIME (84).** Independent re-score, **not** an OPE-591
   leftover rubber-stamp. Why-not-classical: Dilworth 1950 min chain-partition = max antichain
   (width) is settled. Why still a bet / why a new layer: König `Colorable 2 → ν=τ` was the
   blocking primitive on OPE-533/553/574/591; that layer is **closed** (PR #50). Gap still
   holds (word-regexp `dilworth` → ZERO Mathlib+Archive). Proof shape: Fulkerson split graph
   on `α ⊕ α` with `Adj (inl a) (inr b) ↔ a < b` (strict), then reuse `konig_bipartite`.
   Mathlib already has `IsChain` / `IsAntichain`. STATEMENT pin:
   `catalog/problems/dilworth-poset/STATEMENT.md`.
2. **`eulerian-hierholzer` trail residual (81).** Independent re-score, **not** an OPE-591
   leftover rubber-stamp. Why-not-classical: Euler/Hierholzer is settled. Why still a bet /
   why a new layer: Level B closed the **circuit** clause + complete-odd family; STATEMENT
   `card oddDeg = 2` ∀G is open. Mathlib Trails.lean L26–29 existence TODO still open.
   OPE-597 dummy-edge / Walk-splice did **not** land (SimpleGraph cannot add an already-present
   edge). Named encoding that addresses the failure: longest trail **starting at an odd-degree
   vertex**; **forbid dummy-edge**. Do **not** re-prime circuit / complete-odd / Level A.
   STATEMENT pin: `catalog/problems/eulerian-hierholzer/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-591 leftovers):

- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  ident hits). Chevalley–Warning already upstream. Algebra-heavy `MvPolynomial` unused in
  ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore hits in
  Mathlib are localization, not Ore's theorem). Proof shape is a re-warm of closed Dirac
  longest-path. **Not slotted.**
- **Cayley `n^{n-2}`:** gap holds (`IsTree` exists; no labelled-tree count / no Prüfer).
  Encoding landmine: `SimpleGraph` is a large type, so the claim must go through edge-Finsets /
  Prüfer codes, not `Fintype.card {G // G.IsTree}`. Bench (definition risk).
- **Brooks / greedy `χ ≤ Δ+1`:** gap holds (`Colorable` / `chromaticNumber` / `maxDegree` exist;
  ZERO Brooks; ZERO greedy). Coloring.lean TODO is gather-material / trees / planar / chromatic
  polynomials, not Brooks. Greedy would score well on budget; slot cap used by Dilworth
  (unblocked König corollary) + Eulerian trail (named Mathlib TODO residual). Not slotted.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-640 update (2026-08-29, Scout, support OPE-639):** catalog audit + fresh ≤2 shortlist.
OPE-613 shortlist **plus** the OPE-618/OPE-632 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #55, `6c32a467`). Director does not invent primes.
This is **not** a Director-invented Dilworth-C / Eulerian-C / Ore / König continuation: greedy Δ+1 and Brooks were independently re-scored as new proof layers.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `dilworth-poset` Level A+B | OPE-619 PR **#53 MERGED**; OPE-626 PR **#54 MERGED** (`622d076`); OPE-628 APPROVE. `theorem dilworth` on main | yes (A **and** B). Residual EMPTY. Do not invent Level C / Mirsky / Greene |
| `eulerian-hierholzer` trail | OPE-633 Formalist; OPE-634 APPROVE; PRG OPE-637; PR **#55 MERGED** (`6c32a467`). `eulerian_hierholzer_trail` on main | yes (Level A, circuit/complete-odd, **and** this trail). Do not re-prime |
| `konig-bipartite` Level A+B | PRs **#48** / **#50 MERGED** | yes |
| `eulerian-hierholzer` Level A / circuit | PRs **#47** / **#51 MERGED** | yes |
| Scout shortlist PRs **#46** / **#49** / **#52** | MERGED | yes |
| `euler-odd-distinct` / Dirac A+B / EKR / friendship / schur_partition / Glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Catalog hygiene this run: Eulerian `problems.json` stamped **PR #55 MERGED** + `formalized` (was PR #51 / `in_review`). Dilworth stamped **PR #54 MERGED** + `formalized` (was awaiting Reviewer). Ledger last-updated no longer says “PR pending Reviewer”.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas,
Zeckendorf, Beatty, Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert
Nullstellensatz (`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form),
Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange
four squares, quadratic reciprocity, Möbius inversion, Hamiltonian *definitions* (Dirac theorem
now in ProofLab, not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence TODO
L26–29 remains upstream; ProofLab filled circuit + 2-odd trail), `Subgraph.IsMatching` (no König
/ no vertex cover in Mathlib — ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated),
`IsChain` / `IsAntichain` *definitions* (Dilworth now in ProofLab), `Colorable` /
`chromaticNumber` / `maxDegree` / `chromaticNumber_top` (no Brooks in Mathlib; greedy `χ ≤ Δ+1` now in ProofLab OPE-645, not upstream).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`greedy-chromatic` — RECOMMENDED PRIME (89). CONSUMED by OPE-645 Formalist** (Level A+B zero-sorry `theorem greedy_colorable`; awaiting Reviewer / PRG). Independent re-score, **not** an OPE-613
   leftover rubber-stamp. Why-not-classical: every finite simple graph is (Δ+1)-colourable
   (Diestel corollary / greedy algorithm) is settled. Why still a bet / why a new layer:
   Dilworth + Eulerian trail (the previous slot-cap occupiers) are **closed**. Mathlib has
   `Colorable` / `chromaticNumber` / `maxDegree`; ZERO `Colorable (maxDegree+1)`, ZERO
   `chromaticNumber_le_maxDegree`, ZERO Brooks. Proof shape: induction on `card V`, colour
   `G−v`, extend at `v` (≤Δ neighbours leave one colour in `Fin (Δ+1)`). Human-scale; defs
   waiting. Brooks is a *different* named theorem (shortlist #2) — do **not** prove Brooks
   in this id. STATEMENT pin: `catalog/problems/greedy-chromatic/STATEMENT.md`.
2. **`brooks-coloring` (78). OPE-658 Formalist Level B Δ≤2 family landed** (zero-sorry `brooks_colorable_of_maxDegree_le_two`; namesake residual on Δ-regular Δ≥3). Independent re-score, **not** an OPE-613 leftover rubber-stamp.
   Why-not-classical: Brooks 1941 `χ ≤ Δ` except complete graphs and odd cycles is settled.
   Why still a bet / why a new layer: greedy is the cheap lemma; Brooks is the namesake with
   exceptions. Score 78 (not 89) because critical-graph / Kempe is the known sink and Mathlib
   has **no** `cycleGraph` (odd-cycle pin: 2-regular connected + odd `card V`). Do **not**
   assign before greedy unless Director swaps. Do **not** label greedy as Brooks.
   STATEMENT pin: `catalog/problems/brooks-coloring/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-613 leftovers):

- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  ident hits). Chevalley–Warning already upstream. Algebra-heavy `MvPolynomial` unused in
  ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore hits in
  Mathlib are localization, not Ore's theorem). Proof shape is a re-warm of closed Dirac
  longest-path. **Not slotted.**
- **Cayley `n^{n-2}`:** gap holds (`IsTree` exists, including `card_edgeFinset`; no labelled-tree
  count / no Prüfer). Encoding landmine remains: `SimpleGraph` is a large type, so the claim
  must go through edge-Finsets / Prüfer codes, not `Fintype.card {G // G.IsTree}`. Group
  Cayley and Cayley–Hamilton are different already-upstream theorems. Bench (definition risk).
- **Tutte's theorem:** explicit Matching.lean TODO, ZERO theorem. Classical but a substantially
  larger first bite than greedy (Tutte sets / barriers). Bench.
- **Menger:** ZERO Mathlib+Archive. Classical min-cut / disjoint-paths; needs new cut predicates.
  Slot cap used by colouring defs that already exist. Bench.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-666 update (2026-08-29, Scout, support OPE-665):** catalog audit + fresh ≤2 shortlist.
OPE-640 shortlist **plus** the OPE-644/OPE-650 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #59, `ea69b7b`). Director does not invent primes.
This is **not** a Director-invented Brooks-C / Kempe / Dilworth-C / Eulerian-C / Ore / Vizing continuation: Havel–Hakimi is a fresh id; vertex-Menger is an independent re-score of a leftover whose colouring-slot-cap reason no longer holds.

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `greedy-chromatic` Level A+B | OPE-645 Formalist; PR **#57 MERGED**. `theorem greedy_colorable` on main | yes. Do not expand into Brooks / list-colouring |
| `brooks-coloring` Level A | OPE-651 Formalist; PR **#58 MERGED**. Exceptions `⊤` / odd-cycle `χ=Δ+1`; greedy reused not labelled Brooks | yes (Level A) |
| `brooks-coloring` Level B | OPE-658 Formalist; PRG OPE-663; PR **#59 MERGED** (`ea69b7b`). `brooks_colorable_of_maxDegree_le_two` on main. Namesake residual Δ-regular Δ≥3 **not** sorry-ed | yes (Level B). Do **not** invent namesake Kempe / Level C as a leftover. Status stays `informal` |
| `dilworth-poset` Level A+B | PRs **#53** / **#54 MERGED**. Residual EMPTY | yes. Do not invent Level C / Mirsky / Greene |
| `eulerian-hierholzer` A / circuit / trail | PRs **#47** / **#51** / **#55 MERGED** | yes. Do not invent Eulerian-C |
| `konig-bipartite` Level A+B | PRs **#48** / **#50 MERGED** | yes |
| Scout shortlist PRs **#46** / **#49** / **#52** / **#56** | MERGED | yes |
| `euler-odd-distinct` / Dirac A+B / EKR / friendship / schur_partition / Glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Catalog hygiene this run: Brooks `problems.json` stamped **PR #59 MERGED** + honest `informal` (namesake residual). Greedy already `formalized` / #57. Not a new proof layer.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport,
EGZ, Sperner/LYM, Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas,
Zeckendorf, Beatty, Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert
Nullstellensatz (`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form),
Chevalley–Warning (`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange
four squares, quadratic reciprocity, Möbius inversion, Hamiltonian *definitions* (Dirac theorem
now in ProofLab, not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence TODO
L26–29 remains upstream; ProofLab filled circuit + 2-odd trail), `Subgraph.IsMatching` (no König
/ no vertex cover in Mathlib — ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated),
`IsChain` / `IsAntichain` *definitions* (Dilworth now in ProofLab), `Colorable` /
`chromaticNumber` / `maxDegree` / `chromaticNumber_top` (no Brooks in Mathlib; greedy `χ ≤ Δ+1`
and Brooks Δ≤2 family now in ProofLab, not upstream), `degree` / handshaking
(`sum_degrees_eq_twice_card_edges`) — **not** Havel–Hakimi, `Walk` / `Reachable` / `Connected`
— **not** Menger.

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`havel-hakimi` — RECOMMENDED PRIME (86).** Fresh id, **not** an OPE-640 leftover.
   Why-not-classical: Havel 1955 / Hakimi 1962 graphic-sequence iff is settled. Why still a
   bet / why a new layer: greedy + Brooks A/B (the previous slot-cap occupiers) are **closed**.
   Mathlib has `degree` / `neighborFinset` / handshaking; ZERO `IsGraphic`, ZERO `Havel`,
   ZERO `Hakimi`. Proof shape: induction on `n` via the reduction (delete a max-degree vertex
   adjacent to the next `d 0` vertices; reverse to build). Human-scale; defs waiting.
   Even sum is necessary **not** sufficient (`(2,2,0,0)` landmine). Erdős–Gállai / Gale–Ryser /
   Tutte are *different* theorems — do **not** prove them in this id. STATEMENT pin:
   `catalog/problems/havel-hakimi/STATEMENT.md`.
2. **`menger-vertex` (80).** Independent re-score of the OPE-640 considered-not-slotted
   Menger line — **not** a rubber-stamp. Why-not-classical: Menger 1927 min A–B separator =
   max disjoint A–B paths is settled. Why still a bet / why a new layer: last Scout benched
   it because the slot cap was used by colouring defs that already existed; those colouring
   slots are now consumed. Gap still holds (ZERO `Menger` Mathlib+Archive). Named human-scale
   proof: Diestel induction on `|E|`. König `ν=τ` is a *different* min-max (optional engine,
   do not re-prime). Score 80 because separator / A–B-path predicates are new. Do **not**
   assign before `havel-hakimi` unless Director swaps. Do **not** prove edge-Menger /
   max-flow / infinite Erdős–Menger. STATEMENT pin:
   `catalog/problems/menger-vertex/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-640 leftovers):

- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  ident hits). Chevalley–Warning already upstream. Algebra-heavy `MvPolynomial` unused in
  ProofLab. Bench.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore hits in
  Mathlib are localization, not Ore's theorem). Proof shape is a re-warm of closed Dirac
  longest-path. **Not slotted.** Do not invent Ore as a leftover.
- **Cayley `n^{n-2}`:** gap holds (`IsTree` + `card_edgeFinset` exist; `fromEdgeSet` exists;
  ZERO Prüfer / labelled-tree count). Encoding landmine remains: `SimpleGraph` is a large
  type, so the claim must go through edge-Finsets / Prüfer codes, not
  `Fintype.card {G // G.IsTree}`. Group Cayley and Cayley–Hamilton are different
  already-upstream theorems. Bench (definition risk).
- **Tutte's theorem:** explicit Matching.lean TODO, ZERO theorem. Classical but a substantially
  larger first bite than Havel–Hakimi (Tutte sets / barriers). Bench.
- **Namesake Kempe / Brooks Level C / list-colouring Brooks / Vizing / 4CT / Dilworth-C /
  Eulerian-C:** Director declined. Do not invent.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-683 update (2026-08-30, Scout, support OPE-682):** catalog audit + fresh ≤2 shortlist.
OPE-666 shortlist **plus** the OPE-670/OPE-677 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #62, `abf60474`). Director does not invent primes.
This is **not** a Director-invented Dilworth-C / Eulerian-C / Ore / Vizing / 4CT / list-colouring Brooks / namesake Kempe / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser / Tutte / Whitney continuation: Cayley is an independent re-score of a leftover whose *encoding* bench reason no longer holds; Mycielski is a fresh id (χ vs ω, not Brooks χ vs Δ).

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `havel-hakimi` Level A + reverse | OPE-671 Formalist; PR **#61 MERGED** (`9dab9a5`). `isGraphic_of_reduce` on main. Namesake forward switching **not** sorry-ed | yes. Do not expand into Erdős–Gállai / Gale–Ryser / Tutte |
| `menger-vertex` Level A | OPE-678 Formalist; PRG OPE-680; PR **#62 MERGED** (`abf60474`). `p ≤ s` / `A ∩ B` / singleton edge / no-path / `menger_bot` on main. Namesake `s = p` **not** sorry-ed | yes (Level A). Do **not** invent namesake Diestel induction / edge-Menger / max-flow / infinite Erdős–Menger as a leftover. Status stays `informal` |
| `greedy-chromatic` Level A+B | PR **#57 MERGED** | yes. Do not expand into Brooks / list-colouring |
| `brooks-coloring` Level A/B | PRs **#58** / **#59 MERGED**. Namesake residual is a comment (Kempe / Lovász) | yes. Do **not** invent namesake Kempe / Level C / list-colouring Brooks |
| `dilworth-poset` Level A+B | PRs **#53** / **#54 MERGED**. Residual EMPTY | yes. Do not invent Level C / Mirsky / Greene |
| `eulerian-hierholzer` A / circuit / trail | PRs **#47** / **#51** / **#55 MERGED** | yes. Do not invent Eulerian-C |
| `konig-bipartite` Level A+B | PRs **#48** / **#50 MERGED** | yes |
| Scout shortlist PRs **#46** / **#49** / **#52** / **#56** / **#60** | MERGED | yes |
| `euler-odd-distinct` / Dirac A+B / EKR / friendship / schur_partition / Glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Catalog hygiene this run: Menger `problems.json` stamped **PR #62 MERGED** + honest `informal` (namesake residual). Havel stamped **PR #61 MERGED** + honest `informal`. Not a new proof layer.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport
(`Combinatorics/SetFamily/CauchyDavenport.lean`), EGZ, Sperner/LYM, Hall marriage
(`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas, Zeckendorf, Beatty,
Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert Nullstellensatz
(`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form), Chevalley–Warning
(`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange four squares,
quadratic reciprocity, Möbius inversion, group Cayley's theorem
(`GroupTheory/Perm/Subgroup.lean` — embed in `Sym`; **not** labelled trees), Cayley–Hamilton
(`LinearAlgebra/Matrix/Charpoly` — **not** labelled trees), Configuration `HasLines.card_le`
(de Bruijn–Erdős incidence form), Hamiltonian *definitions* (Dirac theorem now in ProofLab,
not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence filled in ProofLab
circuit + 2-odd trail), `Subgraph.IsMatching` (no König / no vertex cover in Mathlib —
ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated), `IsChain` /
`IsAntichain` *definitions* (Dilworth now in ProofLab), `Colorable` / `chromaticNumber` /
`maxDegree` / `chromaticNumber_top` / `Walk.three_le_chromaticNumber_of_odd_loop` (no Brooks
in Mathlib; greedy `χ ≤ Δ+1` and Brooks Δ≤2 family now in ProofLab, not upstream), `degree`
/ handshaking (`sum_degrees_eq_twice_card_edges`) — **not** Havel–Hakimi (ProofLab),
`Walk` / `Reachable` / `Connected` — **not** Menger (ProofLab), `IsTree` /
`IsTree.card_edgeFinset` / `fromEdgeSet` — **not** Cayley's `n^{n-2}` count, `CliqueFree` —
**not** Mycielski unbounded-χ, `lapMatrix` (kernel rank = components) — **not** Kirchhoff
matrix-tree.

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`cayley-trees` — RECOMMENDED PRIME (85).** Independent re-score of the OPE-666
   considered-not-slotted Cayley line — **not** a rubber-stamp. Why-not-classical: Cayley
   1889 / Prüfer 1918 labelled-tree count `n^{n-2}` is settled. Why still a bet / why a new
   layer: last Scout benched it because `SimpleGraph` is a large type; this run **pins**
   `LabelledTree n := {s : Finset (Sym2 (Fin n)) // (fromEdgeSet ↑s).IsTree}`, so that
   bench reason no longer holds. Mathlib has `IsTree` / `fromEdgeSet` /
   `IsTree.card_edgeFinset`; ZERO Prüfer, ZERO labelled-tree cardinality (the only "Prüfer"
   hit is the unrelated Prüfer *subgroup*). Proof shape: Prüfer bijection, human-scale.
   Group Cayley and Cayley–Hamilton are *different* already-upstream theorems. Kirchhoff
   matrix-tree is a *different* theorem (`K_n` special case) — do **not** prove it in this
   id. STATEMENT pin: `catalog/problems/cayley-trees/STATEMENT.md`.
2. **`mycielski-triangle-free` (82).** Fresh id — never previously shortlisted. Why-not-classical:
   Mycielski 1955 triangle-free graphs of arbitrarily high `χ` is settled. Why still a bet /
   why a new layer: colouring slots (greedy + Brooks A/B) are consumed; this is `χ` versus
   `ω` (`CliqueFree 3`), **not** Brooks `χ` versus `Δ` and **not** namesake Kempe. Mathlib
   has `CliqueFree` / `Colorable` / odd-loop `χ ≥ 3`; ZERO `Mycielski`. Proof shape: `C5`
   Level A glue (reuse odd-loop lemma, not labelled Mycielski) then iterate `μ(G)` on
   `V ⊕ V ⊕ Unit`. Score 82 because the construction encoding is new. Do **not** assign
   before `cayley-trees` unless Director swaps. Do **not** prove Grötzsch / Hajós / Kneser /
   Vizing / 4CT/5CT. STATEMENT pin:
   `catalog/problems/mycielski-triangle-free/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-666 leftovers):

- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  ident hits). Re-eval vs last bench: `MvPolynomial` **is** in Mathlib (Chevalley–Warning
  already uses it), so "unused in ProofLab" is weaker than OPE-666 stated. Still **bench**:
  Chevalley–Warning already upstream (finite-field counting corollary that often motivates
  CNS); slot cap used by graph-infra bets with defs waiting (`IsTree`, `CliqueFree`). Not a
  rubber-stamp.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only; Ore hits in
  Mathlib are localization, not Ore's theorem). Proof shape is a re-warm of closed Dirac
  longest-path. **Not slotted.** Do not invent Ore as a leftover.
- **Tutte's theorem:** explicit Matching.lean TODO, ZERO theorem. Classical but banned as a
  leftover this commission. Bench.
- **Kirchhoff matrix-tree:** `LapMatrix` exists; ZERO spanning-tree count. Would be the
  `K_n` generalisation of the Cayley prime — do **not** invent as a leftover of `cayley-trees`.
- **König edge-chromatic `χ'=Δ`:** ZERO `chromaticIndex` / `LineGraph`. Looks like inventing
  Vizing (banned). Bench.
- **Five colour / planar:** Coloring.lean TODO lists planar; ZERO planar defs. Bench.
- **Namesake Kempe / Brooks Level C / list-colouring Brooks / Vizing / 4CT / Dilworth-C /
  Eulerian-C / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser /
  Whitney:** Director declined. Do not invent.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-702 update (2026-08-30, Scout, support OPE-701):** catalog audit + fresh ≤2 shortlist.
OPE-683 shortlist **plus** the OPE-687/OPE-694 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #65, `cb6cad3b`). Director does not invent primes.
This is **not** a Director-invented Dilworth-C / Eulerian-C / Ore / Vizing / 4CT / list-colouring Brooks / namesake Kempe / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser / Tutte / Whitney / Kirchhoff / Grötzsch / Hajós / Kneser / Mycielski-C / Prüfer-namesake continuation: Kruskal–Katona is a fresh SetFamily id (shadow-minimiser on colex init segments — defs already waiting in Mathlib); Oddtown is a fresh linear-algebra-method id (not EKR).

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `cayley-trees` Level A | OPE-688 Formalist; PR **#64 MERGED** (`50073a9`). `cayley_formula_of_le_three` on main. Namesake Prüfer **not** sorry-ed | yes. Status stays `informal`. Do **not** invent Prüfer-namesake / Kirchhoff / Tutte / Whitney / unlabelled A000055 |
| `mycielski-triangle-free` Level A+B namesake | OPE-695 Formalist; PRG OPE-699; PR **#65 MERGED** (`cb6cad3b`). `mycielski_unbounded` on main. Zero-sorry | yes. Status `formalized`. Do **not** invent Mycielski-C / Grötzsch / Hajós / Kneser / Vizing / 4CT |
| `havel-hakimi` Level A + reverse | PR **#61 MERGED**. Namesake forward switching **not** sorry-ed | yes. Do not expand into Erdős–Gállai / Gale–Ryser / Tutte |
| `menger-vertex` Level A | PR **#62 MERGED**. Namesake `s = p` **not** sorry-ed | yes. Do **not** invent namesake Diestel / edge-Menger / max-flow / infinite Erdős–Menger |
| `greedy-chromatic` Level A+B | PR **#57 MERGED** | yes. Do not expand into Brooks / list-colouring |
| `brooks-coloring` Level A/B | PRs **#58** / **#59 MERGED**. Namesake residual is a comment (Kempe / Lovász) | yes. Do **not** invent namesake Kempe / Level C / list-colouring Brooks |
| `dilworth-poset` Level A+B | PRs **#53** / **#54 MERGED**. Residual EMPTY | yes. Do not invent Level C / Mirsky / Greene |
| `eulerian-hierholzer` A / circuit / trail | PRs **#47** / **#51** / **#55 MERGED** | yes. Do not invent Eulerian-C |
| `konig-bipartite` Level A+B | PRs **#48** / **#50 MERGED** | yes |
| Scout shortlist PRs **#46** / **#49** / **#52** / **#56** / **#60** / **#63** | MERGED | yes |
| `euler-odd-distinct` / Dirac A+B / EKR / friendship / schur_partition / Glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Catalog hygiene this run: Mycielski `problems.json` verified **PR #65 MERGED** + `formalized` (namesake landed). Cayley verified **PR #64 MERGED** + honest `informal` (Prüfer residual). Not a new proof layer.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport
(`Combinatorics/SetFamily/CauchyDavenport.lean`), EGZ, Sperner/LYM (`IsAntichain.sperner`),
Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas, Zeckendorf, Beatty,
Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert Nullstellensatz
(`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form), Chevalley–Warning
(`FieldTheory/ChevalleyWarning.lean`), Burnside (group actions), Lagrange four squares,
quadratic reciprocity, Möbius inversion, group Cayley's theorem
(`GroupTheory/Perm/Subgroup.lean` — **not** labelled trees), Cayley–Hamilton
(`LinearAlgebra/Matrix/Charpoly` — **not** labelled trees), Configuration `HasLines.card_le`
(de Bruijn–Erdős incidence form), Hamiltonian *definitions* (Dirac theorem now in ProofLab,
not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence filled in ProofLab
circuit + 2-odd trail), `Subgraph.IsMatching` (no König / no vertex cover in Mathlib —
ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated), `IsChain` /
`IsAntichain` *definitions* (Dilworth now in ProofLab), `Colorable` / `chromaticNumber` /
`maxDegree` / `chromaticNumber_top` / `Walk.three_le_chromaticNumber_of_odd_loop` (no Brooks
in Mathlib; greedy `χ ≤ Δ+1`, Brooks Δ≤2 family, and Mycielski unbounded-χ now in ProofLab,
not upstream), `degree` / handshaking — **not** Havel–Hakimi (ProofLab), `Walk` / `Reachable`
— **not** Menger (ProofLab), `IsTree` / `fromEdgeSet` / `card_edgeFinset` — **not** Cayley's
`n^{n-2}` count (ProofLab Level A), `CliqueFree` — **not** Mycielski (ProofLab), `lapMatrix`
(kernel rank = components) — **not** Kirchhoff matrix-tree, `Finset.shadow` / `IsInitSeg` /
`UV.card_shadow_compression_le` — **not** Kruskal–Katona (the namesake is the gap),
`LinearIndependent` / `ZMod` / graph `incMatrix` — **not** Oddtown (the set-family theorem
is the gap; `incMatrix` is the wrong matrix).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`kruskal-katona` — RECOMMENDED PRIME (86).** Fresh id — never previously shortlisted.
   Why-not-classical: Kruskal 1963 / Katona 1968 colex shadow-minimiser is settled. Why still
   a bet / why a new layer: Cayley (`IsTree`) and Mycielski (`CliqueFree`) defs-waiting slots
   are consumed; Mathlib's own Colex / Shadow / UV-compression files were written **for this
   theorem** and still do not prove it (UV.lean comments: “key fact in Kruskal-Katona”).
   Sperner/LYM are *different* already-upstream theorems. Dilworth is *consumed in ProofLab*.
   Proof shape: Level A empty/singleton/`r≤1` + UV glue (not labelled KK); Level B namesake
   `IsInitSeg 𝒞 r ∧ 𝒞.card = 𝒜.card ⇒ (∂𝒞).card ≤ (∂𝒜).card`. Score 86 because defs are
   waiting but the colex-minimiser glue is the budget sink (verification 14). Do **not**
   assign `oddtown` first unless Director swaps. Do **not** prove Hilton–Milner / Oddtown /
   Eventown / Lovász-`ℝ` binomial in this id. STATEMENT pin:
   `catalog/problems/kruskal-katona/STATEMENT.md`.
2. **`oddtown` (84).** Fresh id — never previously shortlisted. Why-not-classical: Berlekamp
   1969 oddtown bound is settled. Why still a bet / why a new layer: EKR (intersecting
   k-uniform) is consumed in ProofLab; this is a *parity* constraint via `GF(2)` characteristic
   vectors, **not** intersecting families. Mathlib has `LinearIndependent` / `ZMod`; ZERO
   Oddtown / Eventown / Berlekamp. Proof shape: Level A empty/`n≤1`/singleton tightness;
   Level B namesake `𝒜.card ≤ n` by linear independence of `charVec`. Score 84 because
   `charVec` is new encoding even though the namesake is short. Do **not** assign before
   `kruskal-katona` unless Director swaps. Do **not** prove Eventown / Fisher / BIBD /
   Hilton–Milner. STATEMENT pin: `catalog/problems/oddtown/STATEMENT.md`.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-683 leftovers):

- **Combinatorial Nullstellensatz:** gap still holds (Hilbert NS ≠ Alon 1999; ZERO combinatorial
  ident hits). Re-eval vs last bench: graph-infra “defs waiting” (`IsTree`, `CliqueFree`) are
  now consumed, so that *slot-cap* reason is weaker. Still **bench**: Chevalley–Warning already
  upstream (the finite-field counting corollary that often motivates CNS); univariate `n=1`
  is Mathlib `Polynomial` root bounds; remaining multivariate coeff lemma is `MvPolynomial`
  unused in ProofLab, while Kruskal–Katona has *ready* Colex/Shadow/UV scaffolding. Not a
  rubber-stamp.
- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only). Proof shape
  is a re-warm of closed Dirac longest-path. **Not slotted.** Do not invent Ore as a leftover.
- **Tutte's theorem:** explicit Matching.lean TODO, ZERO theorem. Banned as a leftover this
  commission. Bench.
- **Kirchhoff matrix-tree:** `LapMatrix` exists; ZERO spanning-tree count. Would be the `K_n`
  generalisation of consumed Cayley — do **not** invent as a leftover of `cayley-trees`.
- **König edge-chromatic `χ'=Δ`:** ZERO `chromaticIndex` / `LineGraph`. Looks like inventing
  Vizing (banned). Bench.
- **Five colour / planar:** Coloring.lean TODO lists planar; ZERO planar defs. Bench.
- **Hilton–Milner:** ZERO theorem (gap holds) but it is the uniqueness companion of consumed
  EKR — do **not** invent as an `erdos-ko-rado` leftover. Bench.
- **Namesake Kempe / Brooks Level C / list-colouring Brooks / Vizing / 4CT / Dilworth-C /
  Eulerian-C / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser /
  Whitney / Grötzsch / Hajós / Kneser / Mycielski-C / Prüfer-namesake:** Director declined.
  Do not invent.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

**OPE-717 update (2026-08-30, Scout, support OPE-716):** catalog audit + fresh ≤2 shortlist.
OPE-702 shortlist **plus** the OPE-706/OPE-711 Formalist assignment wave is **fully consumed on merged main**.
Zero open PRs at scout start (`origin/main` = merge of PR #68, `0b531ef`). Director does not invent primes.
This is **not** a Director-invented Dilworth-C / Eulerian-C / Ore / Vizing / 4CT / list-colouring Brooks / namesake Kempe / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser / Tutte / Whitney / Kirchhoff / Grötzsch / Hajós / Kneser / Mycielski-C / Prüfer-namesake / Eventown / Fisher / BIBD / Hilton–Milner / Sperner/LYM / Kruskal–Katona-C / Oddtown-C continuation: sunflower is a fresh Δ-system id (not intersecting / not parity / not shadows); combinatorial Nullstellensatz is a polynomial-method id (not Hilbert NS, not Chevalley–Warning).

Consumption (live this run):

| Prior slot | Disposition | Do not re-prime? |
|------------|-------------|------------------|
| `kruskal-katona` Level A+B namesake | OPE-707 Formalist; PRG OPE-709; PR **#67 MERGED** (`a00d323`). `kruskal_katona` on main. Zero-sorry | yes. Status `formalized`. Hygiene this run: catalog `pr` stamped #67. Do **not** invent Kruskal–Katona-C / Lovász-ℝ binomial / Sperner/LYM |
| `oddtown` Level A+B namesake | OPE-712 Formalist; PRG OPE-714; PR **#68 MERGED** (`0b531ef`). `oddtown` on main. Zero-sorry | yes. Status `formalized`. Hygiene this run: catalog `pr` stamped #68. Do **not** invent Oddtown-C / Eventown / Fisher / BIBD / Hilton–Milner |
| `cayley-trees` Level A | PR **#64 MERGED**. Namesake Prüfer **not** sorry-ed | yes. Status stays `informal`. Do **not** invent Prüfer-namesake / Kirchhoff / Tutte / Whitney / unlabelled A000055 |
| `mycielski-triangle-free` Level A+B namesake | PR **#65 MERGED**. `mycielski_unbounded` on main | yes. Do **not** invent Mycielski-C / Grötzsch / Hajós / Kneser / Vizing / 4CT |
| `havel-hakimi` Level A + reverse | PR **#61 MERGED**. Namesake forward switching **not** sorry-ed | yes. Do not expand into Erdős–Gállai / Gale–Ryser / Tutte |
| `menger-vertex` Level A | PR **#62 MERGED**. Namesake `s = p` **not** sorry-ed | yes. Do **not** invent namesake Diestel / edge-Menger / max-flow / infinite Erdős–Menger |
| `greedy-chromatic` Level A+B | PR **#57 MERGED** | yes. Do not expand into Brooks / list-colouring |
| `brooks-coloring` Level A/B | PRs **#58** / **#59 MERGED**. Namesake residual is a comment (Kempe / Lovász) | yes. Do **not** invent namesake Kempe / Level C / list-colouring Brooks |
| `dilworth-poset` Level A+B | PRs **#53** / **#54 MERGED**. Residual EMPTY | yes. Do not invent Level C / Mirsky / Greene |
| `eulerian-hierholzer` A / circuit / trail | PRs **#47** / **#51** / **#55 MERGED** | yes. Do not invent Eulerian-C |
| `konig-bipartite` Level A+B | PRs **#48** / **#50 MERGED** | yes |
| Scout shortlist PRs **#46** / **#49** / **#52** / **#56** / **#60** / **#63** / **#66** | MERGED | yes |
| `euler-odd-distinct` / Dirac A+B / EKR / friendship / schur_partition / Glaisher | previously consumed | yes |
| ramsey-r33 / R(3,4) / R(4,4); ramsey-r35; ramsey-multicolor-r333 (PR #36); weak-schur-ws2 (PR #35); S(2)/S(3); W(2,3); ES monotone; ES(3)=5 (PRs #24/#25); EW k=16; frobenius / derangement / catalan / turan | previously closed or already-in-Mathlib | yes |

**Leave OPE-403 alone** (Happy Ending parked on board confirmation since 2026-08-24).

Catalog hygiene this run: Kruskal–Katona `problems.json` stamped **PR #67 MERGED** + `formalized` (namesake landed). Oddtown stamped **PR #68 MERGED** + `formalized`. Not a new proof layer.

Mathlib pin re-grepped this run: `a719ba5c3115` / `v4.10.0`. **Negative control:** `turan` →
`Mathlib/Combinatorics/SimpleGraph/Turan.lean` (`isTuranMaximal_iff_nonempty_iso_turanGraph`)
⇒ never cite Turán as a gap. **Already in Mathlib (never cite as gap):** Cauchy–Davenport
(`Combinatorics/SetFamily/CauchyDavenport.lean`), EGZ, Sperner/LYM (`IsAntichain.sperner`),
Hall marriage (`HallMarriageTheorem` / `hall_hard_inductive`), Wilson, Lucas, Zeckendorf, Beatty,
Pythagorean triples, Turán, non-uniform `Intersecting.card_le`, Hilbert Nullstellensatz
(`RingTheory/Nullstellensatz.lean` — **not** Alon's combinatorial form), Chevalley–Warning
(`FieldTheory/ChevalleyWarning.lean`), Hales–Jewett (`Line.exists_mono_in_high_dimension`) +
homothetic VdW existence (`exists_mono_homothetic_copy`; finitary exact W(2,k) still a TODO),
Hindman, Sauer–Shelah / Pajor (`SetFamily/Shatter.lean` `card_le_card_shatterer` + `vcDim`),
Four Functions / Ahlswede–Zhang / Harris–Kleitman, Burnside (group actions), Lagrange four squares,
quadratic reciprocity, Möbius inversion, group Cayley's theorem
(`GroupTheory/Perm/Subgroup.lean` — **not** labelled trees), Cayley–Hamilton
(`LinearAlgebra/Matrix/Charpoly` — **not** labelled trees), Configuration `HasLines.card_le`
(de Bruijn–Erdős incidence form), Hamiltonian *definitions* (Dirac theorem now in ProofLab,
not Mathlib), `Walk.IsEulerian` + necessary `card_odd_degree` (existence filled in ProofLab
circuit + 2-odd trail), `Subgraph.IsMatching` (no König / no vertex cover in Mathlib —
ProofLab has both), cardinal König (`SetTheory.Cardinal`, unrelated), `IsChain` /
`IsAntichain` *definitions* (Dilworth now in ProofLab), `Colorable` / `chromaticNumber` /
`maxDegree` / `chromaticNumber_top` / `Walk.three_le_chromaticNumber_of_odd_loop` (no Brooks
in Mathlib; greedy `χ ≤ Δ+1`, Brooks Δ≤2 family, and Mycielski unbounded-χ now in ProofLab,
not upstream), `degree` / handshaking — **not** Havel–Hakimi (ProofLab), `Walk` / `Reachable`
— **not** Menger (ProofLab), `IsTree` / `fromEdgeSet` / `card_edgeFinset` — **not** Cayley's
`n^{n-2}` count (ProofLab Level A), `CliqueFree` — **not** Mycielski (ProofLab), `lapMatrix`
(kernel rank = components) — **not** Kirchhoff matrix-tree, `Finset.shadow` / `IsInitSeg` /
`UV.card_shadow_compression_le` — **not** Kruskal–Katona (ProofLab namesake),
`LinearIndependent` / `ZMod` / graph `incMatrix` — **not** Oddtown (ProofLab namesake;
`incMatrix` is the wrong matrix), `YoungDiagram` / `SemistandardYoungTableau` *definitions*
— **not** hook-length (no theorem), `MvPolynomial.coeff` / `degreeOf` / `eval` — **not**
combinatorial Nullstellensatz (the non-vanishing lemma is the gap).

Fresh shortlist (≤2, known-classical / formalize-only, no novelty claims):

1. **`sunflower-erdos-rado` — RECOMMENDED PRIME (88).** Fresh id — never previously
   shortlisted. Why-not-classical: Erdős–Rado 1960 sunflower / Δ-system bound is settled.
   Why still a bet / why a new layer: Kruskal–Katona (shadows) and Oddtown (GF(2) parity)
   are consumed; this is a *Δ-system* configuration theorem, **not** intersecting families,
   **not** parity, **not** colex shadows. Mathlib has `Finset` and already-upstream
   Sauer–Shelah (`card_le_card_shatterer`); ZERO sunflower ident. The **sunflower
   conjecture** is open and is **out of v1**. Proof shape: Level A `k=1`/`r≤1`/empty;
   Level B namesake `r! (k-1)^r < |𝒜| ⇒ ∃ k-petals sunflower`. Score 88 because Finset
   encoding is native (formalizability 18) but there is no dedicated scaffolding written
   for this theorem (attack 16). Do **not** assign `combinatorial-nullstellensatz` first
   unless Director swaps. Do **not** prove the conjecture / ALWZ / Eventown / Fisher /
   Hilton–Milner in this id. STATEMENT pin:
   `catalog/problems/sunflower-erdos-rado/STATEMENT.md`.
2. **`combinatorial-nullstellensatz` (84).** Independent re-score of the OPE-702
   considered-not-slotted CNS line — **not** a rubber-stamp. Why-not-classical: Alon 1999
   non-vanishing form is settled. Why still a bet / why a new layer: OPE-702 benched CNS
   because Kruskal–Katona had ready Colex/Shadow/UV scaffolding; that competitor is now
   consumed. Hilbert NS and Chevalley–Warning remain *different* already-upstream theorems.
   Mathlib has `MvPolynomial.coeff` / `degreeOf` / `eval`; ZERO combinatorial Nullstellensatz
   ident. Proof shape: Level A `n≤1` univariate glue (not labelled CNS); Level B namesake
   non-vanishing on a box. Score 84 because MvPolynomial is unused in ProofLab and the
   multivariate division/induction is the Lean sink (verification 14). Do **not** assign
   before `sunflower-erdos-rado` unless Director swaps. Do **not** prove Hilbert NS / CW /
   EGZ / Alon–Füredi. STATEMENT pin:
   `catalog/problems/combinatorial-nullstellensatz/STATEMENT.md`.
   **CONSUMED this heartbeat:** Formalist **OPE-729** Level A+B namesake landed
   (zero-sorry `ProofLab/CombinatorialNullstellensatz.lean`). OPE-717 wave fully
   consumed (sunflower #70 + this leftover). Not a re-prime.

Re-evaluated, not shortlisted (do not rubber-stamp OPE-702 leftovers):

- **ES(4)=9:** still no human-scale hand proof. Reject. Leave OPE-403 alone.
- **ramsey-r46** R(4,6)=41: still no hand upper bound / no certified witness in repo. Reject.
- **W(2,4)≤35:** still no named human-scale case-split/certificate. Stay bench/skip
  (standing OPE-458/533 rule). Closed `vdw24_gt_34` is not a re-prime. General VdW
  *existence* is already in Mathlib (`exists_mono_homothetic_copy` via Hales–Jewett) —
  not a gap.
- **Ore stretch:** independently a remaining Mathlib gap (Hamiltonian defs only). Proof shape
  is a re-warm of closed Dirac longest-path. **Not slotted.** Do not invent Ore as a leftover.
- **Tutte's theorem:** explicit Matching.lean TODO, ZERO theorem. Banned as a leftover this
  commission. Bench.
- **Kirchhoff matrix-tree:** `LapMatrix` exists; ZERO spanning-tree count. Would be the `K_n`
  generalisation of consumed Cayley — do **not** invent as a leftover of `cayley-trees`.
- **König edge-chromatic `χ'=Δ`:** ZERO `chromaticIndex` / `LineGraph`. Looks like inventing
  Vizing (banned). Bench.
- **Five colour / planar:** Coloring.lean TODO lists planar; ZERO planar defs. Bench.
- **Hilton–Milner:** ZERO theorem (gap holds) but it is the uniqueness companion of consumed
  EKR — do **not** invent as an `erdos-ko-rado` leftover. Bench.
- **Rédei / tournaments:** ZERO `IsTournament`; Hamiltonian *path* defs exist. Encoding-from-scratch,
  same class as the planar bench. Bench.
- **Hook-length formula:** `YoungDiagram` / `SemistandardYoungTableau` defs waiting, ZERO theorem.
  Proof is a known sink (GNW probabilistic / Nijenhuis–Wilf / RSK) — worse than Cayley's Prüfer
  residual. Bench; do not invent as a “defs waiting” prime this wave.
- **Sauer–Shelah:** already in Mathlib (`card_le_card_shatterer`). Never cite as a gap.
- **Namesake Kempe / Brooks Level C / list-colouring Brooks / Vizing / 4CT / Dilworth-C /
  Eulerian-C / edge-Menger / max-flow / infinite Erdős–Menger / Erdős–Gállai / Gale–Ryser /
  Whitney / Grötzsch / Hajós / Kneser / Mycielski-C / Prüfer-namesake / Eventown / Fisher /
  BIBD / Kruskal–Katona-C / Oddtown-C:** Director declined. Do not invent.

Director assigns after approval. Scout opened **no attack issues**. Do not merge. Do not claim.

## Active sprint (from OPE-43)


**OPE-43 (Director): approved the fresh Scout keep-fresh shortlist (OPE-36/PR #14 + van-der-Waerden PR #10).**
Next bets are all known-classical → **formalize-only**, genuine Mathlib gaps, zero novelty claims.
Prime = `ramsey-r33` (Scout's own recommendation: "ramsey-r33 recommended first"). Wake-order chain via
blockedBy: OPE-44 → OPE-45 → OPE-46 (one specialist at a time).

| Bet | Issue | Owner role | Intent |
|-----|-------|------------|--------|
| `ramsey-r33` (R(3,3)=6 / R(3,4)=9 / R(4,4)=18) | **OPE-44** (child of OPE-43; PRIME) | Attack Lead | **DONE formalized.** Zero-sorry Lean: eq bounds for all three; `lake build ProofLab` green. formalize-only, no claim. |
| `van-der-waerden-w23` (W(2,3)=9) | **OPE-45** (child of OPE-43; blockedBy OPE-44) | Attack Lead | Formalize-only finitary VdW; Mathlib TODO (HalesJewett.lean L50-53). |
| `schur-number` (S(2)/S(3)) | **OPE-46** (child of OPE-43; blockedBy OPE-45) | Attack Lead | Formalize-only Schur numbers; pin indexing convention in statement. |
| OPE-43 control | **OPE-43** | Research Director | Approve Scout shortlist, assign Attack Lead, keep catalog+ledger, open PR — then **done**. |

**Wake discipline:** one specialist at a time on shared model limits. OPE-44 fires first; OPE-45/46 are
blocked until their predecessor completes (or board raises concurrency).

## Lessons encoded (do not relearn the hard way)

1. **Definition bugs kill sprints** — OPE-12 EW used a non-standard predicate; board veto. Always pin literature definition in STATEMENT.md before “solved.”
2. **Known theorems are process fuel, not discoveries** — sum-free, caterpillar-graceful families: label `informal`/`heuristic`, residual risks mandatory.
3. **Enumeration ≠ isomorphism classes** — OPE-13/18: 2142 representations → 560 distinct after adversarial pressure.
4. **Compute ≠ Lean** — passing Python tests with `sorry` in Lean is blocked at review (OPE-14).
5. **Git SoT** — write under `Documents/VSCode/open-math-lab`, not Paperclip managed `_default` mirror.
6. **Scout shortlist gate** — Director must not pick primes from catalog scores alone. Fresh Scout shortlist (or explicit board-named problem) before new attack issues (`docs/PORTFOLIO_PRINCIPLES.md`).
7. **Verify “Mathlib gap” claims against the local toolchain first** — OPE-25: frobenius (`frobeniusNumber_pair`), derangement (`numDerangements*`), catalan (`catalan*`) were all **already in Mathlib** despite dossier “gap” claims; only schur-partition was a real gap. `grep` the pinned `Mathlib/` snapshot (`.lake/packages/mathlib`) before citing a gap or scoring a candidate.

## How to update this ledger

1. Change status in `catalog/problems.json`.
2. Add/adjust the row in **Handled** or **Untouched**.
3. Link attack dir + Paperclip issue IDs in the table.
4. If a skill pack gained a real tactic/checklist, patch `skills/<pack>/SKILL.md` and note it under lessons or the problem row.
