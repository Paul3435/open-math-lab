# mathforge Problem Catalog

This directory contains curated mathematical problems suitable for formalization
and attack within mathforge constraints.

**Authoritative handled-history:** [`docs/PROBLEM_LEDGER.md`](../docs/PROBLEM_LEDGER.md)  
**Index JSON:** [`problems.json`](problems.json)

## Structure

```
catalog/
├── problems.json          # Index of all problems (+ statuses)
├── README.md              # This file
└── problems/
    ├── <problem-id>/
    │   ├── STATEMENT.md   # Problem statement and formalization target
    │   └── DOSSIER.json   # Feasibility scores and metadata
    └── ...
```

Working attack trees and extra notes also live under repo-root `problems/<id>/`
and `attacks/<id>-<timestamp>/`. Prefer git SoT:
`C:\Users\paulb\Documents\VSCode\open-math-lab`.

## Snapshot (2026-08-04, OPE-21)

### Active / shortlisted

| Problem ID | Title | Domain | Score | Status |
|------------|-------|--------|------:|--------|
| **frobenius-coin-problem** | Frobenius Coin Problem (Two Denominations) | Number Theory | 90 | **shortlisted (OPE-22 attack)** |
| sum-free-subsets | Sum-Free Subsets in Finite Sets | Additive Combinatorics | 90 | informal (OPE-14 process; known thm) |
| derangement-formula | Derangement Counting Formula | Enumerative Combinatorics | 89 | candidate |
| catalan-recurrence | Catalan Numbers - Recurrence and Closed Form | Enumerative Combinatorics | 85 | candidate |
| bertrand-postulate-computational | Bertrand Computational Certificate | Computational NT | 84 | candidate |
| schur-partition | Schur partition theorem | Partitions | — | candidate (formalize-only) |
| erdos-woods | Erdős-Woods k=16 (correct a=2184) | Elem. NT | — | candidate; OPE-12 claim **vetoed** |

### Handled (see ledger for full residual risks)

| Problem ID | Result | Tickets |
|------------|--------|---------|
| graceful-tree-conjecture (caterpillars n≤12) | heuristic verify, 560 classes, 0 failures; family already known graceful ∀n | OPE-13,18,20 |
| erdos-woods (false a=5 path) | definition bug → board veto | OPE-12,15 |
| sum-free-subsets | classical Erdős; compute OK; Lean not claim-ready | OPE-14 |

### Seeds / needs Scout

| ID | Notes |
|----|-------|
| demo-collatz-bound-toy | pipeline demo only |
| ~~mathlib-gap-candidate~~ | **replaced** 2026-08-07 (Scout keep-fresh) → `van-der-Waerden-w23`, then `ramsey-r33`/`schur-number` |
| ~~oeis-finite-check-candidate~~ | **replaced** 2026-08-07 (Scout keep-fresh) → `ramsey-r33` + `schur-number` (formalize-only, Mathlib-gap) |

## Usage

```bash
python bin/mathforge list
python bin/mathforge score <problem-id>
python bin/mathforge shortlist --limit 3
```

## Scoring Methodology

See `docs/FEASIBILITY_RUBRIC.md`. Five dimensions × 0–20 → total 0–100.

| Total | Verdict |
|------:|---------|
| 80–100 | Prime target |
| 60–79 | Feasible |
| 40–59 | Risky (board justification) |
| 20–39 | Long shot |
| 0–19 | Infeasible |

## Problem Lifecycle

1. **Candidate** — Scout curated and scored  
2. **Shortlisted** — Director approved for attack  
3. **In Progress** — Attack Lead working  
4. **In Review** — Adversarial Reviewer  
5. **Claim-Ready** — rare; board escalation only  
6. **Completed / formalized / heuristic / informal / vetoed** — see ledger labels  
7. **Archived** — abandoned or superseded by Mathlib  

## Catalog Curation Policy

**Add** if: well-defined + authoritative source; score ≥ 60 (or justified); not already trivial in Mathlib without extension value; no crackpot triggers.

**Remove / archive** if: already fully in Mathlib with no lab value; score collapses < 40; crankery.

## Novelty tagging (OPE-28)

Every `problems.json` entry must carry an `expected` tag set by Scout during the pre-screen
(before funding an attack), per `docs/roles/problem-scout.md`:

- `known-classical` — already in Mathlib/classic literature → do not re-fund as novel
- `formalize-only` — genuine Mathlib gap, no novelty claim
- `open` — unsolved; eligible for a gate-funded attack

Fuller enum in `problems.json` → `expected_taxonomy`.

## Prize-money shortlist (OPE-1028, 2026-09-06) — WAVE CONSUMED

Board asked for one *open* problem with *live cash*. Scout did **not** solve and did **not** open Lean.

1. **`krenn-gu` — CONSUMED.** PR **#101** Level A + PR **#102** Level B. €3,000 namesake **out of v1**. No Level C. Do not revive.
2. **`hou-zeng-pfc` — CONSUMED Level A.** PR **#103**. $1,000/$200 namesake `∀ n>4` **out of v1**. Level B declined (OPE-1047). Do not email Hou/Zeng. Do not revive.
3. **`sun-135` — ARCHIVED (OPE-1042 REJECT / OPE-1062 stamp).** Proved 2020; not live cash. Do not revive.

RSA Factoring Challenge **ended 2007**. Millennium / Beal $1M **out of v1 as a solve**. No prize claim.

## Formalize-only shortlist (OPE-1062, 2026-09-07) — WAVE CONSUMED

Catalog-audit mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`frobenius-real-division` — CONSUMED.** PR **#105** Level A. Catalog `formalized`. Level B `AlgEquiv` **out of v1**. Do not revive.
2. **`noether-normalization` — CONSUMED Level A.** PR **#106**. Catalog `formalized`. Level B namesake **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1078, 2026-09-07) — WAVE CONSUMED

OPE-1078 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`andrasfai-erdos-sos` — CONSUMED.** PR **#108** Level A. Catalog `formalized`. Level B namesake AES **out of v1**. Do not revive.
2. **`ostrowski-q` — CONSUMED Level A.** PR **#109** Level A. Catalog `formalized`. Level B namesake ostrowski **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1095, 2026-09-07) — WAVE CONSUMED

OPE-1095 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`ore-hamiltonian` — CONSUMED.** PR **#111** Level A. Catalog `formalized`. Level B namesake `ore_hamiltonian` **out of v1**. Do not revive.
2. **`bipartite-chromatic-index` — CONSUMED Level A.** PR **#112** Level A. Catalog `formalized`. Level B namesake `konig_edge_chromatic` **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1110, 2026-09-07) — WAVE CONSUMED

OPE-1110 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`schwartz-zippel` — CONSUMED.** PR **#114** Level A. Catalog `formalized`. Level B namesake `schwartz_zippel` **out of v1**. Do not revive.
2. **`hadamard-det` — CONSUMED Level A.** PR **#115** Level A. Catalog `formalized`. Level B namesake `hadamard_det` **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1125, 2026-09-07) — WAVE CONSUMED

OPE-1125 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” lines naming these ids are **INPUT to restamp**, not a prime.

1. **`cauchy-binet` — CONSUMED.** PR **#117** Level A. Catalog `formalized`. Level B namesake `cauchy_binet` **out of v1**. Kirchhoff residual **out of v1**. Do not revive.
2. **`bollobas-two-families` — CONSUMED Level A.** PR **#118** Level A. Catalog `formalized`. Level B namesake `bollobas` **out of v1**. Weighted `ℚ` residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1142, 2026-09-08) — WAVE CONSUMED

OPE-1142 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`singleton-bound` — CONSUMED.** PR **#120** Level A. Catalog `formalized`. Level B namesake `singleton_bound` **out of v1**. Hamming/Plotkin/MDS residual **out of v1**. Do not revive.
2. **`hook-length` — CONSUMED Level A.** PR **#121** Level A. Catalog `formalized`. Level B namesake `hook_length` **out of v1**. Catalan 2-row / RSK / hook-content residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1157, 2026-09-08) — WAVE CONSUMED

OPE-1157 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`birkhoff-von-neumann` — CONSUMED.** PR **#123** Level A. Catalog `formalized`. Level B namesake `birkhoff_von_neumann` / Gale–Ryser residual **out of v1**. Do not revive.
2. **`nash-williams-arboricity` — CONSUMED Level A.** PR **#124**. Catalog `formalized`. Level B namesake `nash_williams` / matroid-union residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1173, 2026-09-08) — WAVE CONSUMED

OPE-1173 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`gale-shapley` — CONSUMED.** PR **#126** Level A. Catalog `formalized`. Level B namesake `gale_shapley` / rural hospitals residual **out of v1**. Do not revive.
2. **`farey-sequence` — CONSUMED Level A.** PR **#127**. Catalog `formalized`. Level B namesake `farey_adjacent` / Stern–Brocot residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1189, 2026-09-08) — WAVE CONSUMED

OPE-1189 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`schur-product` — CONSUMED.** PR **#129** Level A. Catalog `formalized`. Level B namesake `schur_product` / SVD residual **out of v1**. Do not revive.
2. **`lame-euclid` — CONSUMED Level A.** PR **#130**. Catalog `formalized`. Level B namesake `lame` / Cassini residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1200, 2026-09-08) — WAVE CONSUMED

OPE-1200 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`circulant-det` — CONSUMED.** PR **#132** Level A. Catalog `formalized`. Level B namesake `det_circulant` / DFT / pfaffian / Kirchhoff residual **out of v1**. Do not revive.
2. **`wantzel-constructible` — CONSUMED Level A.** PR **#133**. Catalog `formalized`. Level B namesake `IsConstructible` tower / angle trisection residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1216, 2026-09-09) — WAVE CONSUMED

OPE-1216 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`petersen-1-factor` — CONSUMED Level A.** OPE-1223 Formalist. PR **#135**. Lean `ProofLab/PetersenOneFactor.lean`. Catalog `formalized`. Level B namesake `petersen_one_factor` / Tutte / Tait / snarks / Petersen-graph uniqueness residual **out of v1**. Do not revive.
2. **`lagrange-quadratic-cf` — CONSUMED Level A.** OPE-1228 Formalist. PR **#136**. Lean `ProofLab/LagrangeQuadraticCf.lean`. Catalog `formalized`. Level A: `(of φ).h = 1` and first two `partDens = 1`; optional `√2` extra. Level B namesake `lagrange_quadratic_cf` / Pell / Galois purely-periodic / Hurwitz residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1233, 2026-09-09) — WAVE CONSUMED

OPE-1233 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`kraft-inequality` — CONSUMED Level A.** OPE-1238 Formalist. PR **#138**. Lean `ProofLab/KraftInequality.lean`. Catalog `formalized`. Level A: empty Finset / singleton / binary `{[0],[1,0],[1,1]}` Kraft sum 1. Level B namesake `kraft_inequality` / McMillan / Huffman / Shannon residual **out of v1**. Do not revive.
2. **`sabidussi-boxprod` leftover (84) — CONSUMED Level A.** OPE-1243 Formalist. PR **#139**. Lean `ProofLab/SabidussiBoxProd.lean`. Catalog `formalized`. Level A: empty `⊥□⊥` / `K1□K1` / `K2□K2` Colorable. Level B namesake `sabidussi_boxprod` / Hedetniemi / other products / Vizing domination residual **out of v1**. Do not revive.

## Formalize-only shortlist (OPE-1248, 2026-09-09)

OPE-1233 mill consumed (#138+#139). Catalog-audit shortlist (not a prize hunt; not a Formalist leftover continuation; not a Level B namesake revival). Independent Mathlib v4.10.0 grep this run.

1. **`sherman-morrison` — CONSUMED Level A.** OPE-1253 Formalist. PR **#141**. Director OPE-1252 approved Scout OPE-1248 RECOMMENDED PRIME. Lean `ProofLab/ShermanMorrison.lean`. Catalog `formalized`. Level A: empty Fin 0 / Fin 1 scalar / Fin 2 `I+e₀e₀ᵀ` inverse, not labelled Sherman. Level B namesake `sherman_morrison` / Woodbury residual **out of v1**. Do not revive.
2. **`graham-pollak` leftover (84) — CONSUMED Level A.** OPE-1258 Formalist. PR **#142**. Director OPE-1257 approved Scout OPE-1248 leftover. Lean `ProofLab/GrahamPollak.lean`. Catalog `formalized`. Level A: K₁ empty / K₂ one edge / K₃ star-plus-edge, not labelled Graham–Pollak. Level B namesake `graham_pollak` / biclique cover / Zarankiewicz residual **out of v1**. Do not revive.

Scout opened **no attack issues**. Formalist OPE-1258 lands the leftover. OPE-1248 mill fully consumed.

## Formalize-only shortlist (OPE-1263, 2026-09-09)

OPE-1248 mill consumed (#141+#142). Catalog-audit shortlist (not a prize hunt; not a Formalist leftover continuation; not a Level B namesake revival). Independent Mathlib v4.10.0 grep this run.

1. **`fine-wilf` — CONSUMED Level A.** OPE-1268 Formalist. PR **#144**. Director OPE-1267 approved Scout OPE-1263 RECOMMENDED PRIME. Lean `ProofLab/FineWilf.lean`. Catalog `formalized`. Level A: empty / constant period 1 / `[0,1,0,1,0]` periods 2 and 4 + optional sharpness `[0,1,0,0,1,0]`, not labelled Fine–Wilf. Level B namesake `fine_wilf` / Lyndon–Schützenberger residual **out of v1**. Do not revive.
2. **`british-flag` leftover (84) — CONSUMED Level A.** OPE-1273 Formalist. PR **#145**. Director OPE-1272 approved Scout OPE-1263 leftover. Lean `ProofLab/BritishFlag.lean`. Catalog `formalized`. Level A: unit-square origin / vertex C / centre, not labelled British flag. Level B namesake `british_flag` / Napoleon / Simson / Viviani residual **out of v1**. Do not revive.

Scout opened **no attack issues**. Formalist OPE-1273 lands the leftover. OPE-1263 mill fully consumed.

## Formalize-only shortlist (OPE-1278, 2026-09-09)

OPE-1263 mill consumed (#144+#145). Catalog-audit shortlist (not a prize hunt; not a Formalist leftover continuation; not a Level B namesake revival). Independent Mathlib v4.10.0 grep this run.

1. **`platonic-solids` — CONSUMED Level A.** OPE-1284 Formalist. PR **#147**. Director OPE-1283 approved Scout OPE-1278 RECOMMENDED PRIME. Lean `ProofLab/PlatonicSolids.lean`. Catalog `formalized`. Level A: tetra/cube/octa/icosa/dodeca `(V,E,F)` witnesses + `(3,6)`/`(4,4)` fail, not labelled Platonic. Level B namesake `platonic_schlafli` / Euler polyhedron / Coxeter classification residual **out of v1**. Do not revive.
2. **`egyptian-fractions` leftover (84) — CONSUMED Level A.** OPE-1289 Formalist. PR **#148**. Director OPE-1288 approved Scout OPE-1278 leftover. Lean `ProofLab/EgyptianFractions.lean`. Catalog `formalized`. Level A: `1=1/1` / unit `1/n` / `3/4=1/2+1/4` / `2/3=1/2+1/6` + optional `1=1/2+1/3+1/6`, not labelled Egyptian. Level B namesake `egyptian_fractions` / Erdős–Straus residual **out of v1**. Do not revive.

Scout opened **no attack issues**. Formalist OPE-1289 lands the leftover. OPE-1278 mill fully consumed.

## Formalize-only shortlist (OPE-1294, 2026-09-10) — WAVE CONSUMED

OPE-1294 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`frucht-graph-aut` — CONSUMED Level A.** OPE-1300 Formalist. PR **#150**. Director OPE-1299 approved Scout OPE-1294 RECOMMENDED PRIME. Lean `ProofLab/FruchtGraphAut.lean`. Catalog `formalized`. Level A: unique Aut on `K₁`/`P₁` + `pathGraph 3` endpoint-swap `≠` refl + optional `K₂` swap via `Iso.completeGraph`, not labelled Frucht. Level B namesake `frucht_graph_aut` / Cayley-graph gadgets residual **out of v1**. Do not revive.
2. **`proth-primality` leftover (84) — CONSUMED Level A.** OPE-1305 Formalist. PR **#151**. Director OPE-1304 approved Scout OPE-1294 leftover. Lean `ProofLab/ProthPrimality.lean`. Catalog `formalized`. Level A: `3` / `5` / `13` form+witness `2` + optional `9` form-and-composite, not labelled Proth. Level B namesake `proth_primality` / Pépin / Pocklington / Fermat residual **out of v1**. Do not revive.

Scout opened **no attack issues**. Formalist OPE-1305 lands the leftover. OPE-1294 mill fully consumed.

## Formalize-only shortlist (OPE-1310, 2026-09-10) — WAVE CONSUMED

OPE-1310 mill fully consumed. Do **not** re-prime. Stale “RECOMMENDED PRIME” / leftover-unassigned lines naming these ids are **INPUT to restamp**, not a prime.

1. **`alcuin-integer-triangles` — CONSUMED Level A.** OPE-1316 Formalist. PR **#153**. Director OPE-1315 approved Scout OPE-1310 RECOMMENDED PRIME. Lean `ProofLab/AlcuinIntegerTriangles.lean`. Catalog `formalized`. Level A: perimeter `1` none / `3=(1,1,1)` / `5=(1,2,2)` / `6=(2,2,2)` + optional perimeter `7`, not labelled Alcuin. Level B namesake `alcuin_integer_triangles` / Heronian / Pick residual **out of v1**. Do not revive.
2. **`cannonball-square-pyramid` leftover (84) — CONSUMED Level A.** OPE-1321 Formalist. PR **#154**. Director OPE-1320 approved Scout OPE-1310 leftover. Lean `ProofLab/CannonballSquarePyramid.lean`. Catalog `formalized`. Level A: `P(1)=1²` / `P(24)=70²` + optional `P(2)` not square, not labelled cannonball / Lucas. Level B namesake `cannonball_square_pyramid` / Lucas uniqueness / Watson residual **out of v1**. Do not revive.

Scout opened **no attack issues**. Formalist OPE-1321 lands the leftover. OPE-1310 mill fully consumed.

## Formalize-only shortlist (OPE-1326, 2026-09-10)

OPE-1310 mill consumed (#153+#154). Catalog-audit shortlist (not a prize hunt; not a Formalist leftover continuation; not a Level B namesake revival). Independent Mathlib v4.10.0 grep this run.

1. **`jordan-canonical-form` — RECOMMENDED PRIME (86).** Fresh id. Jordan 1870: over an algebraically closed field every square matrix is similar to a block-diagonal matrix of Jordan blocks. Named theorem ZERO (`jordanCanonical` / `JordanForm` / `jordan_form` / `IsJordanBlock` / `JordanBlock`). `Matrix.aeval_self_charpoly` (Charpoly/Basic.lean L123) HIT as already-in Cayley–Hamilton glue **not** namesake. `exists_isNilpotent_isSemisimple` (JordanChevalley.lean L71) HIT as already-in Dunford split **not** namesake. `IsJordan` (Algebra/Jordan/Basic.lean L78) HIT as already-in Jordan-algebra identity **not** namesake. **Not** Sherman–Morrison / Cauchy–Binet / circulant-det / Hadamard / Schur-product (consumed matrix mills). **Not** Alcuin / cannonball (consumed #153+#154). Finite, one-wave Level A (`J=!![0,1;0,0]` with `J*J=0` and `J≠0` / diagonal `!![1,0;0,2]`).
2. **`orthogonal-latin-squares` leftover (84).** Fresh id. Euler 1782 Graeco-Latin: two Latin squares are orthogonal when symbol-pairs cover `[n]×[n]`; order 3 admits an affine pair, order 2 admits none. Named theorem ZERO (`latinSquare` / `LatinSquare` / `IsLatinSquare` / `orthogonalLatin` / `graecoLatin`). `Equiv.Perm` HIT as row-permutation glue **not** namesake. `ProjectivePlane` (Configuration.lean L329) HIT as different incidence glue **not** namesake. `HasLines.card_le` L211 HIT as different de Bruijn–Erdős. **Not** BvN / Gale–Shapley (consumed). **Not** Jordan form (prime of this shortlist). Finite, one-wave Level A (order 2 none / order 3 affine `L_1, L_2`). **Unassigned this tick.**

Scout opened **no attack issues**. Formalist lands the prime after Director approval. Hold leftover until this prime lands. Cap is 2.

---

**Last updated:** 2026-09-10 (OPE-1326 Scout: catalog-audit shortlist jordan-canonical-form + orthogonal-latin-squares.)

## Shortlist (post OPE-21) — STALE JSON LEFTOVERS, NOT THIS MILL

These catalog JSON rows **fail the gap gate** this run (already Mathlib or not one-wave). Replaced, not reaffirmed. Do **not** re-prime.

1. **Frobenius (two coins)** — already `frobeniusNumber_pair`; process-fuel only
2. **Derangement formula** — already `numDerangements`
3. **Catalan recurrence** — already `catalan_eq_centralBinom_div`
**Alternate:** Bertrand — already `exists_prime_lt_and_le_two_mul`. vdW W(2,4) — Hales–Jewett infinitary already-in; finitary not one-wave.
**Do not re-open** EW a=5 path. Sum-free only as Lean cleanup, not “discovery.”

## Contributing

Problem Scout owns catalog maintenance:

1. `catalog/problems/<id>/STATEMENT.md` + `DOSSIER.json`  
2. Entry in `problems.json`  
3. Row in `docs/PROBLEM_LEDGER.md` when touched  
4. `python bin/mathforge score <id>`  
5. Director review before attack assignment
