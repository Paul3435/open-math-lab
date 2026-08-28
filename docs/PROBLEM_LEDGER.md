# Problem ledger — Open Math Lab

Source of truth for **which mathematical bets we have touched**, their disposition,
and pointers to artifacts. Update this file whenever a problem changes lifecycle
status. Catalog index: `catalog/problems.json`. Feasibility dossiers live under
`catalog/problems/<id>/` and/or `problems/<id>/`.

**Last updated:** 2026-08-25 (OPE-433 erdos-szekeres-monotone formalized; OPE-430 scout shortlist; OPE-410 ES(3)=5; OPE-455 W(2,4)>34; OPE-393 R(3,5)=14)

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
| `erdos-woods` | elem. number theory | OPE-12 attack; OPE-15 hygiene veto; OPE-334 dossier refresh; **OPE-391 Formalist** | **formalize-only, Lean ZERO-sorry** (`ProofLab/ErdosWoodsCorrect.lean`): literature predicate open interval `(a,a+k)`; `isErdosWoodsWitness_16_2184` + `erdos_woods_16` via `interval_cases`+`native_decide` on 15 interiors; `lake env lean ProofLab/ErdosWoodsCorrect.lean` EXIT=0; `ProofLab.lean` EXIT=0. Vetoed wrong draft renamed `ErdosWoodsVetoed.lean` (not imported). Minimality of a=2184 **not** proven (literature/OEIS). **No novelty claim**. Prior OPE-12 claim remains vetoed. | Known (1980) | `problems/erdos-woods/`, Lean `ProofLab/ErdosWoodsCorrect.lean`, `attacks/erdos-woods-20260730-125506/` (+ BOARD_VETO) |
| `sum-free-subsets` | additive combinatorics | OPE-14 (board may still be open); children OPE-23/32/33/34 | **Classical Erdős (1965)** process demo. **Lean ZERO-sorry** (`sum_free_subset_bound`, wired via `erdos_sum_free_bound`; `lake env lean ProofLab/SumFree.lean` exit 0); Erdős computational verify 200/200. Adversarial veto (2026-07-31, 3 sorries + strategy mismatch) **lifted** by Adversarial Reviewer 2026-08-07. Known theorem — **`informal` / process fuel, not a discovery claim**. `lake build ProofLab` OK | Known theorem | `problems/sum-free-subsets/`, `attacks/sum-free-subsets-20260730-221216/`, Lean `ProofLab/SumFree.lean` (+ `ErdosSumFree.lean`) |
| `graceful-tree-conjecture` (bounded caterpillars n≤12) | graph theory | OPE-13 attack; OPE-18 review; OPE-20 re-review | **`heuristic`** bounded verify: 560 distinct non-iso caterpillars, 0 search failures after dedup. Family already known graceful for all n (Rosa/Golomb). **Not** full GTC; **not** Lean-gated | Sanity check, not new math | `problems/graceful-tree-conjecture/`, `attacks/graceful-tree-conjecture-20260731-094627/` |
| `schur-partition` | partitions | OPE-2 seed; OPE-25 shortlist; OPE-21 Director approve; OPE-26 Level A+B; **OPE-424 partial ladder** | **`heuristic`** — OPE-424 closed as a **partial ladder** (finite certs n≤24 computable / n≤12 Finset + bridge; zero sorry; PR #27) with Adversarial approval in OPE-426. Full ∀n A(n)=B(n) remains OPEN — finite-certificate scope closed, do not re-prime. STATEMENT pin 2026-08-04 held (distinct parts ≡1,2 mod 3 = parts ≡±1 mod 6). Formalize-only | Known (1926); **genuine Mathlib gap** (OPE-25 + OPE-430 grep) | `problems/schur-partition/`, `ProofLab/Schur.lean`, PR #27 |
| `frobenius-coin-problem` | number theory | OPE-21/22; OPE-25 | **process-fuel** (not gap prime). Mathlib already has `frobeniusNumber_pair`. Level A/B artifacts under attack dir + `ProofLab/Frobenius.lean` | Known textbook; already-in-Mathlib | `problems/frobenius-coin-problem/`, `attacks/frobenius-coin-problem-20260804-222513/` |
| `ramsey-r35` | graph theory / combinatorics | OPE-390 scout prime; **OPE-393** attack | **`formalized`** (formalize-only). Lean **zero-sorry** `ramsey35_eq_14` in `ProofLab/Ramsey.lean`: lower circulant C13({±1,±5}) `native_decide`; upper `R(2,5)+R(3,4)=5+9` via `ramsey_two_right` + `ramsey34_le_9` + `ramseyUpper_add`. `lake build ProofLab` green. Default **no claim**. | Known classical (Greenwood–Gleason 1955); Mathlib gap remains for upstream packaging | `problems/ramsey-r35/`, Lean `ProofLab/Ramsey.lean`, `attacks/ramsey-r35-20260824/` |
| `ramsey-r33` | graph theory / combinatorics | OPE-40 scout keep-fresh; OPE-43 shortlist+prime; OPE-44 attack | **`formalized`** (formalize-only). Lean **zero-sorry**, `lake build ProofLab` green: `ramsey33_eq_6`, `ramsey34_eq_9`, `ramsey44_eq_18` (`ProofLab/Ramsey.lean`). Hand pigeonhole R(3,3)≤6; degree-parity R(3,4)≤9; recurrence R(4,4)≤18; lower bounds via C5 / 8-vtx witness / Paley-17. Default **no claim**. Board 2026-08-24: independent `lake env lean ProofLab/Ramsey.lean` EXIT=0. | Known classical; **genuine Mathlib gap** (no Ramsey theorem in v4.10.0) | `problems/ramsey-r33/`, Lean `ProofLab/Ramsey.lean` |
| `ramsey-r35` | graph theory / combinatorics | OPE-390 scout; OPE-393 attack; OPE-410 finish | **`formalized`** (formalize-only). R(3,5)=14 Lean **zero-sorry**: upper bound hand degree-counting; lower bound 13-vtx witness via decidable clique check. Gate-approved PRs #22/#23/#24/#25. Known-classical, no claim. | Known classical; genuine Mathlib gap (no Ramsey theorem in v4.10.0) | `problems/ramsey-r35/`, `ProofLab/Ramsey*.lean` |
| `happy-ending-es3` | discrete geometry | OPE-403 attack; OPE-410 finish | **`formalized`** (formalize-only). ES(3)=5: any 5 points in general position contain a convex 4-gon. Lean **zero-sorry** with new orientation/order-type plumbing (reusable infra). ES(4)=9 stretch **not** attacked. Gate-approved PRs #23/#24/#25. Known-classical, no claim. | Known classical (Erdős–Szekeres 1935); genuine Mathlib gap (no happyEnding/ErdosSzekeres content v4.10.0) | `problems/happy-ending-es3/`, `ProofLab/` ES files |
| `van-der-waerden-w23` | additive combinatorics | OPE-45 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/VanDerWaerden.lean`): `vdw_le_9` (every 2-colouring of `Fin 9` has a mono 3-AP, `native_decide`) + `vdw_gt_8` (witness `11001100` on `Fin 8` with none). ⇒ W(2,3)=9. `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/VanDerWaerden.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — finitary VdW still an explicit TODO in the pinned `Mathlib/Combinatorics/HalesJewett.lean` (~L51) | Known classical; genuine Mathlib TODO (HalesJewett.lean) | `proofs/lean-project/ProofLab/VanDerWaerden.lean`, `problems/van-der-waerden-w23/` |
| `van-der-waerden-w24` | additive combinatorics | Scout OPE-430 bench; Director OPE-454; **OPE-455 Attack Lead** | **PARTIAL ladder (formalize-only)**: STATEMENT pinned; Lean `HasMono4` + `vdw24_gt_34` (`¬ HasMono4 witness34` on Fin 34 colouring `0010001110100100011101001000111011`, `native_decide`) ⇒ **W(2,4)>34**, zero sorry. **Upper `W(2,4)≤35` NOT proved** (Chvátal 1979 computer-assisted; no brute force in Lean; timebox). Exact equality open in Lean. `lake env lean` + `lake build ProofLab` green. **No novelty / no claim.** | Known classical; Mathlib finitary VdW TODO | `problems/van-der-waerden-w24/`, `attacks/van-der-waerden-w24-20260825-ope455/`, Lean `ProofLab/VanDerWaerden.lean` |
| `schur-number` | additive combinatorics | OPE-46 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/SchurNumber.lean`): `schur2_lower`/`schur2_le_4` ⇒ S(2)=4 (classes {1,4}/{2,3}, least-forcing N=5); `schur3_lower`/`schur3_le_13` ⇒ S(3)=13 (classes {1,4,7,10,13}/{2,3,11,12}/{5,6,8,9}, least-forcing N=14). Convention pinned (x=y allowed, standard). `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/SchurNumber.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — no SchurNumber/additive-Schur content anywhere in the v4.10.0 Mathlib pin | Known classical; genuine Mathlib gap (no SchurNumber content) | `proofs/lean-project/ProofLab/SchurNumber.lean`, `problems/schur-number/` |
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
