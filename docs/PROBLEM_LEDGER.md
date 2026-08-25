# Problem ledger — Open Math Lab

Source of truth for **which mathematical bets we have touched**, their disposition,
and pointers to artifacts. Update this file whenever a problem changes lifecycle
status. Catalog index: `catalog/problems.json`. Feasibility dossiers live under
`catalog/problems/<id>/` and/or `problems/<id>/`.

**Last updated:** 2026-08-25 (OPE-461 Formalist: ramsey-multicolor-r333 R(3,3,3)=17 BOTH bounds zero-sorry formalized)

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
| `ramsey-multicolor-r333` | graph theory / combinatorics | OPE-458 Scout prime; **OPE-461 Formalist** | **`formalized`** (formalize-only). Lean **zero-sorry** `ProofLab/RamseyMulticolor.lean`: `r333_gt_16` (GG F₂⁴ cert on Fin 16, `native_decide`); `r333_le_17` (pigeonhole deg≥6 + `ramsey33_clique_inside_finset` pullback); `r333_eq_17`. `lake env lean` EXIT=0; `lake build ProofLab` green. Axioms: propext/Quot.sound/Classical.choice/`Lean.ofReduceBool` only. **No novelty claim**. | Known classical (Greenwood–Gleason 1955); Mathlib gap (no multicolour Ramsey) | `problems/ramsey-multicolor-r333/STATEMENT.md`, Lean `ProofLab/RamseyMulticolor.lean`, `attacks/ramsey-multicolor-r333-20260825-ope461/`, cert `catalog/problems/ramsey-multicolor-r333/witness16_certificate.txt` |
| `erdos-woods` | elem. number theory | OPE-12 attack; OPE-15 hygiene veto; OPE-334 dossier refresh; **OPE-391 Formalist** | **formalize-only, Lean ZERO-sorry** (`ProofLab/ErdosWoodsCorrect.lean`): literature predicate open interval `(a,a+k)`; `isErdosWoodsWitness_16_2184` + `erdos_woods_16` via `interval_cases`+`native_decide` on 15 interiors; `lake env lean ProofLab/ErdosWoodsCorrect.lean` EXIT=0; `ProofLab.lean` EXIT=0. Vetoed wrong draft renamed `ErdosWoodsVetoed.lean` (not imported). Minimality of a=2184 **not** proven (literature/OEIS). **No novelty claim**. Prior OPE-12 claim remains vetoed. | Known (1980) | `problems/erdos-woods/`, Lean `ProofLab/ErdosWoodsCorrect.lean`, `attacks/erdos-woods-20260730-125506/` (+ BOARD_VETO) |
| `sum-free-subsets` | additive combinatorics | OPE-14 (board may still be open); children OPE-23/32/33/34 | **Classical Erdős (1965)** process demo. **Lean ZERO-sorry** (`sum_free_subset_bound`, wired via `erdos_sum_free_bound`; `lake env lean ProofLab/SumFree.lean` exit 0); Erdős computational verify 200/200. Adversarial veto (2026-07-31, 3 sorries + strategy mismatch) **lifted** by Adversarial Reviewer 2026-08-07. Known theorem — **`informal` / process fuel, not a discovery claim**. `lake build ProofLab` OK | Known theorem | `problems/sum-free-subsets/`, `attacks/sum-free-subsets-20260730-221216/`, Lean `ProofLab/SumFree.lean` (+ `ErdosSumFree.lean`) |
| `graceful-tree-conjecture` (bounded caterpillars n≤12) | graph theory | OPE-13 attack; OPE-18 review; OPE-20 re-review | **`heuristic`** bounded verify: 560 distinct non-iso caterpillars, 0 search failures after dedup. Family already known graceful for all n (Rosa/Golomb). **Not** full GTC; **not** Lean-gated | Sanity check, not new math | `problems/graceful-tree-conjecture/`, `attacks/graceful-tree-conjecture-20260731-094627/` |
| `schur-partition` | partitions | OPE-2 seed; OPE-25 shortlist; OPE-21 Director approve | **`shortlisted` prime** — STATEMENT pin 2026-08-04 (distinct parts ≡1,2 mod 3 = parts ≡±1 mod 6). Attack child filed after approval. Formalize-only | Known (1926); **genuine Mathlib gap** (OPE-25 grep) | `problems/schur-partition/` |
| `frobenius-coin-problem` | number theory | OPE-21/22; OPE-25 | **process-fuel** (not gap prime). Mathlib already has `frobeniusNumber_pair`. Level A/B artifacts under attack dir + `ProofLab/Frobenius.lean` | Known textbook; already-in-Mathlib | `problems/frobenius-coin-problem/`, `attacks/frobenius-coin-problem-20260804-222513/` |
| `ramsey-r33` | graph theory / combinatorics | OPE-40 scout keep-fresh; OPE-43 shortlist+prime; OPE-44 attack | **`formalized`** (formalize-only). Lean **zero-sorry**, `lake build ProofLab` green: `ramsey33_eq_6`, `ramsey34_eq_9`, `ramsey44_eq_18` (`ProofLab/Ramsey.lean`). Hand pigeonhole R(3,3)≤6; degree-parity R(3,4)≤9; recurrence R(4,4)≤18; lower bounds via C5 / 8-vtx witness / Paley-17. Default **no claim**. Board 2026-08-24: independent `lake env lean ProofLab/Ramsey.lean` EXIT=0. | Known classical; **genuine Mathlib gap** (no Ramsey theorem in v4.10.0) | `problems/ramsey-r33/`, Lean `ProofLab/Ramsey.lean` |
| `erdos-szekeres-monotone` | combinatorics / order theory | OPE-430 scout prime; **OPE-433 attack**; OPE-437 re-verify; OPE-438 adversarial APPROVE (PR #29) | **CLOSED — formalize-only, Lean ZERO-sorry.** Full finite ES monotone theorem: every sequence on a linear order of length ≥ (r−1)(s−1)+1 has a weakly increasing subsequence of length r or weakly decreasing of length s (`ProofLab/ErdosSzekeres.lean`: `erdosSzekeres_monotone`; incLen/decLen pigeonhole; weak mono + `List.Sorted` pin). Do not re-prime this scope. | Known (1935); genuine gap at attack time (only infinitary lemma upstream) | `problems/erdos-szekeres-monotone/`, `attacks/erdos-szekeres-monotone-20260825/`, Lean `ProofLab/ErdosSzekeres.lean`, PR #29 |
| `van-der-waerden-w24` | additive combinatorics | OPE-430 bench; Director OPE-454; **OPE-455 Attack Lead**; OPE-456 adversarial APPROVE (PR #33) | **PARTIAL ladder closed:** STATEMENT pinned (HasMono4: exists a d, 0<d, a+3d<n, all four equal); `vdw24_gt_34` via witness34 colouring `0010001110100100011101001000111011` on Fin 34, native_decide, zero sorry. **Upper W(2,4)≤35 OPEN** (Chvátal 1979 computer-assisted; no hand certificate named → only eligible as bench with concrete case-split strategy per OPE-458 commission). No novelty/claim. | Known classical; Mathlib finitary VdW TODO (HalesJewett.lean L53) | `problems/van-der-waerden-w24/`, `attacks/van-der-waerden-w24-20260825-ope455/`, Lean `ProofLab/VanDerWaerden.lean`, PR #33 |
| `van-der-waerden-w23` | additive combinatorics | OPE-45 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/VanDerWaerden.lean`): `vdw_le_9` (every 2-colouring of `Fin 9` has a mono 3-AP, `native_decide`) + `vdw_gt_8` (witness `11001100` on `Fin 8` with none). ⇒ W(2,3)=9. `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/VanDerWaerden.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — finitary VdW still an explicit TODO in the pinned `Mathlib/Combinatorics/HalesJewett.lean` (~L51) | Known classical; genuine Mathlib TODO (HalesJewett.lean) | `proofs/lean-project/ProofLab/VanDerWaerden.lean`, `problems/van-der-waerden-w23/` |
| `schur-number` | additive combinatorics | OPE-46 (folded into OPE-51) | **formalize-only, Lean ZERO-sorry** (`ProofLab/SchurNumber.lean`): `schur2_lower`/`schur2_le_4` ⇒ S(2)=4 (classes {1,4}/{2,3}, least-forcing N=5); `schur3_lower`/`schur3_le_13` ⇒ S(3)=13 (classes {1,4,7,10,13}/{2,3,11,12}/{5,6,8,9}, least-forcing N=14). Convention pinned (x=y allowed, standard). `lake env lean` exit 0, zero `sorry`. **Gate re-verified by Scout 2026-08-22 (OPE-334)**: independent `lake env lean ProofLab/SchurNumber.lean` exit 0 against pinned Lean 4.10.0 + Mathlib v4.10.0 snapshot; grep confirms zero real `sorry`/`admit`/`axiom`; gap re-confirmed — no SchurNumber/additive-Schur content anywhere in the v4.10.0 Mathlib pin | Known classical; genuine Mathlib gap (no SchurNumber content) | `proofs/lean-project/ProofLab/SchurNumber.lean`, `problems/schur-number/` |

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
| **`schur-partition`** | **`shortlisted` → done (OPE-26 attack complete)** | partition theory | OPE-25 recommended; Director approved; STATEMENT pinned (distinct ≡1,2 mod 3 vs parts ≡±1 mod 6). **OPE-26** attack completed 2026-08-04 — Level A cert (N≤1000, DP+brute force agree) + Level B Lean sorry-free small-n (`ProofLab/Schur.lean`). |
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
1. **`ramsey-r35` R(3,5)=14 — RECOMMENDED PRIME** (86). Direct infrastructure carry-over from
   merged PR #18 (`ProofLab/Ramsey.lean` vocabulary); upper bound hand degree-counting (one notch
   above the OPE-44 R(3,4) argument); lower bound via offline-certified 13-vtx witness checked in
   Lean by decidable clique enumeration. Needs STATEMENT.md pin before attack.
2. **`happy-ending-es3` ES(3)=5** (78). Highest infra risk (orientation/order-type glue is new);
   ES(4)=9 stretch only.
3. *(bench)* `schur-partition` full statement (parts ≡ ±1 mod 6) remains a fallback gap if the
   Director prefers number-theory continuity over graph-theory carry-over.

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
