# OPE-28 — Consultation: Research Pipeline Gap Review

Author: Research Director
Date: 2026-08-05
Status: Proposals — awaiting board input
Scope: skill-pack hygiene, candidate hires, process gates

## 1. Current pipeline (as built)

```
Board → Research Director (portfolio, refuse crackpottery, ticket split)
 ├─ Problem Scout (researcher)  — catalogs, feasibility dossiers, novelty triage
 ├─ Formalist (Lean)            — Lean statements + verify; toolchain installed (OPE-17)
 ├─ Attack Lead                 — strategies + skills/<pack>/, computational runs
 └─ Adversarial Reviewer        — breaks claims; vetoes rubber-stamp
    (+ built-ins Summarizer / Reflection — leave unless configured)
```

Roles present: 4 core workers (Scout, Formalist, Attack Lead, Adversarial Reviewer) under the Research Director, plus 2 built-ins. All workers run DeepSeek via OpenRouter; only the Director uses grok-4.5 (xAI sub).

Report: pipeline is mid first-mathforge-sprint. Several targets turned out to be *classical* results (sum-free, Schur partitions, Frobenius 2-denom) rather than open problems. Lean toolchain installed (OPE-17). No external claims without board — good.

## 2. Concrete gaps found

### GAP-1 — Skill-pack catalog is stale / contradicts on-disk reality
- `skills/README.md` advertises packs: `number-theory, combinatorics, graph-theory, analysis-lite, formalization, experimental`.
- **On disk only:** `algebra, analysis, combinatorics, logic, number-theory, topology`.
- So four advertised packs (**graph-theory, analysis-lite, formalization, experimental**) have **no SKILL.md / folder**, while (algebra, analysis, logic, topology) exist but are **not documented** in the table at all.

**Impact:** the point of skill packs was "one specialist lens per attack". The table (single source of truth) no longer matches disk, and agents literally cannot load a `formalization` or `experimental` pack because they don't exist.

### GAP-2 — Formalization skill pack is missing entirely
Lean is installed and `lake build` is green (OPE-17), yet there is **no SKILL.md defining how Formalist carves an attack into Lean/Mathlib** — which Mathlib modules, proof conventions, `sorry` policy, statement patterns, or the ProofLab layout in `proofs/lean-project/`. Every Lean proof (Basic/Erdos/Schur/SumFree) is re-approached from scratch with no shared procedure.

### GAP-3 — Experimental / compute pack missing (OEIS / SAT / SMT / certificates)
- Attack artifacts are mostly Python enumerators (`verify_*.py`) with no standard for small-case enumeration, OEIS lookup, SAT/SMT routes, reproducible certificates, or when "compute heuristic" vs "proof". This is also the stage that could have caught "this is a known theorem" earlier.

### GAP-4 — No novelty / literature pre-screen
- Repeatedly, problems Scout selected turned out to be known results (Erdős sum-free, Schur partitions, Frobenius two-coin, Bertrand's postulate computational). The catalog skews toward textbook results rather than open problems. A dedicated **novelty / prior-art screen before an attack is funded** would (a) stop re-deriving famous theorems and (b) tag candidates `formalize-only` vs `open` early, rather than late.

### GAP-5 — Graph-theory pack gap (minor)
- Graceful-caterpillar work (OPE-13) had no graph-theory pack, even though the README advertises one. Graph problems will recur; cost to add a pack is low.

## 3. Recommendations

### 3.1 Add & sync skill packs (no new hire)
1. `skills/formalization/SKILL.md` (Mathlib patterns, tactics, sorry policy) → Formalist.
2. `skills/experimental/SKILL.md` (OEIS/SAT/SMT/brute-force + compute-vs-proof policy) → Attack Lead.
3. `skills/graph-theory/SKILL.md` → Attack Lead.
4. `analysis-lite` slim stub + document existing packs (algebra/analysis/topology/number-theory/logic) so the table matches disk.
5. Reconcile `skills/README.md` table with what actually exists on disk (one column per present pack).

All agents have `canCreateSkills: true`, so the workers can author these packs themselves; board merges the resulting PRs.

### 3.2 Optional new hire (board decision) — Novelty Reviewer (lit-novelty)
Rationale: the single recurring failure is attacking known/classical problems. A junior `researcher` that runs a novelty screen *before* funding an attack sets expected-class/count and tags `known` / `formalize-only` / `open` — directly addressing GAP-4.
- Cost: small (same deepseek budget as Attack Lead ~$40/mo, shared quota).
- Cheaper alternative (recommended first): fold a **novelty-scan sub-step into Problem Scout** + tag column in the catalog — nearly free.
Director recommends **no-hire first**; hire only if novelty-screening becomes a recurring bottleneck.

### 3.3 Process changes (adopt now, no board)
- Add `expected`/gap tag (`known-classical` or `open`) to problem catalog so later attacks don't re-fund a settled theorem.
- Route formal proofs through Formalist's new pack; Reviewer gates before any link to proofs/.

## 4. Budget / model note
All workers are DeepSeek (OpenRouter). If Lean `sorry`-gap review ever needs a stronger semantic check, a single xAI grok-4.5 reviewer could be considered — not urgent, flagging for the board. Whole-org budget is small.

## 5. Recommended disposition to board

**Verdict:** No new agent needed — the gaps are skill/process, not org shape or headcount. Core fix: add `formalization` + `experimental` + `graph-theory` packs and reconcile README with disk; add a novelty-screen sub-step before funded attacks; tag catalog for expected result. Hire a Novelty Reviewer only if the novelty gate becomes the bottleneck after the no-hire fix.

**Ask board to:**
- [x] Approve pack-addition tickets (formalization, experimental, graph-theory). — **APPROVED 2026-08-05**
- [x] Decide Novelty Reviewer: hire later / no (director: no). — **DECIDED no hire; fold novelty-screen into Scout**
- [x] Approve novelty-screen and catalog-tagging process change. — **APPROVED 2026-08-05**

## 6b. Board decisions & execution (2026-08-05, interaction 707b9c26)

Interaction `ask_user_questions` answered by board:
1. **Skill packs** — `approve` → add all 3 packs.
2. **Novelty Reviewer** — `no_first` → fold novelty-screen into Scout (no hire).
3. **Process change** — `approve` → adopt novelty-screen + catalog `expected` tags.

Execution (branch `ope/28-consultation-exec`, PR #8):
- Added `skills/formalization/SKILL.md`, `skills/experimental/SKILL.md`, `skills/graph-theory/SKILL.md`.
- Reconcilement `skills/README.md` table now matches on-disk dirs (no more planned/ stubs).
- Scout role updated (`docs/roles/problem-scout.md`) with a novelty pre-screen gate.
- `catalog/problems.json` v1.2: every problem tagged `expected` (`known-classical` / `formalize-only` / `open`) + `expected_taxonomy` enum documented; `catalog/README.md` novelty-tagging policy.
- No Novelty Reviewer created (director recommendation upheld).