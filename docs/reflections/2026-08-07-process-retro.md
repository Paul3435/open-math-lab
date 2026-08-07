# Reflection — Process Retro (2026-08-07)

Author: Reflection Coach
Scope: first-mathforge-sprint. Sources: `docs/PROBLEM_LEDGER.md`, `docs/BOARD_NOTES.md`,
`docs/CONSULTATION.md`, git log, Paperclip tickets (OPE-1…OPE-28).

## What's working

1. **Honest gates hold.** The board veto on OPE-12 (EW, wrong definition), the OPE-14
   rejections for `sorry`/false statements, and the OPE-25 correctness pass (frobenius /
   derangement / catalan were already in Mathlib) all fired. The adversarial-review /
   veto loop is the strongest asset in the lab — keep it mandatory, never let a fast
   "solved" skip it.
2. **Process corrections land as docs.** Every near-miss (EW definition, Mathlib-gap
   false claims, Scout-shortlist breach) became a durable rule in `PROBLEM_LEDGER.md`
   Lessons + `PORTFOLIO_PRINCIPLES.md`. The lab learns on paper, not just in memory.
3. **Workspace SoT discipline** (git repo vs. Paperclip managed mirror) is now followed.
4. **Scope integrity.** No one over-claimed: sum-free, Schur, Frobenius, caterpillars are
   all labelled `informal` / `heuristic` / process-fuel, not discoveries. That restraint
   is the correct default and should stay.

## What's slowing the lab down

1. **Model routing / no shared math brain raised.** All workers run DeepSeek over
   OpenRouter; only the Director runs grok. DeepSeek is slow on first token and on math;
   long Lean refactors (OPE-23's fiber-averaging proof) stall and get re-woken, losing
   the thread. This is the single biggest velocity drag. Options: (a) run the Formalist
   on grok for Lean-heavy steps, (b) shrink Lean steps into smaller, well-scoped tickets
   so a slow model doesn't hold a huge proof in one window.
2. **Ticket hygiene — wake discipline is good, handoff pins are not.** OPE-14 flips
   `blocked → in_progress → blocked` and OPE-23 sits in `backlog` with the Formalist's
   `ErdosSumFree.lean` untracked and not wired into `SumFree.lean`. The unblock action is
   named, but nothing drives the Formalist to actually run `lake build` and close it —
   "re-launch gate: zero sorries + SumFree.olean" never gets an owner with a deadline.
   Blocked tickets need a named owner **and** a check-wake, not just a "owner + action"
   note that waits for the next accidental wake.
3. **Lean velocity** is gated by (a) one-`sorry`-at-a-time grind under a slow model,
   (b) no shared `formalization` skill pack (noted in OPE-28, still not built), so every
   proof is re-approached from scratch. The Mathlib-gap lessons are encoded in the ledger
   but the *technique* (how to carve, which modules, sorry policy) is not in a skill.
4. **Review gate cadence.** Reviews are thorough but event-driven (wake on status change).
   There is no "review is due" schedule, so artifacts can sit in `blocked/in_review` for
   days waiting for a reviewer wake that nobody fires.

## Recommendations (top 3)

1. **Formalist on grok for Lean, or Lean-first small tickets.** Assign the OPE-23
   fiber-averaging formalization a dedicated wake on the stronger model with a hard scope
   (prime `p > max S`, middle-third interval, fiber averager — nothing else), and gate on
   `lake build` passing with zero `sorry` before marking done. Force the `ErdosSumFree`
   wiring in the same ticket so OPE-14 can unblock.
2. **Add a check-wake/date to every `blocked` and `backlog` ticket.** "Owner + action" is
   not enough — the Director should set a `monitorNextCheckAt` or schedule one wake so a
   ticket with a named unblocker actually gets resumed instead of decaying. Do this for
   OPE-23 and OPE-14 now.
3. **Land the OPE-28 skill-pack work (no new hire).** Specifically the
   `skills/formalization/SKILL.md` (Mathlib carving, `sorry` policy, ProofLab layout) — it
   directly attacks the Lean-velocity problem and costs nothing but one Attack-Lead/
   Formalist pass. Novelty pre-screen can fold into Problem Scout without a hire.

None of this needs a new role or new budget; it's routing + ticket mechanics + one skill
pack.