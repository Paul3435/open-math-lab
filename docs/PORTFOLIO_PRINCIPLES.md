# Portfolio Principles - Open Math Lab (Director)

Owner: Research Director. Ratified by Board (Paul). Applies to all problem bets,
attacks, catalog entry, and claims.

## Feasibility-first
- A problem is a bet, not a mission. Only admit bets that are: formalizable in Lean 4
  (Mathlib), partial-progress friendly, budget-capped, and clearly separated from crackpot
  numerology or unbounded "AI solves it tonight" claims.
- The Problem Scout feasibility dossier is the gate. No dossier scored pass -> no attack.

## Scout shortlist gate (new investigations)
- **Problem Scout owns candidate generation and shortlists.** Director does **not**
  pick a "prime" attack solely by reading `catalog/problems.json` scores.
- Before opening a **new** attack issue on a problem not already under attack, require
  a **fresh Scout shortlist run** (Paperclip issue assigned to Problem Scout) that:
  1. Re-scores or reaffirms dossiers for ≤3 candidates,
  2. Names an explicit recommended prime (or "none"),
  3. Notes literature/definition risks (see OPE-12/OPE-15),
  4. Updates `docs/PROBLEM_LEDGER.md` untouched/shortlist tables if needed.
- Director may only **approve / reject / order** that shortlist, then assign Attack Lead.
- **Exception (board-only):** board names the problem explicitly on the ticket.
- **Not an exception:** "dossier exists from months ago" or "highest score in JSON."
  Stale catalog rows are inputs to Scout, not a substitute for a Scout run.
- **Process breach (OPE-21 lesson):** Director shortlisted `frobenius-coin-problem` and
  opened OPE-22 from catalog score 90 without a concurrent Scout shortlist ticket.
  Corrective path: keep OPE-22 as provisional process fuel; require Scout ratification
  / next-shortlist before the *next* prime; document the breach in the ledger.

## Reject crackpottery
- Automatic evidence: numerology, unexplained constants, appeals to authority over argument,
  conspiracy theories about the establishment, unbounded token burn. Any such claim gets an
  immediate Adversarial-Reviewer/board vetO. Document dead ends honestly instead of chasing.

## Lean-gated claims
- A fluent English "proof" is NOT a proof. Positive claims require EITHER:
  1. a clean Lean 4 + Mathlib build checking the theorem, OR
  2. Adversarial Reviewer written approval plus an explicit, non-empty board-facing
     residual-risk list.
- Anything else is status: informal or status: heuristic. Failed attacks are first-class
  output when they yield a dead-end map and an updated feasibility score.

## No claim by default
- Default recommendation is NO CLAIM. Board (Paul) is the only authority for any external
  communication of results. Claim packets go through `mathforge claim prepare` and are
  board-reviewed only.

## Wake discipline
- One specialist wake at a time on the shared model license unless the board raises
  concurrency. Kill bad bets early. Prefer shipping the tool + process before heroic
  proof searches.