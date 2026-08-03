# Portfolio Principles - Open Math Lab (Director)

Owner: Research Director. Ratified by Board (Paul). Applies to all problem bets,
attacks, catalog entry, and claims.

## Feasibility-first
- A problem is a bet, not a mission. Only admit bets that are: formalizable in Lean 4
  (Mathlib), partial-progress friendly, budget-capped, and clearly separated from crackpot
  numerology or unbounded "AI solves it tonight" claims.
- The Problem Scout feasibility dossier is the gate. No dossier scored pass -> no attack.

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