# Krenn–Gu monochromatic quantum graphs (open; live cash)

**id:** `krenn-gu`
**ticket:** OPE-1028 Scout RECOMMENDED PRIME (board prize-money hunt)
**expected:** `open` — **no prize claim this ticket; no novelty claim until a software-checked
counterexample or a refereed proof exists**
**cash:** €3,000 — Mario Krenn and Dominik Leitner (personal offer, still advertised
2026-09-06). First proof *or* counterexample. Proof must appear in a respected
peer-reviewed journal; a counterexample must be confirmable (e.g. by software).
No deadline. PPL 007 (verified open, last checked 2026-07-26).
Sponsor page: https://mariokrenn.wordpress.com/graph-theory-question/
MathOverflow 311325 (24 Sep 2018). Mixon blog 2021-01-18.

## What the prize is for

A bi-colored complex-weighted graph on `n` vertices with `d` colors assigns to
each edge a complex weight and an ordered pair of colors from `{1,…,d}`.
Each perfect matching induces an inherited vertex coloring. The *weight* of a
vertex coloring is the sum, over perfect matchings that induce it, of the
product of edge weights.

**Question (Krenn):** for which even `n` and integers `d` does there exist such
a weighting so that every *monochromatic* inherited coloring has weight `1`
and every other coloring has weight `0`?

**Conjecture (Krenn–Gu, informal):** except for `K_4` (where `d=3` is possible),
no such graph exists for `n>4` and `d>2`. A counterexample is any even `n≥6`
with `d≥3` (or `n=4` with `d≥4`, now ruled out).

Known finite landscape (sponsor page, 2026-07-23 news):

- Positive examples: `C_{2k}` with `d=2`, and `K_4` with `d≤3`.
- Positive-real weights: Bogdanov — those are the only solutions.
- `n=4`, `d≥4`: no solution (Kevin M. 2023; AlphaProof Nexus `d≥n` for even `n`, May 2026).
- `deg≤3`: conjecture true (Chandran–Gajjala–Illickan 2024).
- Simple graphs: several `d` upper bounds (Chandran–Gajjala).
- Reported numerical window: `C(4)=3`, `C(6)=2`, `2≤C(8)≤3`.

RSA Factoring Challenge prizes **ended 2007** — not this id.
Millennium / Beal $1M items are **out of v1** as a solve (listed on the issue
comment only).

## Why this is the prize-money prime (not a classical re-prime)

This is **open**. Value is a **machine-checkable lemma on a live bounty**, not a
Mathlib restatement of a textbook theorem.

Mathlib v4.10.0 pin `a719ba5c3115`:

- HIT as infra (USE, never cite as this gap): `SimpleGraph.Subgraph.IsMatching`
  (`Combinatorics/SimpleGraph/Matching.lean`), `Complex`, `Fin n`.
- ZERO `Krenn` / `EqSystemN` / `inherited vertex` / `monochromatic quantum` /
  GHZ-graph matching equations under `Mathlib/` + `Archive/` this run.

**Not** König `ν=τ` (consumed). **Not** Ramsey r33/r35/r333 / Erdős first-moment
(consumed). **Not** Friendship / Moore / expander-mixing (#98). **Not**
frobenius-real-division / noether-normalization (OPE-886 mill, consumed as
formalize-only). **Not** matching-index `μ(G)` full characterisation
(Chandran–Gajjala–Illickan is literature, not this id's namesake). **Not**
DeepMind `formal-conjectures` import.

Do **not** describe an attack as collecting €3,000. Do **not** email Krenn.
Board is the only external-claim authority (`docs/CLAIM_POLICY.md`).

## Pinned convention (exact)

**v1 is a finite, checkable slice — not the namesake prize.**

Encoding sketch (Formalist may refine; pin the *shape*):

- Even `N ≥ 2`, colors `D ≥ 1`, weights `W` on bicolored edges with values in `ℂ`
  (or a decidable subring `ℤ` / `{−1,0,1}` for search).
- `pmSum ι` = sum over perfect matchings of the product of induced edge weights
  at vertex coloring `ι : Fin N → Fin D`.
- `EqSystem N D W` iff `pmSum ι = 1` when `ι` is constant and `= 0` otherwise.

**Level A (not labelled Krenn–Gu):** encoding compiles; exhibit a known
*positive* witness (`N=4,D=2` or `N=4,D=3` on `K_4`, and/or even cycle `D=2`).
Zero `sorry`. `#print axioms` = `propext` / `Classical.choice` / `Quot.sound`
and, if a finite `native_decide` witness is used, `Lean.ofReduceBool` only.

**Level B (still not the prize):** exactly one of:

1. a published finite *nonexistence* that is not a copy-paste of AlphaProof
   `d≥N` / Kevin M. `n=4,d≥4` — e.g. a self-contained `¬ EqSystem 6 3 W` over
   a stated coefficient ring, **or**
2. a bounded search log for `(N,D)=(8,3)` with `attacks/.../STATUS.json` +
   `RESULTS.md` (heuristic / SAT / Gröbner). Honest partial allowed.

Cap two levels. Namesake `∀ even N≥6, ∀ D≥3, ¬ ∃ W, EqSystem N D W` is **out
of v1**. Do **not** `sorry` it.

## Landmines

1. Do **not** import `Archive.*` or `google-deepmind/formal-conjectures`.
2. Do **not** re-prove AlphaProof Nexus `d≥n` (May 2026) or Kevin M. `n=4,d≥4`
   as this id's namesake.
3. Do **not** re-prove Bogdanov (positive real weights) as namesake.
4. Do **not** claim the €3,000 / Best-Paper €1,000 (deadline End of August 2024
   on the sponsor page — treat Best-Paper as **not live** unless Director
   re-confirms).
5. Do **not** re-prime frobenius-real-division / noether-normalization /
   expander-mixing / mason-stothers / Ramsey consumed mill.
6. Leave OPE-403 alone.
7. Unrestricted complex `(8,3)` may explode — timebox; fall back to encoding +
   a smaller ring / smaller `N`.

## Sources

- Mario Krenn, sponsor page (reward + special cases + 2026-07-23 Lean news)
- MathOverflow 311325 (Krenn, 2018-09-24)
- Dustin Mixon, “A graph coloring problem from quantum physics (with prizes!)”, 2021-01-18
- Prize Problem Ledger PPL 007, https://prizeproblems.org/problems/007/
- Chandran–Gajjala–Illickan, arXiv:2407.00303 (deg ≤ 3)
- Krenn–Gu–Zeilinger, PRL 119, 240403 (2017) — physics motivation, not the v1 pin
