# Domain skill packs

Attack Lead and Formalist extend these. Each pack is a **lens**, not a silo — cross-review is mandatory.

| pack (dir) | lenses | typical artifacts |
|------------|--------|-------------------|
| `number-theory` | congruences, valuations, Bézout/Frobenius, asymptotics (careful) | lemmas, compute checks |
| `combinatorics` | counting, extremal, probabilistic method, partitions | bounds, constructions |
| `algebra` | groups/rings basics, polynomials | algebraic lemmas |
| `analysis` | inequalities, limits, elementary real/complex | ε-proof sketches → Lean |
| `topology` | basic point-set (use sparingly) | definitions, counterexamples |
| `logic` | foundations, encoding pitfalls | statement hygiene |
| *(planned)* `graph-theory` | currently fold into `combinatorics` until pack split | graceful / trees work used combinatorics+scripts |
| *(planned)* `formalization` | Mathlib patterns — use Formalist role + `docs/LEAN_PLAN.md` | Lean statements |
| *(planned)* `experimental` | OEIS, SAT/SMT — fold into attack scripts for now | certificates |

On-disk dirs today: `number-theory`, `combinatorics`, `algebra`, `analysis`, `topology`, `logic`.
README table historically listed packs not yet created; prefer real dirs.

## Pack file convention

`skills/<pack>/SKILL.md` — when to use, anti-patterns, checklist before claiming progress.

## Lab lessons → pack hygiene (OPE-21)

| Lesson | Pack impact |
|--------|-------------|
| Pin literature definitions before “solved” (EW veto) | All packs: STATEMENT.md citation mandatory |
| Known theorems ≠ discoveries | Label `informal`/`heuristic`; residual risks |
| Iso-class vs representation counts (graceful) | Combinatorics: enumerate canonical forms + cross-check |
| Compute pass + Lean `sorry` = review block | Number-theory/combinatorics: separate Level A/B/C success |
| Two-coin Frobenius in sprint | Number-theory: Bézout + non-representability checklist |

## Anti-patterns

- One pack “owns” a problem forever
- Skipping Adversarial Reviewer because Lean `sorry` was removed in the wrong theorem
- Confusing computational evidence with proof
- Scope creep (e.g. Frobenius with ≥3 denominations)
