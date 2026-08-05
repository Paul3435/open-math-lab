# Domain skill packs

Attack Lead and Formalist extend these. Each pack is a **lens**, not a silo — cross-review is mandatory.

| pack (dir) | lenses | typical artifacts |
|------------|--------|-------------------|
| `number-theory` | congruences, valuations, Bézout/Frobenius, asymptotics (careful) | lemmas, compute checks |
| `combinatorics` | counting, extremal, probabilistic method, partitions (general) | bounds, constructions |
| `partition-theory` | restricted partitions, Schur-type identities, generating fns | finite certs, Lean defs |
| `algebra` | groups/rings basics, polynomials | algebraic lemmas |
| `analysis` | inequalities, limits, elementary real/complex | ε-proof sketches → Lean |
| `topology` | basic point-set (use sparingly) | definitions, counterexamples |
| `logic` | foundations, encoding pitfalls | statement hygiene |
| `formalization` | Mathlib patterns, tactics, sorry policy — Formalist | Lean statements, sorry-free builds |
| `experimental` | OEIS, SAT/SMT, exhaustive finite, certificates — Attack Lead | verify scripts + witness files |
| `graph-theory` | labelings, colorings, canonical-form enumeration — Attack Lead (OPE-28) | spectral/color/graceful checks |

On-disk dirs today: `number-theory`, `combinatorics`, `partition-theory`, `algebra`,
`analysis`, `topology`, `logic`, `formalization`, `experimental`, `graph-theory` (last three added OPE-28).
README table matches disk.

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
| Mathlib gap must be grepped on local pin (OPE-25) | All packs: no score from dossier gap prose alone |
| Schur distinctness pin (OPE-21) | `partition-theory`: STATEMENT sides matter; check n=2 |

## Anti-patterns

- One pack “owns” a problem forever
- Skipping Adversarial Reviewer because Lean `sorry` was removed in the wrong theorem
- Confusing computational evidence with proof
- Scope creep (e.g. Frobenius with ≥3 denominations)
