# Domain skill packs (v0 stubs)

Attack Lead and Formalist extend these. Each pack is a **lens**, not a silo — cross-review is mandatory.

| pack | lenses | typical artifacts |
|------|--------|-------------------|
| `number-theory` | congruences, valuations, asymptotics, modular forms (careful) | lemmas, compute checks |
| `combinatorics` | counting, extremal, probabilistic method | bounds, constructions |
| `graph-theory` | connectivity, spectral, coloring | reductions, counterexample search |
| `analysis-lite` | inequalities, limits, elementary real/complex | ε-proof sketches → Lean |
| `formalization` | Mathlib patterns, typeclass, tactics | Lean statements, sorry-free goals |
| `experimental` | OEIS, SAT/SMT, exhaustive finite | scripts + certificates |

## Pack file convention

`skills/<pack>/SKILL.md` — when to use, anti-patterns, checklist before claiming progress.

## Anti-patterns

- One pack “owns” a problem forever
- Skipping Adversarial Reviewer because Lean `sorry` was removed in the wrong theorem
- Confusing computational evidence with proof
