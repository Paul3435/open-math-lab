# Graph Theory Skill Pack

## Purpose

Attack strategies for problems on graphs: labelings, colorings, matchings, paths/connectivity,
spectral and extremal arguments, plus canonical-form enumeration for isomorphism-sensitive
checks. Owned by the **Attack Lead** (previously folded into combinatorics; split into its own
pack under OPE-28).

## When to use this pack

- The target is stated on graphs, trees, or general discrete structures with adjacency/symmetry
  (e.g. graceful labelings, chromatic/polynomial invariants, Ramsey-type, matching bounds).
- You are enumerating graph families and must distinguish non-isomorphic representatives
  (graceful-caterpillar lesson: enumerate canonical forms, cross-check with a second method).
- A graph-theoretic reduction of a harder problem into checkable lemmas is likely.

## Core strategies

1. **Labelings & coverings**: graceful, harmonious, edge/vertex colorings, bandwith/layout;
   constructive labeling + small-case witness search.
2. **Trees & bipartite contracts**: use caterpillar/spine structure, AHU canonical labeling for
   isomorphism-free enumeration.
3. **Connectivity paths/flows**: matchings (Hall), Menger-type reductions, independent sets.
4. **Spectral / matrix**: adjacency/Laplacian eigenvectors for bounds; use sparingly — prefer
   combinatorial when possible.
5. **Extremal**: Turán, Ramsey, degeneracy arguments; balance with computational check.
6. **Reduction to algorithms**: model decision checks as SAT/SAT/SMT or search across a
   bounded family, then hand computational evidence to the Experimental pack for
   certification and the formal gate.

## Anti-patterns

- Counting raw objects instead of canonical forms → inflated / wrong class counts (lab lesson).
- Claiming a general graph conjecture from verified bounds (bounded n is `heuristic`, not a
  proof) — e.g. Graceful Tree Conjecture is NOT proven by n≤12 runs.
- Omitting a canonical-form cross-check when a count is load-bearing.
- Mixing known results with novelty: if the family is already proven graceful for all n (Rosa
  1967/Golomb), report it as a sanity check, not a discovery.

## Checklist before claiming progress

- [ ] Numeric/structural result re-checked on canonical forms, not raw objects
- [ ] Bounded runs labeled `heuristic`; general claims gated on a Lean build or Reviewer approval
- [ ] Known theorem cited (novelty screen); not re-funded as novel
- [ ] Enumerator/verify script committed under `attacks/<attack>/` with reproducible input

## Maintenance

- Capture repeated canonical-labeling helpers (AHU tree isomorphism, caterpillar spine
  generation) as reusable modules here.