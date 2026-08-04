# Partition Theory Skill Pack

## Purpose

Lens for integer partitions, generating-function identities, and classical partition theorems (formalize-only and compute certificates).

## When to use

- Partition counts with congruence restrictions on parts
- Distinct-parts vs unrestricted-parts comparisons
- q-series / generating-function sketches heading to Lean
- Mathlib `Nat.Partition` (or successor modules) formalization gaps

## Active lab bet

**`schur-partition`** (OPE-25 prime, Director-approved on OPE-21):

- \(A(n)\): **distinct** parts \(\equiv 1\) or \(2 \pmod{3}\)
- \(B(n)\): parts \(\equiv \pm1 \pmod{6}\) (reps allowed)
- Pin: `problems/schur-partition/STATEMENT.md` (2026-08-04)
- **Wrong** (fails at n=2): unrestricted parts \(\equiv1,2\pmod3\) vs distinct \(\equiv\pm1\pmod6\)

## Checklist before claiming progress

1. STATEMENT.md matches a named literature source (Schur 1926 / Andrews).
2. Empty partition \(n=0\) convention fixed.
3. Level A: independent enumerator or DP agrees on a bound \(N\); print a few witnesses.
4. Do not confuse this with **Schur numbers** (Ramsey-type) or other “Schur theorems.”
5. Re-grep local Mathlib pin before any “first formalization” language (ledger lesson #7).
6. Default **no claim**; status stays formalize-only / informal until Lean+review gates.

## Strategies

1. **Finite DP / recurrence** for restricted partition functions.
2. **Generating functions** sketch → then formalize only what Mathlib can host.
3. **Bijection search** only with an explicit map + inverse checks on small n.
4. **Ferrers / conjugate** tools when literature proof uses them.

## Anti-patterns

- Trusting an old dossier “Mathlib gap” without grepping the pinned tree
- Swapping which side is “distinct” without re-checking small n
- Mixing OEIS sequences that differ by offset or part constraints
- Scope creep into modular forms before Level A is green
