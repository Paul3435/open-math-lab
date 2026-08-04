# Formalize Schur's partition theorem

**id:** `schur-partition`  
**Pinned:** 2026-08-04 (Director OPE-21 after OPE-25 Scout)  
**Status:** shortlisted prime — formalize-only, no novelty claim

## Informal statement (literature-pinned)

**Schur's partition theorem** (I. Schur, 1926; see Andrews, *The Theory of Partitions*):

For every non-negative integer \(n\),

\[
A(n) = B(n),
\]

where:

- **\(A(n)\)** = number of partitions of \(n\) into **distinct** parts each congruent to \(1\) or \(2 \pmod{3}\).  
  Allowed part set: \(\{1,2,4,5,7,8,10,11,\ldots\}\) (no part \(\equiv 0 \pmod{3}\)); each part used at most once.
- **\(B(n)\)** = number of partitions of \(n\) into parts each congruent to \(\pm 1 \pmod{6}\) (i.e. \(1\) or \(5 \pmod{6}\)), **repetitions allowed**.  
  Allowed part set: \(\{1,5,7,11,13,17,\ldots\}\).

### Machine check of the pin (do not “fix” without literature)

Python enumeration for \(0 \le n \le 15\): \(A(n)=B(n)\) under **this** pairing.  
The **swapped** pairing (unrestricted parts \(\equiv 1,2 \pmod{3}\) vs distinct \(\equiv \pm1 \pmod{6}\)) **fails** already at \(n=2\).

That swap appeared in an earlier STATEMENT draft example — **superseded**. Treat it as a definition landmine of the same class as OPE-12 EW.

### Worked example \(n=5\)

| Side | Partitions | Count |
|------|------------|------:|
| \(A(5)\) distinct parts \(\equiv 1,2 \pmod{3}\) | \(\{5\}\), \(\{4,1\}\) | 2 |
| \(B(5)\) parts \(\equiv 1,5 \pmod{6}\) (reps OK) | \(\{5\}\), \(\{1,1,1,1,1\}\) | 2 |

(\(2+2+1\) is **not** in \(A(5)\): part \(2\) repeats. \(4+1\) is OK: distinct, both \(\equiv 1\) or \(2 \pmod{3}\).)

### Alternate equivalent phrasings

Some sources swap labels \(A/B\) or state generating-function identities. Before Lean names freeze, Attack Lead must cite **one** primary reference (Andrews § or Schur 1926) and keep Lean defs 1:1 with this file. Do not mix OEIS indices without checking the offset and exact constraints.

## Formalization target

State and prove Schur's theorem in Lean 4 + Mathlib (or a finite computational certificate ladder toward the full theorem).

Honest frame: **formalize-only / process**. Known classical theorem. Default **no external claim**.

## Why feasible?

1. Textbook proofs (generating functions; bijective/combinatorial maps).
2. Mathlib has partition infrastructure (`Nat.Partition` / related); OPE-25 verified the **theorem itself** is still a Mathlib gap on the pinned v4.10.0 snapshot.
3. Finite verification: \(A(n), B(n)\) computable for each fixed \(n\).
4. Incremental path:
   - Level A: Python (or similar) certificate \(A(n)=B(n)\) for \(n \le N\) (suggest \(N \ge 50\)) with explicit partition listing or DP.
   - Level B: Lean defs of \(A,B\) + sorry-free small \(n\) by `native_decide` / computation.
   - Level C (stretch): full theorem `lake build` green.
5. Not crackpot; clear success metric; no deep modular-forms prerequisites for a first attack.

## Definition risks (hard stops)

- **Do not** attack the swapped congruence/distinctness pairing.
- Pin \(n=0\) empty-partition convention (\(A(0)=B(0)=1\)).
- Distinct means multiplicity \(\le 1\), not “parts look different after sorting” bugs.
- No scope creep into other Schur theorems (Ramsey / Schur numbers).

## References

- Schur, I. (1926). "Zur additiven Zahlentheorie." Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse, 488–495.
- Andrews, G. E. (1976). *The Theory of Partitions.* Encyclopedia of Mathematics and its Applications, Vol. 2.
- Hardy & Wright, *An Introduction to the Theory of Numbers*, partition chapters (context).
- OEIS: cross-check only after matching the exact constraints above (do not trust title alone).
- Mathlib: confirm gap still holds on the **local** `.lake/packages/mathlib` pin before claiming contribution (OPE-25 lesson #7).

## Tickets

- Scout shortlist: **OPE-25** (recommended prime)
- Director approval: **OPE-21**
- Attack: child of OPE-21 (see Paperclip)
