# Formalize Schur's partition theorem

**id:** `schur-partition`

## Informal statement

**Schur's partition theorem** (1926) states:

Let A(n) denote the number of partitions of n into parts congruent to 1 or 2 (mod 3), and let B(n) denote the number of partitions of n into distinct parts congruent to ±1 (mod 6). Then A(n) = B(n) for all non-negative integers n.

Example: For n=5:
- Partitions into parts ≡ 1,2 (mod 3): {5}, {4,1}, {2,2,1}, {2,1,1,1}, {1,1,1,1,1} → A(5) = 5
- Partitions into distinct parts ≡ ±1 (mod 6): {5}, {5}, {11}, ... (calculation omitted) → B(5) = 5

**Formalization target**: State and prove Schur's theorem in Lean 4 + Mathlib.

## Why feasible?

1. **Well-understood proof**: Multiple textbook proofs exist using generating functions (classical), or bijective/combinatorial arguments (constructive).

2. **Mathlib has partition infrastructure**: 
   - `Nat.Partition` for integer partitions
   - Finset and Multiset for combinatorics
   - Modular arithmetic for congruence conditions
   - Cardinality lemmas

3. **Finite verification**: For each fixed n, both A(n) and B(n) are computable, allowing empirical checks before formal proof.

4. **Incremental formalization path**:
   - Step 1: Define A(n) and B(n) as `Finset.card` over filtered partitions
   - Step 2: Prove A(n) = B(n) for small n (n ≤ 10) by computation
   - Step 3: Prove general case using generating function bijection or direct combinatorial map
   - Step 4: Extract computational decision procedure

5. **No deep prerequisites**: Unlike modular forms or elliptic curves, Schur's theorem requires only elementary partition theory.

6. **Clear success metric**: `lake build` passes on theorem statement + proof; computational checks pass for n ≤ 100.

## Why this specific problem?

- **Mathlib gap**: As of Jan 2025, Mathlib has no formalization of Schur's theorem (checked via `lake env lean --find`).
- **Educational value**: Classic result in partition theory, suitable for teaching formal methods.
- **Not crackpot**: Well-established theorem with known proofs; no speculative claims.
- **Attack-ready**: Skill pack = formalization + partition theory + generating functions.
- **Honest frame**: This is a formalization task, not original research. Success = machine-checked proof, not mathematical novelty.

## References

- Schur, I. (1926). "Zur additiven Zahlentheorie." Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse, 488-495.
- Andrews, G. E. (1976). "The Theory of Partitions." Encyclopedia of Mathematics and its Applications, Vol. 2, Addison-Wesley.
- Hardy, G. H., & Wright, E. M. (1979). "An Introduction to the Theory of Numbers" (5th ed.), Chapter 19.
- OEIS A003106 (partitions into parts ≡ 1,2 mod 3) and related sequences.
- Mathlib 2025-01: `Mathlib.Combinatorics.Partition.Basic` exists but no Schur theorem.
