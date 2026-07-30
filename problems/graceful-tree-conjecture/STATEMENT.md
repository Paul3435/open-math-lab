# Graceful labeling verification for small caterpillar trees

**id:** `graceful-tree-conjecture`

## Informal statement

A **graceful labeling** of a graph G with n edges is an injective function f: V(G) → {0, 1, ..., n} such that the induced edge labels {|f(u) - f(v)| : uv ∈ E(G)} are exactly {1, 2, ..., n}.

The **Graceful Tree Conjecture** (Rosa, 1967) states that every tree admits a graceful labeling.

A **caterpillar tree** is a tree in which all non-leaf vertices lie on a single path (the "spine"). Caterpillar trees form a natural test case for the graceful tree conjecture.

**Research question**: Verify computationally that all caterpillar trees with ≤12 vertices admit graceful labelings.

## Why feasible?

1. **Finite enumeration**: The number of non-isomorphic caterpillar trees with n vertices is polynomial in n. For n=12, there are ~400 distinct caterpillar trees.

2. **Backtracking search**: For each tree T with n vertices and m edges, search for a valid labeling f: V → {0, ..., m} is a constraint satisfaction problem solvable via backtracking.

3. **Known partial results**: 
   - Caterpillar trees with ≤8 vertices: confirmed graceful (various papers).
   - Paths (trivial caterpillars): always graceful.
   - General caterpillar graceful labeling construction exists for many infinite families.

4. **Checkable**: Each candidate labeling is verified in O(|E|) time.

5. **Incremental progress**: Results partition by vertex count (n=1 to n=12) and by spine length.

6. **Formalizable output**: A constructive proof (explicit labeling for each tree) can be encoded in Lean as a computable witness.

## Why this specific problem?

- **Not crackpot**: The general graceful tree conjecture is open, but restricting to small caterpillar trees is a bounded computational task.
- **Research value**: Empirical evidence strengthens the conjecture; finding a counterexample (unlikely but possible) would be significant.
- **Attack-ready**: Skill pack = graph theory + backtracking search + verification script.
- **Honest frame**: This is a verification task, not a proof of the full conjecture. Success = "all caterpillar trees with ≤12 vertices are graceful" + explicit labelings.
- **Failure is useful**: If a counterexample is found, that's a publishable result.

## Verification strategy

1. **Enumerate**: Generate all non-isomorphic caterpillar trees with n vertices (n=1 to 12).
2. **Search**: For each tree, run backtracking search for graceful labeling (timeout: 60s per tree).
3. **Record**: Store successful labelings in JSON/YAML + optional Lean witness.
4. **Report**: Summary table: n → (total caterpillar trees, gracefully labeled, failed, timed out).

## References

- Rosa, A. (1967). "On certain valuations of the vertices of a graph." Theory of Graphs (Internat. Symposium, Rome, 1966), Gordon and Breach, 349-355.
- Gallian, J. A. (2021). "A dynamic survey of graph labeling." Electronic Journal of Combinatorics, Dynamic Survey DS6.
- Hrnčiar, P., & Haviar, A. (2001). "All trees of diameter five are graceful." Discrete Mathematics, 233(1-3), 133-150.
- OEIS A000055: Number of trees on n unlabeled nodes.
- Graph labeling literature: Caterpillar trees are a standard test family.
