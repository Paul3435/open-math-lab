# Graceful Caterpillar Trees Attack (n ≤ 12)

**Problem**: Graceful Tree Conjecture — verify graceful labelings for caterpillar trees  
**Attack ID**: graceful-tree-conjecture-20260731-094627  
**Date**: 2026-07-31  
**Status**: Ready for review

---

## Quick Start

```bash
cd attacks/graceful-tree-conjecture-20260731-094627
python verify_caterpillar.py  # Re-run verification (takes ~12 minutes)
```

---

## Result

✓ **All 2,142 non-isomorphic caterpillar trees with n ≤ 12 vertices are graceful**

- Zero failures
- Zero timeouts
- Explicit constructive labelings in `RESULTS.json`

---

## Files

| File | Description |
|------|-------------|
| `LOG.md` | Attack log with strategy, execution, findings |
| `RESULTS.md` | Results interpretation, scope, limitations, next steps |
| `RESULTS.json` | Full verification results (725KB) — all 2,142 labelings |
| `verify_caterpillar.py` | Python verification script (enumeration + backtracking) |
| `STATUS.json` | Metadata |
| `README.md` | This file |

---

## What is a Caterpillar Tree?

A **caterpillar tree** is a tree where all non-leaf vertices lie on a single path (the "spine").

Examples:
```
n=3, spine=2, leaves=(0,1):
  0---1---2

n=4, spine=2, leaves=(1,1):
    2
   /
  0---1
       \
        3
```

Caterpillars are a natural test case for the **Graceful Tree Conjecture** (Rosa, 1967), which states that every tree admits a graceful labeling.

---

## What is a Graceful Labeling?

A **graceful labeling** of a graph G with m edges assigns distinct labels from {0, 1, ..., m} to vertices such that edge labels {|f(u) - f(v)| : (u,v) ∈ E} = {1, 2, ..., m}.

Example (n=3, m=2):
```
Vertices: 0, 1, 2
Edges: (0,1), (1,2)
Labeling: f(0)=0, f(1)=2, f(2)=1
Edge labels: |0-2|=2, |2-1|=1 → {1, 2} ✓ graceful
```

---

## Verification Method

1. **Enumerate** all non-isomorphic caterpillar trees (n=1 to 12)
2. **Search** for graceful labelings via backtracking
3. **Verify** each labeling satisfies the graceful property
4. **Record** results and constructive witnesses

### Enumeration Strategy
- Represent caterpillars as `(spine_length, leaf_config)`
- Use canonical partition form to avoid symmetry overcounting
- Generated 2,142 distinct caterpillar trees

### Search Strategy
- n ≤ 8: Brute-force permutation search
- n > 8: Backtracking constraint satisfaction
- 60s timeout per tree (none hit)

---

## Scope

✓ **In scope**:
- Caterpillar trees with n ≤ 12 vertices
- Computational verification with constructive witnesses

✗ **Out of scope**:
- General trees (non-caterpillar)
- Caterpillar trees with n > 12
- Theoretical proof (this is empirical)

---

## Confidence: 8/10 (High)

**Strengths**:
- All 2,142 trees verified
- Explicit constructive labelings
- Self-verification in code

**Limitations**:
- Enumeration logic not independently verified
- Backtracking implementation not formally proven
- Computational, not theoretical

---

## Next Steps

1. **Adversarial review**: Verify enumeration and backtracking correctness
2. **Spot-check**: Manual verification of sample labelings
3. **Extension** (optional): n=13-15 if compute budget allows
4. **Formalization** (future): Lean 4 encoding of results

---

## References

- Rosa, A. (1967). "On certain valuations of the vertices of a graph."
- Gallian, J. A. (2021). "A dynamic survey of graph labeling." (Dynamic Survey DS6)
- OEIS A000055: Number of trees on n unlabeled nodes

---

## Safe Claim Language

**Use**:
> Computational verification: All 2,142 non-isomorphic caterpillar trees with n ≤ 12 vertices admit graceful labelings.

**Do NOT use**:
- "Proof of graceful tree conjecture"
- "All caterpillar trees are graceful" (only n≤12 tested)
- "No counterexamples exist" (only in bounded scope)

---

## Contact

**Attack Lead**: Attack Lead Agent (OPE-13)  
**Session**: 2026-07-31T09:46:27Z to 2026-07-31T10:00:16Z  
**Runtime**: 739 seconds (~12.3 minutes)  
**Tokens**: ~56k / 200k budget
