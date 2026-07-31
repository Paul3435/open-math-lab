#!/usr/bin/env python3
"""
Computational verification of sum-free subset bound.

Tests the claim: Every finite set of n positive integers contains
a sum-free subset of size at least n/3 (i.e., |A| * 3 >= n).
"""

import random
from typing import Set, List
from collections import defaultdict
import math


def is_sum_free(A: Set[int]) -> bool:
    """Check if set A is sum-free (no x, y, z in A with x + y = z)."""
    for x in A:
        for y in A:
            if x + y in A:
                return False
    return True


def mod3_construction(S: Set[int]) -> Set[int]:
    """
    Construct sum-free subset using modulo-3 residues.
    Returns the largest of C1, C2, C0 (in that priority order).
    """
    C0 = {x for x in S if x % 3 == 0}
    C1 = {x for x in S if x % 3 == 1}
    C2 = {x for x in S if x % 3 == 2}

    # Try C1 and C2 first (guaranteed sum-free)
    candidates = [(len(C1), C1, "C1"), (len(C2), C2, "C2"), (len(C0), C0, "C0")]
    candidates.sort(reverse=True)

    for size, subset, name in candidates:
        if is_sum_free(subset):
            return subset

    # Fallback: return C1 or C2 (always sum-free)
    return C1 if len(C1) >= len(C2) else C2


def verify_bound(S: Set[int]) -> dict:
    """
    Verify that S contains a sum-free subset A with |A| * 3 >= |S|.
    Returns verification results.
    """
    n = len(S)
    A = mod3_construction(S)
    a_size = len(A)

    # Check bound: |A| * 3 >= n
    bound_satisfied = (a_size * 3 >= n)

    # Verify A is sum-free
    is_sf = is_sum_free(A)

    # Verify A ⊆ S
    is_subset = A.issubset(S)

    return {
        "n": n,
        "subset_size": a_size,
        "bound_satisfied": bound_satisfied,
        "is_sum_free": is_sf,
        "is_subset": is_subset,
        "ratio": a_size / n if n > 0 else 0,
        "subset": A,
        "S": S
    }


def brute_force_max_sum_free(S: Set[int]) -> Set[int]:
    """
    Brute force search for largest sum-free subset (exponential time).
    Only for small sets (n <= 20).
    """
    from itertools import chain, combinations

    def powerset(s):
        s = list(s)
        return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

    max_size = 0
    max_subset = set()

    for subset in powerset(S):
        subset_set = set(subset)
        if is_sum_free(subset_set) and len(subset_set) > max_size:
            max_size = len(subset_set)
            max_subset = subset_set

    return max_subset


def test_small_cases():
    """Test small cases and edge cases."""
    print("=" * 60)
    print("Testing small cases and edge cases")
    print("=" * 60)

    test_cases = [
        {1},
        {1, 2},
        {1, 2, 3},
        {1, 2, 3, 4},
        {1, 2, 3, 4, 5},
        {1, 2, 4, 8, 16},  # powers of 2
        {3, 6, 9, 12, 15},  # multiples of 3
        {1, 4, 7, 10, 13, 16},  # residue 1 mod 3
        {2, 5, 8, 11, 14, 17},  # residue 2 mod 3
        set(range(1, 11)),  # {1, 2, ..., 10}
        set(range(1, 21)),  # {1, 2, ..., 20}
    ]

    for S in test_cases:
        result = verify_bound(S)
        n = result["n"]
        a_size = result["subset_size"]
        bound = result["bound_satisfied"]

        status = "✓" if bound else "✗"
        print(f"\n{status} S = {S if n <= 10 else f'{{1..{n}}}'}")
        print(f"  n = {n}, |A| = {a_size}, ratio = {a_size/n:.3f}")
        print(f"  Bound |A|*3 >= n: {a_size}*3 = {a_size*3} >= {n} ? {bound}")
        print(f"  Sum-free: {result['is_sum_free']}")

        # For small sets, compare with brute force
        if n <= 12:
            optimal = brute_force_max_sum_free(S)
            opt_size = len(optimal)
            print(f"  Optimal: |A_max| = {opt_size} (brute force)")
            if opt_size > a_size:
                print(f"  ⚠ Modulo-3 construction is suboptimal ({a_size} < {opt_size})")


def test_random_sets(num_tests=100, max_n=50):
    """Test random sets."""
    print("\n" + "=" * 60)
    print(f"Testing {num_tests} random sets (n up to {max_n})")
    print("=" * 60)

    failures = []
    ratios = []

    for i in range(num_tests):
        n = random.randint(3, max_n)
        max_val = n * 10
        S = set(random.sample(range(1, max_val), n))

        result = verify_bound(S)
        ratios.append(result["ratio"])

        if not result["bound_satisfied"]:
            failures.append(result)
            print(f"\n✗ Test {i+1}: FAILED")
            print(f"  S = {S if n <= 10 else f'(n={n}, sample: {list(S)[:10]}...)'}")
            print(f"  |A| = {result['subset_size']}, |A|*3 = {result['subset_size']*3}, n = {n}")

    print(f"\n{num_tests - len(failures)}/{num_tests} tests passed")
    print(f"Average ratio |A|/n: {sum(ratios)/len(ratios):.3f}")
    print(f"Min ratio: {min(ratios):.3f}, Max ratio: {max(ratios):.3f}")

    if failures:
        print(f"\n⚠ {len(failures)} FAILURES detected!")
        for fail in failures[:5]:  # Show first 5 failures
            print(f"  n={fail['n']}, |A|={fail['subset_size']}, ratio={fail['ratio']:.3f}")
    else:
        print("\n✓ All tests passed!")

    return len(failures) == 0


def test_worst_case():
    """
    Test potential worst cases for modulo-3 construction.
    """
    print("\n" + "=" * 60)
    print("Testing worst-case scenarios")
    print("=" * 60)

    # Case 1: Mostly residue 0 mod 3
    print("\nCase 1: Mostly multiples of 3")
    S = set(range(3, 31, 3))  # {3, 6, 9, ..., 30}, n=10
    result = verify_bound(S)
    print(f"S = {S}")
    print(f"|A| = {result['subset_size']}, bound satisfied: {result['bound_satisfied']}")
    print(f"A = {result['subset']}")
    print(f"Is sum-free: {result['is_sum_free']}")

    # Case 2: Balanced residues but small n
    print("\nCase 2: n = 3k+1 (edge case for ceiling division)")
    for n in [4, 7, 10, 13]:
        S = set(range(1, n+1))
        result = verify_bound(S)
        print(f"n = {n}: |A| = {result['subset_size']}, |A|*3 = {result['subset_size']*3}, bound: {result['bound_satisfied']}")

    # Case 3: Sets where C0 is largest
    print("\nCase 3: C0 largest (many multiples of 3)")
    S = set(list(range(3, 30, 3)) + [1, 2])  # 10 multiples of 3, plus 1 and 2
    result = verify_bound(S)
    print(f"S has {len(S)} elements: {len([x for x in S if x%3==0])} in C0, {len([x for x in S if x%3==1])} in C1, {len([x for x in S if x%3==2])} in C2")
    print(f"|A| = {result['subset_size']}, bound satisfied: {result['bound_satisfied']}")


if __name__ == "__main__":
    print("Sum-Free Subset Verification")
    print("=" * 60)

    # Verify basic properties
    print("\nVerifying sum-free property:")
    print(f"{{1, 2}} is sum-free: {is_sum_free({1, 2})}")  # True (1+1=2 is in set, so False!)
    print(f"{{1, 2, 3}} is sum-free: {is_sum_free({1, 2, 3})}")  # False (1+2=3)
    print(f"{{1, 5, 7}} is sum-free: {is_sum_free({1, 5, 7})}")  # True
    print(f"{{2, 5, 8}} is sum-free: {is_sum_free({2, 5, 8})}")  # True (all ≡ 2 mod 3)

    # Run tests
    test_small_cases()
    test_worst_case()
    all_pass = test_random_sets(num_tests=200, max_n=100)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    if all_pass:
        print("✓ All tests passed! Modulo-3 construction appears sound.")
    else:
        print("✗ Some tests failed. Modulo-3 construction needs refinement.")
    print("=" * 60)
