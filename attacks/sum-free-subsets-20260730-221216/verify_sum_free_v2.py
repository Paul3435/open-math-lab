#!/usr/bin/env python3
"""
Improved sum-free subset construction.

Tests multiple strategies:
1. Modulo-3 construction (baseline)
2. Interval-based construction
3. Greedy maximum
"""

import random
from typing import Set, List
from collections import defaultdict
import math


def is_sum_free(A: Set[int]) -> bool:
    """Check if set A is sum-free (no x, y, z in A with x + y = z)."""
    if not A:
        return True
    for x in A:
        for y in A:
            if x + y in A:
                return False
    return True


def mod3_construction(S: Set[int]) -> Set[int]:
    """Modulo-3 construction: return largest of C1, C2."""
    C0 = {x for x in S if x % 3 == 0}
    C1 = {x for x in S if x % 3 == 1}
    C2 = {x for x in S if x % 3 == 2}

    # Return largest of C1, C2 (both guaranteed sum-free)
    return C1 if len(C1) >= len(C2) else C2


def interval_construction(S: Set[int]) -> Set[int]:
    """
    Interval-based construction using dyadic intervals.
    For each k, partition into [2^k, 2^(k+1)).
    These intervals are sum-free.
    """
    if not S:
        return set()

    intervals = defaultdict(set)
    max_val = max(S)

    # Group elements by dyadic intervals
    for x in S:
        if x == 0:
            intervals[0].add(x)
        else:
            # Find k such that 2^k <= x < 2^(k+1)
            k = x.bit_length() - 1  # floor(log2(x))
            intervals[k].add(x)

    # Return largest interval
    if not intervals:
        return set()
    return max(intervals.values(), key=len)


def odlyzko_construction(S: Set[int]) -> Set[int]:
    """
    Odlyzko's construction: partition by x mod (max(S)+1).
    Take elements in range [a, 2a) for some a.
    """
    if not S:
        return set()

    S_list = sorted(S)
    n = len(S_list)

    # Try different ranges [a, 2a)
    best = set()

    # Try ranges based on elements in S
    for i, a in enumerate(S_list):
        if a == 0:
            continue
        interval = {x for x in S if a <= x < 2*a}
        if is_sum_free(interval) and len(interval) > len(best):
            best = interval

    return best


def greedy_construction(S: Set[int]) -> Set[int]:
    """
    Greedy construction: iteratively add elements that maintain sum-freedom.
    """
    if not S:
        return set()

    S_list = sorted(S)
    A = set()

    for x in S_list:
        # Try adding x to A
        if is_sum_free(A | {x}):
            A.add(x)

    return A


def hybrid_construction(S: Set[int]) -> Set[int]:
    """
    Hybrid: try all strategies and return the largest sum-free subset found.
    """
    strategies = [
        ("mod3", mod3_construction(S)),
        ("interval", interval_construction(S)),
        ("odlyzko", odlyzko_construction(S)),
        ("greedy", greedy_construction(S)),
    ]

    best_size = 0
    best_subset = set()
    best_name = ""

    for name, subset in strategies:
        if is_sum_free(subset) and len(subset) > best_size:
            best_size = len(subset)
            best_subset = subset
            best_name = name

    return best_subset


def verify_bound(S: Set[int], construction_fn=hybrid_construction) -> dict:
    """Verify bound with given construction."""
    n = len(S)
    A = construction_fn(S)
    a_size = len(A)

    bound_satisfied = (a_size * 3 >= n)
    is_sf = is_sum_free(A)
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


def compare_strategies(S: Set[int]):
    """Compare all strategies on a given set."""
    strategies = {
        "mod3": mod3_construction,
        "interval": interval_construction,
        "odlyzko": odlyzko_construction,
        "greedy": greedy_construction,
        "hybrid": hybrid_construction,
    }

    results = {}
    for name, fn in strategies.items():
        subset = fn(S)
        results[name] = {
            "subset": subset,
            "size": len(subset),
            "sum_free": is_sum_free(subset),
            "ratio": len(subset) / len(S) if len(S) > 0 else 0
        }

    return results


def test_problematic_cases():
    """Test cases that failed with modulo-3."""
    print("=" * 60)
    print("Testing problematic cases with hybrid construction")
    print("=" * 60)

    cases = [
        ({3, 6, 9, 12, 15}, "All multiples of 3"),
        (set(list(range(3, 30, 3)) + [1, 2]), "Mostly multiples of 3"),
        (set(range(1, 11)), "Consecutive 1-10"),
        ({1, 2, 3}, "Tight case: {1,2,3}"),
    ]

    for S, desc in cases:
        print(f"\n{desc}: S = {S if len(S) <= 15 else f'(n={len(S)})'}")
        results = compare_strategies(S)

        for name, result in results.items():
            status = "✓" if result["sum_free"] else "✗"
            print(f"  {status} {name:10s}: size={result['size']}, ratio={result['ratio']:.3f}, bound={result['size']*3 >= len(S)}")


def test_random_with_hybrid(num_tests=200, max_n=100):
    """Test random sets with hybrid construction."""
    print("\n" + "=" * 60)
    print(f"Testing {num_tests} random sets with hybrid construction")
    print("=" * 60)

    failures = []
    ratios = []

    for i in range(num_tests):
        n = random.randint(3, max_n)
        max_val = n * 10
        S = set(random.sample(range(1, max_val), n))

        result = verify_bound(S, construction_fn=hybrid_construction)
        ratios.append(result["ratio"])

        if not result["bound_satisfied"]:
            failures.append(result)

    print(f"\n{num_tests - len(failures)}/{num_tests} tests passed")
    print(f"Average ratio |A|/n: {sum(ratios)/len(ratios):.3f}")
    print(f"Min ratio: {min(ratios):.3f}, Max ratio: {max(ratios):.3f}")

    if failures:
        print(f"\n⚠ {len(failures)} FAILURES detected!")
        for fail in failures[:10]:
            print(f"  n={fail['n']}, |A|={fail['subset_size']}, ratio={fail['ratio']:.3f}")
            print(f"    Sample: {list(fail['S'])[:15]}")
    else:
        print("\n✓ All tests passed!")

    return len(failures) == 0


if __name__ == "__main__":
    print("Improved Sum-Free Subset Construction")
    print("=" * 60)

    test_problematic_cases()
    all_pass = test_random_with_hybrid(num_tests=500, max_n=100)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    if all_pass:
        print("✓ All tests passed with hybrid construction!")
    else:
        print("✗ Some tests still fail. Theorem may require deeper construction.")
    print("=" * 60)
