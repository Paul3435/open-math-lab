#!/usr/bin/env python3
"""
Correct sum-free subset construction using Erdős's averaging argument.

The classical proof (Erdős 1965):
1. Given S with max(S) = m, find prime p > m.
2. Let I = {k ∈ ℤ_p : p/3 < k < 2p/3} — this is sum-free in ℤ_p.
3. For each t ∈ {1,...,p-1}, let A_t = {s ∈ S : t·s mod p ∈ I}.
4. A_t is sum-free in ℕ (since x+y=z implies tx+ty≡tz mod p, contradicting I sum-free in ℤ_p).
5. Averaging: Σ_t |A_t| = n·|I| ≥ n·(p-1)/3, so max_t |A_t| ≥ n/3.

This module implements the deterministic version (try all t, pick best).

status: informal (no machine-verified proof)
"""

from typing import Set, Optional
import math


def is_sum_free(A: Set[int]) -> bool:
    """Check if set A is sum-free: no x,y,z ∈ A with x+y=z."""
    A_list = sorted(A)
    for i, x in enumerate(A_list):
        for y in A_list:
            if x + y in A:
                return False
    return True


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def next_prime(n: int) -> int:
    """Find smallest prime > n."""
    k = n + 1
    while not is_prime(k):
        k += 1
    return k


def interval_in_Zp(p: int) -> Set[int]:
    """
    I = {k ∈ {1,...,p-1} : p/3 < k < 2p/3}.

    This set is sum-free in ℤ_p:
    If a, b ∈ I then a+b ∈ (2p/3, 4p/3).
    - If a+b < p: a+b ∈ (2p/3, p), not in I.
    - If a+b ≥ p: (a+b) mod p ∈ (0, p/3), not in I.
    Either way, (a+b) mod p ∉ I.
    """
    lo = p / 3
    hi = 2 * p / 3
    return {k for k in range(1, p) if lo < k < hi}


def erdos_sum_free(S: Set[int]) -> Set[int]:
    """
    Find sum-free A ⊆ S with |A| ≥ |S|/3 using Erdős averaging argument.

    Correctness argument:
    - A_t is sum-free: if x+y=z in ℕ with x,y,z ∈ A_t,
      then tx mod p, ty mod p ∈ I and (tx+ty) mod p = tz mod p ∈ I.
      But I is sum-free in ℤ_p, contradiction.
    - Averaging: each s ∈ S contributes to A_t for exactly |I| values of t
      (since multiplication by s is a bijection on ℤ_p* as p > max(S) ≥ s).
      So Σ_t |A_t| = n·|I| ≥ n·(p-1)/3.
      Hence max_t |A_t| ≥ n·(p-1)/(3·(p-1)) = n/3.
    """
    if not S:
        return set()

    n = len(S)
    m = max(S)

    # Find prime p > m
    p = next_prime(m)

    I = interval_in_Zp(p)

    # Try all t ∈ {1,...,p-1}, find best
    best: Set[int] = set()
    for t in range(1, p):
        A_t = {s for s in S if (t * s) % p in I}
        if len(A_t) > len(best):
            best = A_t

    return best


def verify_theorem(S: Set[int]) -> dict:
    """Verify ∃ A ⊆ S. IsSumFree(A) ∧ |A|·3 ≥ |S|."""
    A = erdos_sum_free(S)
    n = len(S)
    a_size = len(A)
    return {
        "n": n,
        "a_size": a_size,
        "bound_satisfied": a_size * 3 >= n,
        "is_sum_free": is_sum_free(A),
        "is_subset": A.issubset(S),
        "ratio": a_size / n if n > 0 else 0,
    }


def run_tests(num_random: int = 200) -> None:
    import random
    random.seed(42)

    print("=== Sum-Free Subset Theorem — Erdős Construction ===\n")

    # --- Named test cases ---
    named = [
        ("empty", set()),
        ("singleton", {7}),
        ("pair non-sf", {5, 10}),    # 5+5=10, so not sum-free; need subset
        ("all mod-3 zero", {3, 6, 9, 12, 15}),
        ("all mod-3 zero large", {3, 6, 9, 12, 15, 18, 21, 24, 27}),
        ("{1,2,3}", {1, 2, 3}),
        ("range 1-9", set(range(1, 10))),
        ("range 1-30", set(range(1, 31))),
        ("powers of 2", {2**i for i in range(1, 8)}),
        ("Fibonacci", {1, 2, 3, 5, 8, 13, 21, 34}),
    ]

    failures = 0
    for name, S in named:
        if not S:
            print(f"  ✓ {name}: empty set trivially ok")
            continue
        r = verify_theorem(S)
        ok = r["bound_satisfied"] and r["is_sum_free"] and r["is_subset"]
        sym = "✓" if ok else "✗"
        print(f"  {sym} {name}: n={r['n']}, |A|={r['a_size']}, "
              f"|A|*3={r['a_size']*3} ≥ n={r['n']}? {r['bound_satisfied']}")
        if not ok:
            failures += 1

    # --- Random tests ---
    print(f"\n  Running {num_random} random tests...")
    for _ in range(num_random):
        n = random.randint(1, 30)
        S = set(random.sample(range(1, 200), n))
        r = verify_theorem(S)
        if not (r["bound_satisfied"] and r["is_sum_free"] and r["is_subset"]):
            print(f"  ✗ FAIL: S={S}")
            failures += 1

    print(f"\n  Random tests: {num_random - failures}/{num_random} passed "
          f"({'OK' if failures == 0 else 'FAILURES FOUND'})")

    # --- Averaging argument check ---
    print("\n=== Averaging Argument Verification ===\n")
    print("Checking |I|/(p-1) ≥ 1/3 for small primes:\n")
    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
        I = interval_in_Zp(p)
        ratio = len(I) / (p - 1)
        ok = ratio >= 1/3 - 1e-9
        print(f"  p={p:3d}: |I|={len(I):3d}, (p-1)={p-1:3d}, |I|/(p-1)={ratio:.4f} ≥ 1/3? {'✓' if ok else '✗'}")

    print("\nDone.")


if __name__ == "__main__":
    run_tests()
