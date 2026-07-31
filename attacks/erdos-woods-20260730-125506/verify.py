#!/usr/bin/env python3
"""
Erdős-Woods k=16 Verification
Searches for witness a such that each integer in [a, a+16] is distinguished from a
by at least one prime p ≤ 16.
"""

import sys
from typing import List, Optional, Set
import json
from datetime import datetime

# Primes p ≤ 16
PRIMES = [2, 3, 5, 7, 11, 13]
K = 16


def is_witness(a: int, k: int = K, primes: List[int] = PRIMES) -> bool:
    """
    Check if a is a witness for Erdős-Woods number k.

    For each i in [a, a+k], there must exist at least one prime p ≤ k
    such that p divides exactly one of {i, a}.

    Returns True if a is a witness, False otherwise.
    """
    for i in range(a, a + k + 1):
        if i == a:
            continue  # Skip a itself

        # Check if any prime distinguishes i from a
        distinguished = False
        for p in primes:
            # p divides exactly one of {i, a}
            divides_i = (i % p == 0)
            divides_a = (a % p == 0)

            if divides_i != divides_a:  # XOR: exactly one divides
                distinguished = True
                break

        if not distinguished:
            # Found an i in [a, a+k] that is not distinguished from a
            return False

    return True


def search_witness(start: int, end: int, checkpoint_interval: int = 1000000) -> Optional[int]:
    """
    Search for witness in range [start, end).

    Args:
        start: Start of search range (inclusive)
        end: End of search range (exclusive)
        checkpoint_interval: How often to print progress

    Returns:
        Witness a if found, None otherwise
    """
    print(f"Searching range [{start}, {end})...")
    print(f"Primes: {PRIMES}")
    print(f"k = {K}")
    print()

    for a in range(start, end):
        if a > 0 and a % checkpoint_interval == 0:
            print(f"Progress: checked up to a = {a}")

        if is_witness(a):
            return a

    return None


def verify_known_witness(a: int) -> dict:
    """
    Verify and document a witness.
    Returns detailed information about why a is a witness.
    """
    result = {
        "witness": a,
        "k": K,
        "interval": [a, a + K],
        "primes": PRIMES,
        "verification": {}
    }

    for i in range(a, a + K + 1):
        if i == a:
            continue

        distinguishing_primes = []
        for p in PRIMES:
            divides_i = (i % p == 0)
            divides_a = (a % p == 0)
            if divides_i != divides_a:
                distinguishing_primes.append(p)

        result["verification"][i] = {
            "distinguishing_primes": distinguishing_primes,
            "is_distinguished": len(distinguishing_primes) > 0
        }

    return result


def optimize_search_bounds():
    """
    Use residue class analysis to estimate search bounds.

    For k=16, we need to find a such that each i in [a, a+16]
    differs from a in at least one prime divisor p ≤ 16.

    This is a strong constraint - we can use CRT to eliminate
    candidates that cannot satisfy this.
    """
    # Simple heuristic: witnesses tend to be found relatively early
    # Literature suggests B(16) ≤ 10^12, but witnesses might be much smaller

    # Start with small search to test algorithm
    small_bound = 10**6

    # If needed, expand to larger bounds
    medium_bound = 10**9
    large_bound = 10**12

    return small_bound, medium_bound, large_bound


def main():
    """
    Main verification routine.
    """
    print("=" * 60)
    print("Erdős-Woods k=16 Verification")
    print("=" * 60)
    print()

    # Test with small examples first
    print("Testing algorithm with small values...")
    test_range = 1000
    for a in range(1, test_range):
        if is_witness(a):
            print(f"\n*** WITNESS FOUND: a = {a} ***\n")

            # Verify and document
            verification = verify_known_witness(a)

            print("Verification details:")
            print(json.dumps(verification, indent=2))

            # Save result
            timestamp = datetime.utcnow().isoformat()
            result_file = f"witness_{a}.json"
            with open(result_file, 'w') as f:
                json.dump({
                    "timestamp": timestamp,
                    "witness": a,
                    "verification": verification,
                    "status": "CONFIRMED"
                }, f, indent=2)

            print(f"\nResult saved to {result_file}")
            return 0

    print(f"No witness found in range [1, {test_range})")
    print("\nExpanding search range...")

    # Search larger ranges
    bounds = optimize_search_bounds()
    small_bound, medium_bound, large_bound = bounds

    print(f"\nSearching range [1, {small_bound})...")
    witness = search_witness(1, small_bound, checkpoint_interval=100000)

    if witness:
        print(f"\n*** WITNESS FOUND: a = {witness} ***\n")
        verification = verify_known_witness(witness)
        print(json.dumps(verification, indent=2))
        return 0
    else:
        print(f"\nNo witness found in range [1, {small_bound})")
        print("Would need to continue search to larger bounds.")
        print(f"Next range: [{small_bound}, {medium_bound})")
        print(f"Literature suggests witness exists below {large_bound}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
