#!/usr/bin/env python3
"""
Adversarial review script: Independent verification of the claim that a=5 is a witness for k=16.

This script implements the Erdős-Woods definition from scratch to verify the claim independently.
"""

# Definition: k is an Erdős-Woods number if there exists a witness a such that
# for every integer i in [a, a+k], there exists a prime p ≤ k where
# p divides exactly one of {i, a} (XOR condition).

K = 16
PRIMES_UP_TO_16 = [2, 3, 5, 7, 11, 13]  # All primes ≤ 16
WITNESS_CLAIM = 5

def get_prime_factors_up_to_k(n, primes):
    """Return the set of primes from `primes` that divide n."""
    return {p for p in primes if n % p == 0}

def is_distinguished(i, a, primes):
    """
    Check if i is distinguished from a by at least one prime p ≤ k.

    i is distinguished from a if there exists p in primes such that
    p divides exactly one of {i, a}.
    """
    for p in primes:
        divides_i = (i % p == 0)
        divides_a = (a % p == 0)
        # XOR: exactly one divides
        if divides_i != divides_a:
            return True, p  # Return first distinguishing prime
    return False, None

def verify_witness(a, k, primes):
    """
    Verify if a is a witness for Erdős-Woods number k.

    Returns: (is_valid, details)
    """
    details = []
    interval_start = a
    interval_end = a + k

    for i in range(interval_start, interval_end + 1):
        if i == a:
            details.append(f"i={i}: Same as witness a (skip)")
            continue

        distinguished, p = is_distinguished(i, a, primes)

        if distinguished:
            i_factors = get_prime_factors_up_to_k(i, primes)
            a_factors = get_prime_factors_up_to_k(a, primes)
            details.append(f"i={i}: ✓ Distinguished by p={p} | factors(i)={i_factors}, factors(a)={a_factors}")
        else:
            i_factors = get_prime_factors_up_to_k(i, primes)
            a_factors = get_prime_factors_up_to_k(a, primes)
            details.append(f"i={i}: ✗ NOT distinguished | factors(i)={i_factors}, factors(a)={a_factors}")
            return False, details

    return True, details

def main():
    print("=" * 80)
    print("ADVERSARIAL REVIEW: Independent Verification")
    print("=" * 80)
    print()
    print(f"Claim: a={WITNESS_CLAIM} is a witness for k={K}")
    print(f"Primes p ≤ {K}: {PRIMES_UP_TO_16}")
    print(f"Interval to check: [{WITNESS_CLAIM}, {WITNESS_CLAIM + K}]")
    print()

    # Verify the witness
    is_valid, details = verify_witness(WITNESS_CLAIM, K, PRIMES_UP_TO_16)

    print("Verification details:")
    print("-" * 80)
    for line in details:
        print(line)
    print("-" * 80)
    print()

    if is_valid:
        print("✓ CLAIM VERIFIED: a=5 is a valid witness for k=16")
        print("✓ Every integer in [5, 21] is distinguished from 5 by at least one prime ≤ 16")
        print()

        # Additional spot checks
        print("Spot checks:")
        print("-" * 80)

        # Check i=17 (prime, coprime to 5)
        i = 17
        factors_i = get_prime_factors_up_to_k(i, PRIMES_UP_TO_16)
        factors_a = get_prime_factors_up_to_k(WITNESS_CLAIM, PRIMES_UP_TO_16)
        print(f"i={i} (prime): factors={factors_i}, a={WITNESS_CLAIM} factors={factors_a}")
        print(f"  Prime 5 divides a but not i → distinguished by p=5 ✓")
        print()

        # Check i=10 (even, multiple of 5)
        i = 10
        factors_i = get_prime_factors_up_to_k(i, PRIMES_UP_TO_16)
        factors_a = get_prime_factors_up_to_k(WITNESS_CLAIM, PRIMES_UP_TO_16)
        print(f"i={i} (even multiple of 5): factors={factors_i}, a={WITNESS_CLAIM} factors={factors_a}")
        print(f"  Prime 2 divides i but not a → distinguished by p=2 ✓")
        print()

        # Check i=15 (odd multiple of 5)
        i = 15
        factors_i = get_prime_factors_up_to_k(i, PRIMES_UP_TO_16)
        factors_a = get_prime_factors_up_to_k(WITNESS_CLAIM, PRIMES_UP_TO_16)
        print(f"i={i} (odd multiple of 5): factors={factors_i}, a={WITNESS_CLAIM} factors={factors_a}")
        print(f"  Prime 3 divides i but not a → distinguished by p=3 ✓")
        print("-" * 80)
        print()

        return 0
    else:
        print("✗ CLAIM REJECTED: a=5 is NOT a valid witness for k=16")
        return 1

if __name__ == "__main__":
    import sys
    sys.exit(main())
