#!/usr/bin/env python3
"""
Verify k=16, a=2184 is an Erdős-Woods witness pair under the CORRECT definition.

Definition: k is Erdős-Woods if ∃a such that ∀j ∈ (a, a+k),
            gcd(j, a) > 1 OR gcd(j, a+k) > 1

Reference: Erdős & Woods (1980), OEIS A059756
"""

import math

def verify_erdos_woods_witness(k: int, a: int) -> bool:
    """
    Verify that (k, a) is a valid Erdős-Woods witness pair.

    Returns True if every integer j in the open interval (a, a+k)
    shares at least one prime factor with a or a+k.
    """
    endpoint_right = a + k

    print(f"Verifying k={k}, a={a}")
    print(f"Endpoints: a={a}, a+k={endpoint_right}")
    print(f"  {a} = {factorize(a)}")
    print(f"  {endpoint_right} = {factorize(endpoint_right)}")
    print(f"\nInterval (a, a+k): ({a}, {endpoint_right})")
    print(f"Checking {k-1} integers: {a+1} through {endpoint_right-1}\n")

    all_valid = True

    for j in range(a + 1, endpoint_right):
        gcd_left = math.gcd(j, a)
        gcd_right = math.gcd(j, endpoint_right)

        shares_factor = (gcd_left > 1) or (gcd_right > 1)
        status = "✓" if shares_factor else "✗"

        if shares_factor:
            factors = []
            if gcd_left > 1:
                factors.append(f"gcd({j},{a})={gcd_left}")
            if gcd_right > 1:
                factors.append(f"gcd({j},{endpoint_right})={gcd_right}")
            detail = ", ".join(factors)
            print(f"  {status} j={j}: {detail}")
        else:
            print(f"  {status} j={j}: COPRIME to both endpoints (FAILS)")
            all_valid = False

    return all_valid

def factorize(n: int) -> str:
    """Return prime factorization as string."""
    if n <= 1:
        return str(n)

    factors = []
    d = 2
    temp = n
    while d * d <= temp:
        count = 0
        while temp % d == 0:
            count += 1
            temp //= d
        if count > 0:
            if count == 1:
                factors.append(str(d))
            else:
                factors.append(f"{d}^{count}")
        d += 1
    if temp > 1:
        factors.append(str(temp))

    return " × ".join(factors) if factors else str(n)

def main():
    print("=" * 70)
    print("Erdős-Woods Witness Verification (CORRECT DEFINITION)")
    print("=" * 70)
    print()

    # Known canonical example from literature
    k = 16
    a = 2184

    result = verify_erdos_woods_witness(k, a)

    print("\n" + "=" * 70)
    if result:
        print(f"✓ VERIFIED: k={k}, a={a} is a valid Erdős-Woods witness pair")
        print(f"\nConclusion: k={k} is an Erdős-Woods number (minimal a={a})")
    else:
        print(f"✗ FAILED: k={k}, a={a} is NOT a valid witness")
    print("=" * 70)

if __name__ == "__main__":
    main()
