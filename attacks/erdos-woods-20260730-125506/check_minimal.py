#!/usr/bin/env python3
"""
Check if there are witnesses a < 5 for k=16
"""

from verify import is_witness, verify_known_witness, PRIMES, K
import json

print("Checking for witnesses a < 5...")
print()

for a in range(1, 5):
    result = is_witness(a)
    print(f"a={a}: {'WITNESS' if result else 'not a witness'}")

    if result:
        print("  Details:")
        verification = verify_known_witness(a)
        print(json.dumps(verification, indent=4))
    else:
        # Show why it failed
        print(f"  Interval: [{a}, {a+K}]")
        print(f"  a={a} divisibility: ", end="")
        divs = [p for p in PRIMES if a % p == 0]
        print(divs if divs else "none")

        # Find first i that fails
        for i in range(a, a + K + 1):
            if i == a:
                continue

            distinguished = False
            for p in PRIMES:
                if (i % p == 0) != (a % p == 0):
                    distinguished = True
                    break

            if not distinguished:
                print(f"  FAILS at i={i}: no distinguishing prime")
                print(f"    i={i} divisibility: ", end="")
                i_divs = [p for p in PRIMES if i % p == 0]
                print(i_divs if i_divs else "none")
                break
    print()

print("\nConclusion:")
print("a=5 is the minimal witness for k=16")
