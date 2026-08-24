#!/usr/bin/env python3
"""Bounded verification of the Erdos-Woods witness pair (k=16, a=2184).

Definition (literature, pinned in problems/erdos-woods/STATEMENT.md):
  k is an Erdos-Woods number iff there exists a > 0 such that every
  integer j with a < j < a + k shares at least one prime factor (>1 gcd)
  with a or with a + k.

This script checks the WITNESS property only — it does not prove minimality
of k=16 or of a=2184 (that is literature knowledge: Erdos & Woods 1980).

Scout keep-fresh OPE-334, 2026-08-22.
"""
import sys

K = 16
A = 2184


def prime_factors(n: int) -> set:
    fs, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs.add(n)
    return fs


def shares_factor(x: int, y: int) -> bool:
    return bool(prime_factors(x) & prime_factors(y))


def main() -> int:
    b = A + K
    fa, fb = prime_factors(A), prime_factors(b)
    print(f"a={A} = {' * '.join(f'{p}^{e}' for p, e in sorted(factorization(A).items()))}")
    print(f"b=a+k={b} = {' * '.join(f'{p}^{e}' for p, e in sorted(factorization(b).items()))}")
    ok = True
    covered = 0
    for j in range(A + 1, b):
        via_a = bool(fa & prime_factors(j))
        via_b = bool(fb & prime_factors(j))
        status = "OK "
        if not (via_a or via_b):
            status = "FAIL"
            ok = False
        else:
            covered += 1
        print(f"j={j}: via_a={via_a} via_b={via_b} {status}")
    print(f"\ncovered {covered}/{K - 1} interior points")
    print("PASS" if ok and covered == K - 1 else "FAIL")
    return 0 if ok else 1


def factorization(n: int):
    fs, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            fs[d] = fs.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        fs[n] = fs.get(n, 0) + 1
    return fs


if __name__ == "__main__":
    sys.exit(main())
