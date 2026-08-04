#!/usr/bin/env python3
"""
Schur's partition theorem — Level A computational certificate.

Classical 1926 theorem (I. Schur; Andrews, The Theory of Partitions), pinned for
this lab in problems/schur-partition/STATEMENT.md (2026-08-04):

For every integer n >= 0:
    A(n) == B(n)

where
    A(n) = number of partitions of n into DISTINCT parts each ≡ 1 or 2 (mod 3)
           (allowed part set {1,2,4,5,7,8,10,11,...}, each part used at most once)
    B(n) = number of partitions of n into parts each ≡ ±1 (mod 6) i.e. 1 or 5 (mod 6),
           REPETITIONS allowed
           (allowed part set {1,5,7,11,13,17,...})

Conventions / hard stops locked in by the statement:
  * n=0 -> exactly one (empty) partition on BOTH sides: A(0)=B(0)=1.
  * "distinct" means each part has multiplicity <= 1 (handled by descending DP
    loop over parts).
  * The SWAPPED pairing (unrestricted parts ≡1,2 mod3 vs DISTINCT parts ≡±1 mod6)
    FAILS at n=2 and is explicitly NOT the theorem (definition landmine).

Two INDEPENDENT enumerators are implemented so that the certificate does not
rely on a single self-consistent bug:

  Method 1 (DP):
      A: descending unbounded-knapsack over distinct parts (each used <= once)
      B: ascending unbounded-knapsack over parts with repetitions allowed

  Method 2 (brute-force multiset listing, small n only):
      identical partition object lists returned by two definitions, then count.

We certify A(n)==B(n) for all 0 <= n <= N (default N=150), report witnesses
(for each of several n: explicit partition lists with A and B counts), and
explicitly demonstrate that the SWAPPED pairing fails at n=2 (guard against the
statement landmine).

This is formalize-only / process. No novelty claim. Default no claim.
"""
from __future__ import annotations

import argparse
from collections import Counter


# --------------------------------------------------------------------------
# Method 1: dynamic programming (exact, arbitrary n)
# --------------------------------------------------------------------------
def parts_mod3_A(n: int) -> int:
    """A(n): partitions into DISTINCT parts ≡ 1 or 2 (mod 3)."""
    # descending loop over parts => each part used at most once (distinct)
    dp = [0] * (n + 1)
    dp[0] = 1
    p = 1
    while p <= n:
        if p % 3 in (1, 2):
            for m in range(n, p - 1, -1):
                dp[m] += dp[m - p]
        p += 1
    return dp[n]


def parts_mod6_reps_B(n: int) -> int:
    """B(n): partitions into parts ≡ 1 or 5 (mod 6), repetitions allowed."""
    dp = [0] * (n + 1)
    dp[0] = 1
    p = 1
    while p <= n:
        if p % 6 in (1, 5):
            for m in range(p, n + 1):
                dp[m] += dp[m - p]
        p += 1
    return dp[n]


# --------------------------------------------------------------------------
# Method 2: brute-force partition listing (small n) — independent check
# --------------------------------------------------------------------------
def partitions_distinct(allowed_parts, n):
    """All partitions of n into DISTINCT parts drawn from allowed_parts."""
    res = []

    def rec(k, remaining, cur):
        if remaining == 0:
            res.append(list(cur))
            return
        for pi in range(k, len(allowed_parts)):
            if allowed_parts[pi] > remaining:
                break
            cur.append(allowed_parts[pi])
            rec(pi + 1, remaining - allowed_parts[pi], cur)  # strict asc index -> distinct
            cur.pop()

    rec(0, n, [])
    return res


def partitions_reps(allowed_parts, n):
    """All partitions of n into parts from allowed_parts with repetitions allowed."""
    res = []

    def rec(k, remaining, cur):
        if remaining == 0:
            res.append(list(cur))
            return
        for pi in range(k, len(allowed_parts)):
            if allowed_parts[pi] > remaining:
                break
            cur.append(allowed_parts[pi])
            rec(pi, remaining - allowed_parts[pi], cur)  # non-decreasing index -> reps
            cur.pop()

    rec(0, n, [])
    return res


def brute_A(n: int) -> int:
    allowed = [p for p in range(1, n + 1) if p % 3 in (1, 2)]
    return len(partitions_distinct(allowed, n))


def brute_B(n: int) -> int:
    allowed = [p for p in range(1, n + 1) if p % 6 in (1, 5)]
    return len(partitions_reps(allowed, n))


# --------------------------------------------------------------------------
# Witness listing
# --------------------------------------------------------------------------
def witnesses(n: int) -> tuple[list[list[int]], list[list[int]]]:
    allowedA = [p for p in range(1, n + 1) if p % 3 in (1, 2)]
    allowedB = [p for p in range(1, n + 1) if p % 6 in (1, 5)]
    return partitions_distinct(allowedA, n), partitions_reps(allowedB, n)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=150, help="certify A(n)==B(n) for 0<=n<=N (default 150)")
    ap.add_argument("--witness-max", type=int, default=12, help="list witnesses for n up to this")
    args = ap.parse_args()

    N = args.N
    assert N >= 50, "acceptance requires N >= 50"

    # ---- main certificate (Method 1, DP) ----
    a_seqs = [parts_mod3_A(n) for n in range(N + 1)]
    b_seqs = [parts_mod6_reps_B(n) for n in range(N + 1)]
    mismatches = [n for n in range(N + 1) if a_seqs[n] != b_seqs[n]]

    n0 = (a_seqs[0], b_seqs[0])
    print(f"Certificate: A(n)==B(n) for all 0<=n<=N (N={N})")
    print(f"  empty-partition convention n=0: A(0)={a_seqs[0]}, B(0)={b_seqs[0]}  (expected 1,1)")
    if mismatches:
        print(f"  FAIL: mismatches at n = {mismatches[:20]} ...")
        return 1
    print(f"  PASS: A(n)==B(n) for all 0..{N} (no mismatches).")

    # ---- independent brute-force cross-check on small n ----
    brute_mism = []
    small = min(N, 24)
    for n in range(small + 1):
        if brute_A(n) != a_seqs[n] or brute_B(n) != b_seqs[n]:
            brute_mism.append(n)
    print(f"Independent brute-force cross-check n=0..{small}: "
          + ("PASS" if not brute_mism else f"FAIL at {brute_mism}"))
    if brute_mism:
        return 1

    # ---- witnesses ----
    print(f"\nWitnesses (explicit partition lists), n up to {min(args.witness_max, small)}:")
    for n in range(min(args.witness_max, small) + 1):
        wa, wb = witnesses(n)
        print(f"  n={n:>2}: A={len(wa):>3}  B={len(wb):>3}   "
              + f"| A e.g. {wa[0] if wa else '()'}   B e.g. {wb[0] if wb else '()'}")
        if len(wa) != len(wb):
            print(f"    MISMATCH at n={n}")
            return 1

    # ---- swapped-pairing landmine guard (hard stop) ----
    # swapped A': DISTINCT parts ≡ ±1 mod6 ; swapped B': reps parts ≡1,2 mod3
    def sw_A(n: int) -> int:
        allowed = [p for p in range(1, n + 1) if p % 6 in (1, 5)]
        return len(partitions_distinct(allowed, n))
    def sw_B(n: int) -> int:
        allowed = [p for p in range(1, n + 1) if p % 3 in (1, 2)]
        return len(partitions_reps(allowed, n))
    print("\nSwapped-pairing guard (must FAIL, i.e. be rejected as the theorem):")
    sw_bad = [n for n in range(0, 16) if sw_A(n) == sw_B(n)]
    print(f"  n=2: swapped A'(2)={sw_A(2)} vs swapped B'(2)={sw_B(2)}  -> {'FAIL (as expected)' if sw_A(2)!=sw_B(2) else 'WARNING: equal?!'}")
    print(f"  Where swapped pairing agrees on n=0..15: n = {sw_bad}  (only n=0,1 must agree trivially; n=2 must differ)")
    if sw_A(2) == sw_B(2):
        print("  ERROR: swapped pairing matched at n=2 — definition landmine not confirmed")
        return 1

    print("\nRESULT: PASS (Level A certificate complete)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
