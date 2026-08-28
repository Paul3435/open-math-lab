#!/usr/bin/env python3
"""Offline search: 2-colouring of [0,n) with no monochromatic 4-AP.

Used for OPE-455 witness generation. Lean re-checks the exported colouring
with native_decide — this script is not a proof.
"""
from __future__ import annotations

import argparse
import time


def has_mono4_ending_at(c: list[int], pos: int) -> bool:
    col = c[pos]
    d = 1
    while True:
        a = pos - 3 * d
        if a < 0:
            return False
        if c[a] == col and c[a + d] == col and c[a + 2 * d] == col:
            return True
        d += 1


def full_verify(c: list[int]) -> bool:
    n = len(c)
    for a in range(n):
        for d in range(1, n):
            if a + 3 * d >= n:
                break
            cols = {c[a], c[a + d], c[a + 2 * d], c[a + 3 * d]}
            if len(cols) == 1:
                return False
    return True


def search(n: int, timeout: float = 60.0):
    c = [-1] * n
    t0 = time.time()
    nodes = 0

    def bt(i: int):
        nonlocal nodes
        nodes += 1
        if time.time() - t0 > timeout:
            return None
        if i == n:
            return c[:]
        for col in (0, 1):
            c[i] = col
            if not has_mono4_ending_at(c, i):
                r = bt(i + 1)
                if r is not None:
                    return r
        c[i] = -1
        return None

    sol = bt(0)
    return sol, time.time() - t0, nodes


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=34)
    ap.add_argument("--timeout", type=float, default=60.0)
    args = ap.parse_args()
    sol, dt, nodes = search(args.n, args.timeout)
    if sol is None:
        print(f"FAIL n={args.n} dt={dt:.3f}s nodes={nodes}")
        raise SystemExit(1)
    s = "".join(str(x) for x in sol)
    mask = sum(1 << i for i, b in enumerate(sol) if b)
    ok = full_verify(sol)
    print(f"OK n={args.n} dt={dt:.3f}s nodes={nodes}")
    print(f"coloring={s}")
    print(f"mask={mask}")
    print(f"full_verify_ok={ok}")
    if not ok:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
