#!/usr/bin/env python3
"""OPE-1038 Level B: timeboxed EqSystem search matching ProofLab/KrennGu.lean.

Encoding pin (STATEMENT Level B option 2; Lean Level A on main):
  Weight[i][j][a][b]  (i < j used by edgeWeight; smaller label first)
  pmSum(ι) = sum over perfect matchings M of product_e W[lo][hi][ι lo][ι hi]
  EqSystem iff pmSum = 1 on constant colourings and 0 otherwise.

Ring: {-1,0,1} (STATEMENT stop-rule). Unrestricted Complex is not started.

Method: exhaustive-on-a-tiny-weight-set + heuristic local search.
Not SAT, not Gröbner (no solver / no Sage on this host).

Default no claim. Not the €3000 prize. Do not email Krenn/Leitner.
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import random
import sys
import time
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

Edge = Tuple[int, int]
Matching = Tuple[Edge, ...]
Coloring = Tuple[int, ...]


def perfect_matchings(n: int) -> List[Matching]:
    """All perfect matchings of K_n as tuples of (lo, hi) with lo < hi."""
    if n % 2:
        raise ValueError("n must be even")
    verts = list(range(n))

    def rec(remaining: List[int]) -> List[Matching]:
        if not remaining:
            return [()]
        a = remaining[0]
        out: List[Matching] = []
        for i in range(1, len(remaining)):
            b = remaining[i]
            lo, hi = (a, b) if a < b else (b, a)
            rest = remaining[1:i] + remaining[i + 1 :]
            for tail in rec(rest):
                out.append(((lo, hi),) + tail)
        return out

    return rec(verts)


def edge_index_map(n: int) -> Tuple[List[Edge], Dict[Edge, int]]:
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    return edges, {e: k for k, e in enumerate(edges)}


def one_factorization(n: int) -> List[Matching]:
    """Circle 1-factorization of K_n (n even). Vertex n-1 is infinity."""
    assert n % 2 == 0
    inf = n - 1
    t = n // 2
    factors: List[Matching] = []
    for k in range(n - 1):
        pairs: List[Edge] = []
        a, b = (inf, k) if inf < k else (k, inf)
        pairs.append((a, b))
        for j in range(1, t):
            u = (k + j) % (n - 1)
            v = (k - j) % (n - 1)
            lo, hi = (u, v) if u < v else (v, u)
            pairs.append((lo, hi))
        factors.append(tuple(sorted(pairs)))
    return factors


def cycle_edges(n: int) -> List[Edge]:
    out: List[Edge] = []
    for i in range(n):
        j = (i + 1) % n
        out.append((i, j) if i < j else (j, i))
    return out


def zero_weights(n: int, d: int) -> List[List[int]]:
    """W[e][a*d + b] in {-1,0,1}."""
    m = n * (n - 1) // 2
    return [[0] * (d * d) for _ in range(m)]


def set_w(W: List[List[int]], eidx: Dict[Edge, int], d: int,
          i: int, j: int, a: int, b: int, val: int) -> None:
    lo, hi = (i, j) if i < j else (j, i)
    if i < j:
        W[eidx[(lo, hi)]][a * d + b] = val
    else:
        # Lean edgeWeight reads smaller-index first only; still store both
        # orientations when the caller passes unordered cycle lookup.
        W[eidx[(lo, hi)]][b * d + a] = val


def set_mono(W: List[List[int]], eidx: Dict[Edge, int], d: int,
             edge: Edge, color: int, val: int) -> None:
    W[eidx[edge]][color * d + color] = val


def cycle_even_weight(n: int, d: int, eidx: Dict[Edge, int]) -> List[List[int]]:
    """C_n alternating monochromatic d=2 unit weights (Lean cycle4Weight for n=4)."""
    W = zero_weights(n, d)
    for i in range(n):
        j = (i + 1) % n
        color = i % 2
        if color >= d:
            continue
        lo, hi = (i, j) if i < j else (j, i)
        # edgeWeight uses W[lo][hi][ι lo][ι hi]; colour of the edge is i%2
        # Independent of traversal direction: both endpoints get `color`.
        W[eidx[(lo, hi)]][color * d + color] = 1
    return W


def matching_to_eids(M: Matching, eidx: Dict[Edge, int]) -> Tuple[int, ...]:
    return tuple(eidx[e] for e in M)


def pmsum(W: List[List[int]], coloring: Sequence[int], d: int,
          matchings_eids: Sequence[Tuple[int, ...]],
          matchings: Sequence[Matching]) -> int:
    total = 0
    for eids, edges in zip(matchings_eids, matchings):
        prod = 1
        for eid, (i, j) in zip(eids, edges):
            prod *= W[eid][coloring[i] * d + coloring[j]]
            if prod == 0:
                break
        total += prod
    return total


def is_constant(coloring: Sequence[int]) -> bool:
    return all(c == coloring[0] for c in coloring)


def eqsystem_residual(W: List[List[int]], n: int, d: int,
                      matchings_eids: Sequence[Tuple[int, ...]],
                      matchings: Sequence[Matching],
                      abort_at: Optional[int] = None) -> Tuple[int, int, Optional[Coloring]]:
    """L1 residual vs EqSystem targets. Returns (residual, n_checked, first_bad)."""
    residual = 0
    checked = 0
    first_bad: Optional[Coloring] = None
    for col in itertools.product(range(d), repeat=n):
        target = 1 if is_constant(col) else 0
        val = pmsum(W, col, d, matchings_eids, matchings)
        checked += 1
        diff = abs(val - target)
        if diff:
            residual += diff
            if first_bad is None:
                first_bad = col
            if abort_at is not None and residual >= abort_at:
                return residual, checked, first_bad
    return residual, checked, first_bad


def filter_matchings_by_support(matchings: Sequence[Matching],
                                support: Sequence[Edge]) -> List[Matching]:
    s = set(support)
    return [M for M in matchings if all(e in s for e in M)]


def check_eqsystem(W: List[List[int]], n: int, d: int,
                   matchings_eids: Sequence[Tuple[int, ...]],
                   matchings: Sequence[Matching]) -> bool:
    res, _, _ = eqsystem_residual(W, n, d, matchings_eids, matchings, abort_at=1)
    return res == 0


def residual_monochromatic_support(
    n: int,
    d: int,
    supp_pms: Sequence[Matching],
    edge_color: Dict[Edge, int],
    edge_weight: Dict[Edge, int],
) -> Tuple[int, Optional[Coloring]]:
    """EqSystem L1 residual when every support edge is a single mono slot.

    Each support PM induces at most one colouring (the colour of the unique
    edge covering each vertex). All other colourings have pmSum 0 automatically.
    """
    acc: Dict[Coloring, int] = {}
    for M in supp_pms:
        col = [-1] * n
        prod = 1
        ok = True
        for e in M:
            if e not in edge_color:
                ok = False
                break
            c = edge_color[e]
            w = edge_weight[e]
            i, j = e
            if col[i] not in (-1, c) or col[j] not in (-1, c):
                ok = False
                break
            col[i] = c
            col[j] = c
            prod *= w
        if not ok:
            continue
        key = tuple(col)
        acc[key] = acc.get(key, 0) + prod
    residual = 0
    first_bad: Optional[Coloring] = None
    for c in range(d):
        const = tuple([c] * n)
        diff = abs(acc.get(const, 0) - 1)
        if diff:
            residual += diff
            if first_bad is None:
                first_bad = const
    for col, val in acc.items():
        if is_constant(col):
            continue
        if val:
            residual += abs(val)
            if first_bad is None:
                first_bad = col
    return residual, first_bad


# ---------------------------------------------------------------------------
# Search arms
# ---------------------------------------------------------------------------

def arm_sanity(n_d_pairs: List[Tuple[int, int]], deadline: float) -> dict:
    report: dict = {"arm": "sanity_cycle_d2", "checks": []}
    for n, d in n_d_pairs:
        if time.time() > deadline:
            report["timeout"] = True
            break
        edges, eidx = edge_index_map(n)
        pms = perfect_matchings(n)
        eids = [matching_to_eids(M, eidx) for M in pms]
        W = cycle_even_weight(n, d, eidx)
        ok = check_eqsystem(W, n, d, eids, pms)
        edge_color: Dict[Edge, int] = {}
        edge_weight: Dict[Edge, int] = {}
        for i in range(n):
            j = (i + 1) % n
            color = i % 2
            e = (i, j) if i < j else (j, i)
            edge_color[e] = color
            edge_weight[e] = 1
        supp = filter_matchings_by_support(pms, list(edge_color))
        fast_res, _ = residual_monochromatic_support(n, d, supp, edge_color, edge_weight)
        ok = ok and fast_res == 0
        report["checks"].append({
            "n": n, "d": d, "ok": ok,
            "n_matchings": len(pms),
            "n_colorings": d ** n,
            "fast_mono_residual": fast_res,
            "construction": "even_cycle_alternating_mono_unit",
        })
        if not ok:
            report["failed"] = True
    report["all_ok"] = all(c["ok"] for c in report["checks"]) and not report.get("failed")
    return report


def arm_signed_one_factors(n: int, d: int, deadline: float,
                           rng: random.Random) -> dict:
    """Exhaustive ±1 signs on d edge-disjoint 1-factors, monochromatic.

    Weight-set: each of d 1-factors from the circle factorization is coloured
    with a distinct colour; each of its n/2 edges has weight ±1 on that
    monochromatic slot; all other slots 0. Finite, fully enumerated when time
    allows; otherwise partial.
    """
    edges, eidx = edge_index_map(n)
    all_pms = perfect_matchings(n)
    factors = one_factorization(n)
    assert len(factors) == n - 1
    triples = list(itertools.combinations(range(len(factors)), d))
    n_edges_per = n // 2
    n_signed = d * n_edges_per
    report = {
        "arm": "exhaustive_signed_one_factors_mono",
        "n": n, "d": d, "ring": "{-1,1} on support, 0 elsewhere",
        "n_factors": len(factors),
        "n_factor_tuples": len(triples),
        "n_sign_bits": n_signed,
        "sign_patterns_per_tuple": 2 ** n_signed,
        "tried": 0,
        "skipped_constant_fail": 0,
        "witnesses": [],
        "exhausted": False,
        "timeout": False,
        "best_residual": None,
        "best_desc": None,
    }
    best_res = None
    for tup in triples:
        if time.time() > deadline:
            report["timeout"] = True
            break
        support: List[Edge] = []
        for fi in tup:
            support.extend(factors[fi])
        supp_pms = filter_matchings_by_support(all_pms, support)
        for signs in itertools.product((-1, 1), repeat=n_signed):
            if time.time() > deadline:
                report["timeout"] = True
                break
            ok_const = True
            for c in range(d):
                chunk = signs[c * n_edges_per:(c + 1) * n_edges_per]
                prod = 1
                for s in chunk:
                    prod *= s
                if prod != 1:
                    ok_const = False
                    break
            report["tried"] += 1
            if not ok_const:
                report["skipped_constant_fail"] += 1
                continue
            edge_color: Dict[Edge, int] = {}
            edge_weight: Dict[Edge, int] = {}
            k = 0
            for c, fi in enumerate(tup):
                for e in factors[fi]:
                    edge_color[e] = c
                    edge_weight[e] = signs[k]
                    k += 1
            res, bad = residual_monochromatic_support(
                n, d, supp_pms, edge_color, edge_weight
            )
            if best_res is None or res < best_res:
                best_res = res
                report["best_residual"] = res
                report["best_desc"] = {
                    "factors": list(tup),
                    "signs": list(signs),
                    "n_support_pms": len(supp_pms),
                    "first_bad": list(bad) if bad is not None else None,
                }
            if res == 0:
                report["witnesses"].append({
                    "factors": list(tup),
                    "signs": list(signs),
                    "n_support_pms": len(supp_pms),
                })
                report["best_residual"] = 0
                return report
        if report["timeout"]:
            break
    else:
        report["exhausted"] = True
    report["best_residual"] = best_res
    return report


def arm_cycle_plus_one_factor_signs(n: int, d: int, deadline: float) -> dict:
    """C_n d=2 unit cycle (colours 0,1) plus one extra 1-factor in colour 2, ±1.

    Tiny: (n-1) candidate extra factors × 2^{n/2} signs on the extra matching.
    Known C_n d=2 is a positive witness; this asks whether a third colour
    1-factor with signs yields EqSystem at d=3.
    """
    edges, eidx = edge_index_map(n)
    all_pms = perfect_matchings(n)
    factors = one_factorization(n)
    cycle = cycle_edges(n)
    n_half = n // 2
    report = {
        "arm": "cycle_d2_plus_signed_1factor_color2",
        "n": n, "d": d, "ring": "{-1,0,1}",
        "tried": 0,
        "witnesses": [],
        "exhausted": False,
        "timeout": False,
        "best_residual": None,
    }
    best = None
    for fi, F in enumerate(factors):
        if time.time() > deadline:
            report["timeout"] = True
            break
        support = list(dict.fromkeys(cycle + list(F)))
        supp_pms = filter_matchings_by_support(all_pms, support)
        # Cycle edges: colour i%2 with weight 1, using the same rule as
        # cycle_even_weight (owner vertex i of directed step i→i+1).
        cycle_color: Dict[Edge, int] = {}
        cycle_weight: Dict[Edge, int] = {}
        for i in range(n):
            j = (i + 1) % n
            color = i % 2
            e = (i, j) if i < j else (j, i)
            cycle_color[e] = color
            cycle_weight[e] = 1
        for signs in itertools.product((-1, 1), repeat=n_half):
            if time.time() > deadline:
                report["timeout"] = True
                break
            report["tried"] += 1
            edge_color = dict(cycle_color)
            edge_weight = dict(cycle_weight)
            overlap = False
            for e, s in zip(F, signs):
                if e in edge_color and edge_color[e] != 2:
                    # Extra factor reuses a cycle edge: keep both only if same
                    # colour; otherwise this weight-set is not a single mono slot.
                    overlap = True
                    break
                edge_color[e] = 2 if d > 2 else 0
                edge_weight[e] = s
            if overlap:
                continue
            res, bad = residual_monochromatic_support(
                n, d, supp_pms, edge_color, edge_weight
            )
            if best is None or res < best:
                best = res
                report["best_residual"] = res
                report["best_desc"] = {
                    "extra_factor": fi,
                    "signs": list(signs),
                    "first_bad": list(bad) if bad is not None else None,
                    "n_support_pms": len(supp_pms),
                }
            if res == 0:
                report["witnesses"].append({
                    "extra_factor": fi, "signs": list(signs)
                })
                return report
        if report["timeout"]:
            break
    else:
        report["exhausted"] = True
    return report


def random_sparse_W(n: int, d: int, eidx: Dict[Edge, int], rng: random.Random,
                    n_nonzero: int, bichromatic: bool) -> List[List[int]]:
    W = zero_weights(n, d)
    edges = list(eidx.keys())
    for _ in range(n_nonzero):
        e = rng.choice(edges)
        if bichromatic:
            a = rng.randrange(d)
            b = rng.randrange(d)
        else:
            a = b = rng.randrange(d)
        val = rng.choice((-1, 1))
        W[eidx[e]][a * d + b] = val
    return W


def mutate_W(W: List[List[int]], rng: random.Random) -> List[List[int]]:
    W2 = [row[:] for row in W]
    e = rng.randrange(len(W2))
    slot = rng.randrange(len(W2[e]))
    W2[e][slot] = rng.choice((-1, 0, 1))
    return W2


def arm_local_search(n: int, d: int, deadline: float, rng: random.Random,
                     bichromatic: bool, tag: str) -> dict:
    edges, eidx = edge_index_map(n)
    all_pms = perfect_matchings(n)
    eids = [matching_to_eids(M, eidx) for M in all_pms]
    report = {
        "arm": tag,
        "n": n, "d": d,
        "ring": "{-1,0,1}",
        "bichromatic": bichromatic,
        "method": "heuristic_hillclimb",
        "restarts": 0,
        "steps": 0,
        "witnesses": [],
        "timeout": False,
        "best_residual": None,
    }
    best = None
    # Seed 1: even-cycle d=2 embedded in d colours.
    current = cycle_even_weight(n, d, eidx)
    while time.time() < deadline:
        report["restarts"] += 1
        res, checked, bad = eqsystem_residual(
            current, n, d, eids, all_pms, abort_at=None if n <= 6 else 8
        )
        # For n=8, abort_at=8 still walks until residual hits 8; cheap enough
        # because first mixed colourings fail fast on random W. For a fair
        # hill-climb use full residual when n=6, and a capped residual when n=8.
        if n >= 8:
            res, checked, bad = eqsystem_residual(
                current, n, d, eids, all_pms, abort_at=4
            )
        report["steps"] += 1
        if best is None or res < best:
            best = res
            report["best_residual"] = res
            report["best_desc"] = {
                "first_bad": list(bad) if bad is not None else None,
                "checked": checked,
            }
        if res == 0:
            # confirm full (no abort)
            full, _, _ = eqsystem_residual(current, n, d, eids, all_pms)
            if full == 0:
                report["witnesses"].append({"restart": report["restarts"]})
                report["best_residual"] = 0
                return report
            res = full
            if best is None or res < best:
                best = res
                report["best_residual"] = res
        # hill-climb a handful of mutations
        improved = False
        for _ in range(24):
            if time.time() >= deadline:
                break
            cand = mutate_W(current, rng)
            cres, _, _ = eqsystem_residual(
                cand, n, d, eids, all_pms, abort_at=(res + 1 if res is not None else 4)
            )
            report["steps"] += 1
            if cres < res:
                current = cand
                res = cres
                improved = True
                if res == 0:
                    full, _, _ = eqsystem_residual(current, n, d, eids, all_pms)
                    if full == 0:
                        report["witnesses"].append({"restart": report["restarts"]})
                        report["best_residual"] = 0
                        return report
                    res = full
                if best is None or res < best:
                    best = res
                    report["best_residual"] = res
        if not improved:
            current = random_sparse_W(
                n, d, eidx, rng,
                n_nonzero=rng.randint(n, n * 2),
                bichromatic=bichromatic,
            )
    report["timeout"] = True
    return report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timebox-83", type=float, default=120.0,
                    help="seconds for (N,D)=(8,3) search")
    ap.add_argument("--timebox-63", type=float, default=45.0,
                    help="seconds for fallback (6,3) if (8,3) has no witness")
    ap.add_argument("--seed", type=int, default=1038)
    ap.add_argument("--out", required=True, help="search_report.json path")
    args = ap.parse_args()

    t0 = time.time()
    rng = random.Random(args.seed)
    report: dict = {
        "issue": "OPE-1038",
        "problem_id": "krenn-gu",
        "method": "exhaustive-on-a-tiny-weight-set + heuristic local search",
        "ring": "{-1,0,1}",
        "encoding": "ProofLab.KrennGu EqSystem / pmSum / Weight (i<j first)",
        "claim": "none",
        "prize_claim": False,
        "started_unix": t0,
        "arms": [],
    }

    # --- Sanity (must pass before any search) ---
    sanity = arm_sanity([(4, 2), (6, 2), (8, 2)], deadline=t0 + 30)
    report["arms"].append(sanity)
    if not sanity.get("all_ok"):
        report["status"] = "error_sanity_failed"
        report["elapsed_sec"] = time.time() - t0
        _dump(args.out, report)
        print("SANITY FAILED", json.dumps(sanity, indent=2))
        return 2
    print("SANITY_OK cycle d=2 for n=4,6,8", flush=True)

    # --- (8,3) ---
    d83 = t0 + args.timebox_83
    print(f"ARM signed 1-factors (8,3) until {d83 - t0:.1f}s", flush=True)
    # Split the (8,3) budget: 55% exhaustive 1-factors, 20% cycle+factor, 25% local
    now = time.time()
    remain = max(1.0, d83 - now)
    a1 = arm_signed_one_factors(8, 3, now + remain * 0.50, rng)
    report["arms"].append(a1)
    print(
        f"  1factors tried={a1['tried']} exhausted={a1['exhausted']} "
        f"timeout={a1['timeout']} witnesses={len(a1['witnesses'])} "
        f"best={a1.get('best_residual')}",
        flush=True,
    )
    witness_83 = bool(a1["witnesses"])

    if not witness_83 and time.time() < d83:
        a2 = arm_cycle_plus_one_factor_signs(8, 3, min(d83, time.time() + remain * 0.25))
        report["arms"].append(a2)
        print(
            f"  cycle+1f tried={a2['tried']} exhausted={a2['exhausted']} "
            f"timeout={a2['timeout']} witnesses={len(a2['witnesses'])} "
            f"best={a2.get('best_residual')}",
            flush=True,
        )
        witness_83 = bool(a2["witnesses"])
    if not witness_83 and time.time() < d83:
        a3 = arm_local_search(8, 3, d83, rng, bichromatic=False,
                              tag="local_mono_83")
        report["arms"].append(a3)
        print(
            f"  local_mono restarts={a3['restarts']} steps={a3['steps']} "
            f"witnesses={len(a3['witnesses'])} best={a3.get('best_residual')}",
            flush=True,
        )
        witness_83 = bool(a3["witnesses"])
    if not witness_83 and time.time() < d83:
        a4 = arm_local_search(8, 3, d83, rng, bichromatic=True,
                              tag="local_bichrome_83")
        report["arms"].append(a4)
        print(
            f"  local_bi restarts={a4['restarts']} steps={a4['steps']} "
            f"witnesses={len(a4['witnesses'])} best={a4.get('best_residual')}",
            flush=True,
        )
        witness_83 = bool(a4["witnesses"])

    report["n8d3_witness"] = witness_83

    # --- Fallback n=6 if (8,3) has no witness ---
    if not witness_83:
        print("NO (8,3) witness on searched sets; fallback n=6 same ring", flush=True)
        d63 = time.time() + args.timebox_63
        b1 = arm_signed_one_factors(6, 3, time.time() + args.timebox_63 * 0.55, rng)
        report["arms"].append(b1)
        print(
            f"  n6 1factors tried={b1['tried']} exhausted={b1['exhausted']} "
            f"timeout={b1['timeout']} witnesses={len(b1['witnesses'])} "
            f"best={b1.get('best_residual')}",
            flush=True,
        )
        witness_63 = bool(b1["witnesses"])
        if not witness_63 and time.time() < d63:
            b2 = arm_cycle_plus_one_factor_signs(6, 3, min(d63, time.time() + args.timebox_63 * 0.2))
            report["arms"].append(b2)
            print(
                f"  n6 cycle+1f tried={b2['tried']} exhausted={b2['exhausted']} "
                f"witnesses={len(b2['witnesses'])} best={b2.get('best_residual')}",
                flush=True,
            )
            witness_63 = bool(b2["witnesses"])
        if not witness_63 and time.time() < d63:
            b3 = arm_local_search(6, 3, d63, rng, bichromatic=True,
                                  tag="local_bichrome_63")
            report["arms"].append(b3)
            print(
                f"  n6 local restarts={b3['restarts']} steps={b3['steps']} "
                f"witnesses={len(b3['witnesses'])} best={b3.get('best_residual')}",
                flush=True,
            )
            witness_63 = bool(b3["witnesses"])
        report["n6d3_witness"] = witness_63
    else:
        report["n6d3_witness"] = None
        report["fallback_n6"] = False

    elapsed = time.time() - t0
    report["elapsed_sec"] = round(elapsed, 3)
    any_witness = witness_83 or bool(report.get("n6d3_witness"))
    exhausted_any = any(a.get("exhausted") for a in report["arms"] if a.get("n") in (8, 6))
    if any_witness:
        report["status"] = "heuristic"
        report["outcome"] = "witness_on_stated_finite_weight_set"
    elif exhausted_any:
        report["status"] = "exhausted"
        report["outcome"] = "no_witness_on_stated_finite_weight_sets"
    else:
        report["status"] = "partial"
        report["outcome"] = "timeout_no_witness_on_searched_sets"

    _dump(args.out, report)
    print("STATUS", report["status"], "OUTCOME", report["outcome"],
          "elapsed", report["elapsed_sec"], flush=True)
    return 0


def _dump(path: str, obj: dict) -> None:
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    sys.exit(main())
