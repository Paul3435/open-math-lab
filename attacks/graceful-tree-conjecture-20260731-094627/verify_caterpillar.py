#!/usr/bin/env python3
"""
Graceful labeling verification for caterpillar trees with n <= 12 vertices.

A caterpillar tree is a tree where all non-leaf vertices lie on a single path (spine).
A graceful labeling assigns distinct labels from {0, 1, ..., m} to vertices
such that edge labels {|f(u) - f(v)| : uv in E} = {1, 2, ..., m}.
"""

import itertools
import json
import time
from typing import List, Tuple, Set, Optional, Dict


class CaterpillarTree:
    """Represents a caterpillar tree by its spine length and leaf configuration."""

    def __init__(self, spine_length: int, leaf_config: Tuple[int, ...]):
        """
        Args:
            spine_length: Number of vertices on the spine (>= 1)
            leaf_config: Tuple of leaf counts at each spine vertex
        """
        self.spine_length = spine_length
        self.leaf_config = leaf_config
        self.n_vertices = spine_length + sum(leaf_config)
        self.n_edges = self.n_vertices - 1  # Tree property

    def __repr__(self):
        return f"Caterpillar(spine={self.spine_length}, leaves={self.leaf_config})"

    def get_edges(self) -> List[Tuple[int, int]]:
        """
        Returns edge list. Vertices numbered as:
        - Spine vertices: 0 to spine_length-1
        - Leaves: spine_length onwards
        """
        edges = []

        # Spine edges
        for i in range(self.spine_length - 1):
            edges.append((i, i + 1))

        # Leaf edges
        leaf_id = self.spine_length
        for spine_idx, num_leaves in enumerate(self.leaf_config):
            for _ in range(num_leaves):
                edges.append((spine_idx, leaf_id))
                leaf_id += 1

        return edges


def enumerate_caterpillar_trees(n: int) -> List[CaterpillarTree]:
    """
    Enumerate all non-isomorphic caterpillar trees with n vertices.

    Strategy: For each spine length s (1 <= s <= n), partition remaining
    (n - s) leaves among s spine vertices. Use ordered partitions to avoid
    counting mirror images twice.
    """
    if n == 1:
        return [CaterpillarTree(1, ())]

    trees = []

    for spine_length in range(1, n + 1):
        num_leaves = n - spine_length

        if num_leaves < 0:
            continue

        # Generate partitions of num_leaves into spine_length parts (including 0s)
        # Use canonical ordering to avoid symmetry: non-increasing from middle out
        for partition in partitions_with_zeros(num_leaves, spine_length):
            trees.append(CaterpillarTree(spine_length, partition))

    return trees


def partitions_with_zeros(total: int, num_parts: int) -> List[Tuple[int, ...]]:
    """
    Generate all ways to partition 'total' into 'num_parts' non-negative integers.
    To avoid counting symmetric caterpillars, we use canonical form:
    - For odd spine length: center is anchor, non-increasing outward
    - For even spine length: symmetric pairs from middle

    For simplicity, we'll generate all partitions and filter for canonical form.
    """
    if num_parts == 0:
        return [()] if total == 0 else []

    if num_parts == 1:
        return [(total,)]

    partitions = []

    # Generate all weak compositions (ordered partitions with zeros)
    def generate(remaining, parts_left, current):
        if parts_left == 0:
            if remaining == 0:
                partitions.append(tuple(current))
            return

        for i in range(remaining + 1):
            generate(remaining - i, parts_left - 1, current + [i])

    generate(total, num_parts, [])

    # Filter for canonical form to remove symmetries
    canonical = []
    for p in partitions:
        if is_canonical_partition(p):
            canonical.append(p)

    return canonical


def is_canonical_partition(partition: Tuple[int, ...]) -> bool:
    """
    Check if partition is in canonical form (avoids counting reflections).
    For caterpillars, we want lexicographically minimal among {p, reversed(p)}.
    """
    rev = tuple(reversed(partition))
    return partition <= rev


def is_graceful_labeling(edges: List[Tuple[int, int]],
                         labeling: List[int]) -> bool:
    """
    Check if a labeling is graceful.

    Args:
        edges: List of edges (u, v)
        labeling: List of vertex labels (labeling[i] is label of vertex i)

    Returns:
        True if labeling is graceful, False otherwise
    """
    n_vertices = len(labeling)
    n_edges = len(edges)

    # Check labels are distinct and in range [0, n_edges]
    if len(set(labeling)) != n_vertices:
        return False

    if any(label < 0 or label > n_edges for label in labeling):
        return False

    # Check edge labels are exactly {1, 2, ..., n_edges}
    edge_labels = set()
    for u, v in edges:
        edge_label = abs(labeling[u] - labeling[v])
        if edge_label == 0 or edge_label > n_edges:
            return False
        edge_labels.add(edge_label)

    return edge_labels == set(range(1, n_edges + 1))


def find_graceful_labeling(tree: CaterpillarTree,
                           timeout_seconds: float = 60.0) -> Optional[List[int]]:
    """
    Find a graceful labeling for the tree using backtracking.

    Returns:
        A graceful labeling (list of vertex labels) if found, None otherwise.
    """
    edges = tree.get_edges()
    n_vertices = tree.n_vertices
    m = tree.n_edges

    start_time = time.time()

    # Try all permutations (for small trees, this is feasible)
    # For larger trees, we'd use smarter backtracking
    if n_vertices <= 8:
        # Brute force for small cases
        for perm in itertools.permutations(range(m + 1), n_vertices):
            if time.time() - start_time > timeout_seconds:
                return None

            if is_graceful_labeling(edges, list(perm)):
                return list(perm)
    else:
        # Backtracking for larger cases
        return backtrack_graceful(edges, n_vertices, m, timeout_seconds, start_time)

    return None


def backtrack_graceful(edges: List[Tuple[int, int]],
                       n_vertices: int,
                       m: int,
                       timeout_seconds: float,
                       start_time: float,
                       labeling: Optional[List[int]] = None,
                       used_labels: Optional[Set[int]] = None,
                       used_edge_labels: Optional[Set[int]] = None,
                       vertex_idx: int = 0) -> Optional[List[int]]:
    """
    Backtracking search for graceful labeling.
    """
    if labeling is None:
        labeling = [-1] * n_vertices
        used_labels = set()
        used_edge_labels = set()
        vertex_idx = 0

    if time.time() - start_time > timeout_seconds:
        return None

    # Base case: all vertices labeled
    if vertex_idx == n_vertices:
        if len(used_edge_labels) == m and used_edge_labels == set(range(1, m + 1)):
            return labeling[:]
        return None

    # Try each available label for current vertex
    for label in range(m + 1):
        if label in used_labels:
            continue

        # Assign label
        labeling[vertex_idx] = label
        used_labels.add(label)

        # Check edge constraints for edges involving this vertex
        valid = True
        new_edge_labels = set()

        for u, v in edges:
            if u == vertex_idx and labeling[v] != -1:
                edge_label = abs(labeling[u] - labeling[v])
                if edge_label == 0 or edge_label > m or edge_label in used_edge_labels:
                    valid = False
                    break
                new_edge_labels.add(edge_label)
            elif v == vertex_idx and labeling[u] != -1:
                edge_label = abs(labeling[u] - labeling[v])
                if edge_label == 0 or edge_label > m or edge_label in used_edge_labels:
                    valid = False
                    break
                new_edge_labels.add(edge_label)

        if valid:
            # Update edge labels and recurse
            for el in new_edge_labels:
                used_edge_labels.add(el)

            result = backtrack_graceful(edges, n_vertices, m, timeout_seconds,
                                       start_time, labeling, used_labels,
                                       used_edge_labels, vertex_idx + 1)

            if result is not None:
                return result

            # Backtrack edge labels
            for el in new_edge_labels:
                used_edge_labels.remove(el)

        # Backtrack label
        labeling[vertex_idx] = -1
        used_labels.remove(label)

    return None


def verify_caterpillars(max_n: int = 12) -> Dict:
    """
    Verify graceful labeling for all caterpillar trees with n <= max_n vertices.

    Returns:
        Dictionary with results by vertex count
    """
    results = {}

    for n in range(1, max_n + 1):
        print(f"\n=== Verifying caterpillar trees with n={n} vertices ===")

        trees = enumerate_caterpillar_trees(n)
        print(f"Found {len(trees)} non-isomorphic caterpillar trees")

        success_count = 0
        failed_trees = []
        timeout_trees = []
        labelings = []

        for i, tree in enumerate(trees):
            print(f"  Tree {i+1}/{len(trees)}: {tree} ... ", end="", flush=True)

            start = time.time()
            labeling = find_graceful_labeling(tree, timeout_seconds=60.0)
            elapsed = time.time() - start

            if labeling is not None:
                # Verify the labeling
                edges = tree.get_edges()
                if is_graceful_labeling(edges, labeling):
                    print(f"✓ graceful (found in {elapsed:.3f}s)")
                    success_count += 1
                    labelings.append({
                        "tree": str(tree),
                        "labeling": labeling,
                        "time": elapsed
                    })
                else:
                    print(f"✗ ERROR: invalid labeling found!")
                    failed_trees.append(tree)
            else:
                if elapsed >= 59.5:  # Near timeout
                    print(f"⊗ timeout ({elapsed:.1f}s)")
                    timeout_trees.append(tree)
                else:
                    print(f"✗ no labeling found ({elapsed:.3f}s)")
                    failed_trees.append(tree)

        results[n] = {
            "total_trees": len(trees),
            "graceful": success_count,
            "failed": len(failed_trees),
            "timeout": len(timeout_trees),
            "failed_trees": [str(t) for t in failed_trees],
            "timeout_trees": [str(t) for t in timeout_trees],
            "labelings": labelings
        }

        print(f"\nSummary for n={n}: {success_count}/{len(trees)} graceful, "
              f"{len(failed_trees)} failed, {len(timeout_trees)} timeout")

    return results


def main():
    print("Graceful Caterpillar Tree Verification")
    print("=" * 60)
    print("Verifying graceful labelings for caterpillar trees")
    print("with n <= 12 vertices\n")

    start_time = time.time()
    results = verify_caterpillars(max_n=12)
    total_time = time.time() - start_time

    # Write results to JSON
    output = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "total_runtime_seconds": total_time,
        "results_by_n": results
    }

    with open("RESULTS.json", "w") as f:
        json.dump(output, f, indent=2)

    # Generate summary table
    print("\n" + "=" * 60)
    print("FINAL SUMMARY TABLE")
    print("=" * 60)
    print(f"{'n':>3} | {'Trees':>6} | {'Graceful':>8} | {'Failed':>6} | {'Timeout':>7}")
    print("-" * 60)

    total_trees = 0
    total_graceful = 0
    total_failed = 0
    total_timeout = 0

    for n in range(1, 13):
        r = results[n]
        total_trees += r["total_trees"]
        total_graceful += r["graceful"]
        total_failed += r["failed"]
        total_timeout += r["timeout"]

        print(f"{n:3} | {r['total_trees']:6} | {r['graceful']:8} | "
              f"{r['failed']:6} | {r['timeout']:7}")

    print("-" * 60)
    print(f"{'TOT':>3} | {total_trees:6} | {total_graceful:8} | "
          f"{total_failed:6} | {total_timeout:7}")
    print("=" * 60)

    if total_failed == 0 and total_timeout == 0:
        print("\n✓ SUCCESS: All caterpillar trees with n <= 12 are graceful!")
    else:
        print(f"\n⊗ RESULT: {total_graceful}/{total_trees} trees verified as graceful")
        if total_failed > 0:
            print(f"  {total_failed} trees had NO graceful labeling found")
        if total_timeout > 0:
            print(f"  {total_timeout} trees timed out (may be graceful)")

    print(f"\nResults saved to RESULTS.json")
    print(f"Total runtime: {total_time:.1f} seconds")


if __name__ == "__main__":
    main()
