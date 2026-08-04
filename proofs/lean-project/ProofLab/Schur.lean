-- Formalization seed (Level B) for Schur's partition theorem.
-- Problem: schur-partition  (STATEMENT.md pinned 2026-08-04)
-- Attack: OPE-26
--
-- Classical 1926 theorem (I. Schur; Andrews, The Theory of Partitions):
--   For every n >= 0,  A(n) == B(n)  where
--     A(n) = # partitions of n into DISTINCT parts each == 1 or 2 (mod 3)
--     B(n) = # partitions of n into parts each == 1 or 5 (mod 6), reps allowed
--
-- This file is a *computational* seed only (Level B): it defines A and B as
-- computable counting functions and gives sorry-free small-n equalities by
-- native_decide.  It is NOT a proof of the general theorem (that is Level C).
-- Default no claim; status stays formalize-only / informal.
--
-- Convention: n = 0 has exactly one (empty) partition on both sides.
import Mathlib

namespace ProofLab.Schur

/-- Part allowed on the A side: == 1 or 2 (mod 3). -/
def partAllowedA (p : ℕ) : Bool :=
  p % 3 = 1 || p % 3 = 2

/-- Part allowed on the B side: == 1 or 5 (mod 6) (i.e. ±1 mod 6). -/
def partAllowedB (p : ℕ) : Bool :=
  p % 6 = 1 || p % 6 = 5

/-- Candidate parts (positive, allowed) up to n, in ascending order. -/
def partsUpToA (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun p => 0 < p && partAllowedA p)

def partsUpToB (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun p => 0 < p && partAllowedB p)

/-- Number of DISTINCT-part partitions of `t` using (a prefix of) `parts`.
Structural recursion on the part list; each part used at most once. -/
def countDistinct : List ℕ → ℕ → ℕ
  | [], t => if t = 0 then 1 else 0
  | p :: ps, t =>
      (if p ≤ t then countDistinct ps (t - p) else 0)
        + countDistinct ps t

/-- Number of unrestricted-multiplicity partitions of `t` using `parts`
(part repetitions allowed). Structural recursion on the part list; for each
part we try multiplicities 0..t/p. -/
def countUnbounded : List ℕ → ℕ → ℕ
  | [], t => if t = 0 then 1 else 0
  | p :: ps, t =>
      let maxm := t / p
      (List.range (maxm + 1)).foldl
        (fun acc m => acc + countUnbounded ps (t - m * p)) 0

/-- A(n): # partitions of n into distinct parts == 1 or 2 (mod 3). -/
def A (n : ℕ) : ℕ := countDistinct (partsUpToA n) n

/-- B(n): # partitions of n into parts == 1 or 5 (mod 6), reps allowed. -/
def B (n : ℕ) : ℕ := countUnbounded (partsUpToB n) n

/-- Empty-partition convention: A(0) = B(0) = 1. -/
example : A 0 = B 0 := by native_decide
example : A 0 = 1 := by native_decide
example : B 0 = 1 := by native_decide

-- Sorry-free small-n checks that A(n) == B(n).
example : A 1 = B 1 := by native_decide
example : A 2 = B 2 := by native_decide
example : A 3 = B 3 := by native_decide
example : A 4 = B 4 := by native_decide
example : A 5 = B 5 := by native_decide
example : A 6 = B 6 := by native_decide
example : A 7 = B 7 := by native_decide
example : A 8 = B 8 := by native_decide
example : A 9 = B 9 := by native_decide
example : A 10 = B 10 := by native_decide
example : A 11 = B 11 := by native_decide
example : A 12 = B 12 := by native_decide

-- Worked example n=5 pin from STATEMENT.md:
--   A(5) = {5}, {4,1}  -> 2 ;  B(5) = {5}, {1,1,1,1,1} -> 2
example : A 5 = 2 := by native_decide
example : B 5 = 2 := by native_decide

-- Definition landmine guard: the SWAPPED pairing (unrestricted parts ==1,2 mod3
-- against DISTINCT parts ==±1 mod6) FAILS at n=2.  We pin the correct defs above;
-- here we just record that n=2 has A(2)=B(2)=1 under the CORRECT pairing.
example : A 2 = 1 := by native_decide
example : B 2 = 1 := by native_decide

end ProofLab.Schur
