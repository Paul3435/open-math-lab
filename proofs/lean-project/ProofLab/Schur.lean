/-
Formalization attack (Level B → Level C ladder) for Schur's partition theorem.
Problem: schur-partition  (STATEMENT.md pinned 2026-08-04 — DO NOT ALTER pairing)
Attacks: OPE-26 (Level A/B seed) · OPE-424 (full-statement attack)

Classical 1926 theorem (I. Schur; Andrews, The Theory of Partitions):
  For every n ≥ 0,  A(n) = B(n)  where
    A(n) = # partitions of n into DISTINCT parts each ≡ 1 or 2 (mod 3)
    B(n) = # partitions of n into parts each ≡ 1 or 5 (mod 6), reps allowed

HARD PINS (OPE-12 class landmine — never swap):
  * A = DISTINCT + parts ≡ 1,2 (mod 3)
  * B = REPS OK  + parts ≡ ±1 (mod 6) i.e. 1 or 5 (mod 6)
  * A(0) = B(0) = 1 (empty partition)
  * The SWAPPED pairing fails at n = 2

This file:
  * Level B: computable A/B + sorry-free native_decide equalities through n ≤ 24
  * Level B+: Mathlib `Nat.Partition` Finset statements `schurA` / `schurB`
    and card equalities through n ≤ 12 (Fintype/composition blow-up limits decide)
  * Level C target name: `schur_partition` — FULL ∀ n, card equality.
    Not closed this run; residual risks documented in the attack log.
    Zero `sorry` / `admit` / custom `axiom` in this file.

formalize-only / known-classical. Default no external claim. No novelty claim.
-/
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat
open Nat.Partition

namespace ProofLab.Schur

/-! ## Level B — computable counters (DP-style structural recursion) -/

/-- Part allowed on the A side: ≡ 1 or 2 (mod 3). -/
def partAllowedA (p : ℕ) : Bool :=
  p % 3 = 1 || p % 3 = 2

/-- Part allowed on the B side: ≡ 1 or 5 (mod 6) (i.e. ±1 mod 6). -/
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

/-- A(n): # partitions of n into distinct parts ≡ 1 or 2 (mod 3). -/
def A (n : ℕ) : ℕ := countDistinct (partsUpToA n) n

/-- B(n): # partitions of n into parts ≡ 1 or 5 (mod 6), reps allowed. -/
def B (n : ℕ) : ℕ := countUnbounded (partsUpToB n) n

/-! ### Empty-partition convention + STATEMENT worked example -/

example : A 0 = B 0 := by native_decide
example : A 0 = 1 := by native_decide
example : B 0 = 1 := by native_decide

-- Worked example n=5 pin from STATEMENT.md:
--   A(5) = {5}, {4,1} → 2 ;  B(5) = {5}, {1×5} → 2
example : A 5 = 2 := by native_decide
example : B 5 = 2 := by native_decide

-- Definition landmine guard: under the CORRECT pairing, A(2)=B(2)=1.
-- (Swapped pairing fails at n=2 — verified in Level A Python, not restated here.)
example : A 2 = 1 := by native_decide
example : B 2 = 1 := by native_decide

/-! ### Level B ladder: A(n)=B(n) for all n ≤ 24 (sorry-free)

Extends the OPE-26 seed (n ≤ 12). Proof is by cases + `native_decide` on the
computable counters — finite certificate in the kernel, not a general proof.
-/

/-- Finite Schur certificate on the computable counters: `A n = B n` for `n ≤ 24`. -/
theorem schur_computable_le_24 (n : ℕ) (hn : n ≤ 24) : A n = B n := by
  interval_cases n <;> native_decide

/-- Convenience restatement via the `≤ 24` certificate. -/
theorem schur_computable_range (n : ℕ) (hn : n ≤ 24) : A n = B n :=
  schur_computable_le_24 n hn

/-! ## Level B+ — Mathlib `Nat.Partition` Finset statement

These are the contribution-shaped definitions: filtered partitions of `n`,
mirroring Mathlib's `odds` / `distincts` style (see Partition.lean TODO on Euler).
-/

/-- Predicate: every part is ≡ 1 or 2 (mod 3). -/
def partsMod3_12 (p : Partition n) : Prop :=
  ∀ i ∈ p.parts, i % 3 = 1 ∨ i % 3 = 2

/-- Predicate: every part is ≡ 1 or 5 (mod 6). -/
def partsMod6_15 (p : Partition n) : Prop :=
  ∀ i ∈ p.parts, i % 6 = 1 ∨ i % 6 = 5

instance (n : ℕ) : DecidablePred (partsMod3_12 (n := n)) := by
  classical
  intro p
  unfold partsMod3_12
  infer_instance

instance (n : ℕ) : DecidablePred (partsMod6_15 (n := n)) := by
  classical
  intro p
  unfold partsMod6_15
  infer_instance

/-- A-side partitions: **distinct** parts, each ≡ 1 or 2 (mod 3). -/
def schurA (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun p => p.parts.Nodup ∧ partsMod3_12 p

/-- B-side partitions: parts ≡ 1 or 5 (mod 6), **repetitions allowed**. -/
def schurB (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun p => partsMod6_15 p

/-! ### Small-n card equalities on the Mathlib Finset statement

`Fintype (Partition n)` goes through compositions (`2^(n-1)`), so `native_decide`
on Finset filters is feasible only for modest n. We certify n ≤ 12 (same as the
OPE-26 seed bound on Finset form).
-/

theorem schurA_card_eq_schurB_card_le_12 (n : ℕ) (hn : n ≤ 12) :
    (schurA n).card = (schurB n).card := by
  interval_cases n <;> native_decide

/-- Empty-partition convention on the Finset statement. -/
theorem schurA_zero_card : (schurA 0).card = 1 := by native_decide
theorem schurB_zero_card : (schurB 0).card = 1 := by native_decide
theorem schurA_zero_eq_schurB_zero : (schurA 0).card = (schurB 0).card := by native_decide

/-- STATEMENT worked example n=5 on Finset cards. -/
theorem schurA_five_card : (schurA 5).card = 2 := by native_decide
theorem schurB_five_card : (schurB 5).card = 2 := by native_decide

/-- Landmine guard on Finset form: n=2 cards equal 1 under the CORRECT pairing. -/
theorem schurA_two_card : (schurA 2).card = 1 := by native_decide
theorem schurB_two_card : (schurB 2).card = 1 := by native_decide

/-! ### Bridge: computable counters agree with Finset cards (small n)

Links Level B DP definitions to the Mathlib-shaped statement. Proved by
`native_decide` per n ≤ 12 (same Fintype budget).
-/

theorem A_eq_schurA_card_le_12 (n : ℕ) (hn : n ≤ 12) :
    A n = (schurA n).card := by
  interval_cases n <;> native_decide

theorem B_eq_schurB_card_le_12 (n : ℕ) (hn : n ≤ 12) :
    B n = (schurB n).card := by
  interval_cases n <;> native_decide

/-! ### Structural lemmas (sorry-free, all n) -/

/-- The empty partition of 0 is in `schurA 0`. -/
theorem empty_mem_schurA : default ∈ schurA 0 := by native_decide

/-- The empty partition of 0 is in `schurB 0`. -/
theorem empty_mem_schurB : default ∈ schurB 0 := by native_decide

/-- A-side forces distinct parts (Nodup). -/
theorem schurA_nodup {n : ℕ} {p : Partition n} (hp : p ∈ schurA n) :
    p.parts.Nodup := by
  rw [schurA, Finset.mem_filter] at hp
  exact hp.2.1

/-- A-side forces parts ≡ 1 or 2 (mod 3). -/
theorem schurA_mod3 {n : ℕ} {p : Partition n} (hp : p ∈ schurA n) :
    partsMod3_12 p := by
  rw [schurA, Finset.mem_filter] at hp
  exact hp.2.2

/-- B-side forces parts ≡ 1 or 5 (mod 6). -/
theorem schurB_mod6 {n : ℕ} {p : Partition n} (hp : p ∈ schurB n) :
    partsMod6_15 p := by
  rw [schurB, Finset.mem_filter] at hp
  exact hp.2

/-- Allowed A-parts are never ≡ 0 (mod 3). -/
theorem partAllowedA_not_mod0 {p : ℕ} (hp : partAllowedA p = true) :
    p % 3 ≠ 0 := by
  unfold partAllowedA at hp
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  omega

/-- Allowed B-parts are ≡ ±1 (mod 6). -/
theorem partAllowedB_pm1 {p : ℕ} (hp : partAllowedB p = true) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  unfold partAllowedB at hp
  simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using hp

/-- Every B-allowed part is automatically A-allowed (mod-3 shadow).
Useful reduction: the B part set ⊂ {p | p ≡ 1 or 2 (mod 3)}. -/
theorem partAllowedB_implies_partAllowedA {p : ℕ}
    (hp : partAllowedB p = true) : partAllowedA p = true := by
  have h := partAllowedB_pm1 hp
  unfold partAllowedA
  rcases h with h | h
  · -- p ≡ 1 (mod 6) ⇒ p ≡ 1 (mod 3)
    have : p % 3 = 1 := by omega
    simp [this]
  · -- p ≡ 5 (mod 6) ⇒ p ≡ 2 (mod 3)
    have : p % 3 = 2 := by omega
    simp [this]

/-! ## Level C target (NOT proved this run)

The full classical theorem in Mathlib-shaped vocabulary:

  ∀ n, (schurA n).card = (schurB n).card

Proof routes (Andrews / Schur 1926), deferred:
  1. Generating functions:
       ∏_k (1 + x^{3k+1})(1 + x^{3k+2})
         = ∏_k 1/((1 - x^{6k+1})(1 - x^{6k+5}))
     as formal power series over ℤ (or ℕ coefficients).
  2. Bijective / Glaisher-style involution on partitions.
  3. Recurrence + uniqueness of partition generating functions.

We deliberately do **not** plant a `sorry` stub for the full theorem: a sorry
would either fail a zero-sorry gate or over-claim. The named theorem below is
the finite certificate form; the universal statement remains an open Mathlib
gap (re-verified OPE-423 on pinned v4.10.0).
-/

/-- **Schur partition theorem — finite form (Level B+/C ladder step).**
For every `n ≤ 24`, the computable counts agree. Combined with the Finset bridge
for `n ≤ 12`, this pins both vocabularies on a common initial segment. -/
theorem schur_partition_finite (n : ℕ) (hn : n ≤ 24) : A n = B n :=
  schur_computable_le_24 n hn

/-- Finset form on the decide-feasible range. -/
theorem schur_partition_finset_finite (n : ℕ) (hn : n ≤ 12) :
    (schurA n).card = (schurB n).card :=
  schurA_card_eq_schurB_card_le_12 n hn

/-
  Future (true Level C, not this file yet):

  theorem schur_partition (n : ℕ) : (schurA n).card = (schurB n).card := ...

  When that lands zero-sorry, promote STATUS to formalized and hand Reviewer.
-/

end ProofLab.Schur
