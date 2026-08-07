-- Basic module for Open Math Lab proof verification
-- This file contains the shared foundational definitions used across ProofLab.

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace ProofLab.SumFree

/-- A finite set A ⊆ ℕ is sum-free if no element is the sum of two (not
    necessarily distinct) elements of A. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ x y z, x ∈ A → y ∈ A → z ∈ A → x + y ≠ z

end ProofLab.SumFree
