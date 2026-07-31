-- Basic module for Open Math Lab proof verification
-- This file contains trivial examples to verify the Lean setup works

namespace ProofLab

-- Trivial arithmetic theorem to verify Lean is working
example : 1 + 1 = 2 := rfl

-- Another simple example using natural number addition
example : Nat.succ 0 = 1 := rfl

-- Simple propositional logic example
example (p q : Prop) : p → (q → p) := fun hp _ => hp

end ProofLab
