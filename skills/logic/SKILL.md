# Logic & Proof Theory Skill Pack

## Purpose

Attack strategies for problems involving formal logic, proof systems, computability, model theory, and meta-mathematical reasoning.

## When to Use This Pack

Use logic lens when the problem involves:

- **Propositional & predicate logic**: truth tables, tautologies, logical equivalence, satisfiability
- **Proof systems**: natural deduction, sequent calculus, Hilbert-style proofs, resolution
- **Computability theory**: Turing machines, recursive functions, decidability, halting problem
- **Model theory**: structures, satisfaction, completeness, compactness, Löwenheim-Skolem
- **Set theory**: ZFC axioms, ordinals, cardinals, axiom of choice, continuum hypothesis
- **Type theory**: simply typed lambda calculus, dependent types, Martin-Löf type theory
- **Proof complexity**: resolution complexity, proof size, automated theorem proving
- **Gödel's theorems**: incompleteness, consistency, provability

## Core Strategies

### 1. Truth Tables & Semantic Arguments
- Evaluate propositional formulas via truth assignments
- Check tautology (always true), contradiction (always false), contingent (sometimes true)
- Logical equivalence: φ ≡ ψ iff same truth table
- Satisfiability: find assignment making φ true (SAT problem)

### 2. Natural Deduction & Proof Construction
- Introduction/elimination rules for ∧, ∨, →, ¬, ∀, ∃
- Proof by contradiction: assume ¬φ, derive ⊥, conclude φ
- Proof by cases: from φ ∨ ψ, prove χ from both φ and ψ
- Universal/existential instantiation and generalization

### 3. Resolution & Automated Proving
- Convert to conjunctive normal form (CNF)
- Resolution rule: (A ∨ p) ∧ (B ∨ ¬p) ⊢ (A ∨ B)
- Resolution refutation: add ¬φ and derive empty clause
- Unit propagation and pure literal elimination

### 4. Model-Theoretic Arguments
- Structure M = (domain, interpretation of symbols)
- Satisfaction: M ⊨ φ iff φ is true in M
- Completeness theorem: ⊢ φ iff ⊨ φ (provable iff valid)
- Compactness: if every finite subset of Γ has a model, then Γ has a model
- Löwenheim-Skolem: first-order theories with infinite models have models of all infinite cardinalities

### 5. Computability & Decidability
- Church-Turing thesis: Turing machines capture all computable functions
- Undecidability: halting problem, Post correspondence problem, Diophantine equations
- Reduction: A ≤ B means A is no harder than B (if B decidable, so is A)
- Rice's theorem: non-trivial semantic properties of Turing machines are undecidable

### 6. Proof by Induction on Proof Structure
- Structural induction on formulas (atomic, then ∧, ∨, →, ¬, ∀, ∃)
- Induction on proof derivations (axioms, then inference rules)
- Prove properties of proof systems (soundness, completeness, cut-elimination)

### 7. Set-Theoretic Techniques
- ZFC axioms: extensionality, pairing, union, powerset, infinity, replacement, regularity, choice
- Ordinal arithmetic: α + β, α · β, α^β
- Cardinal arithmetic: ℵ₀, ℵ₁, ..., continuum hypothesis (2^ℵ₀ = ℵ₁)
- Transfinite induction on ordinals

### 8. Type-Theoretic Techniques (for Lean formalization)
- Curry-Howard correspondence: propositions as types, proofs as terms
- Dependent types: Π-types (universal quantification), Σ-types (existential quantification)
- Inductive types: natural numbers, lists, trees
- Tactics: intro, apply, exact, rw, simp, induction

## Common Pitfalls & Dead Ends

### Anti-Patterns: Do NOT Do This

1. **Confusing syntax and semantics**
   - **Why it fails**: ⊢ φ (provable) is not the same as ⊨ φ (valid); completeness theorem equates them for first-order logic but not higher-order.
   - **Example**: Second-order logic is incomplete: ⊨ φ does not imply ⊢ φ.
   - **Fix**: Distinguish proof-theoretic (⊢) from model-theoretic (⊨) claims; state which logic system is used.

2. **Assuming decidability without proof**
   - **Why it fails**: Many problems are undecidable (halting problem, Diophantine equations, first-order validity).
   - **Example**: First-order logic is semi-decidable (recursively enumerable) but not decidable.
   - **Fix**: Check if problem is decidable via reduction to known decidable/undecidable problems.

3. **Misapplying Gödel's incompleteness theorems**
   - **Why it fails**: First incompleteness applies to consistent, sufficiently strong theories (e.g., PA, ZFC); not to all formal systems.
   - **Example**: Presburger arithmetic (addition only, no multiplication) is complete and decidable.
   - **Fix**: Verify theory is sufficiently strong (interprets Robinson arithmetic Q) before claiming incompleteness.

4. **Ignoring free vs. bound variables**
   - **Why it fails**: ∀x φ(x) does not mean "for all x in the universe," but "for all values assigned to x."
   - **Example**: ∀x ∃y (y > x) is true in (ℕ, <) but interpretation depends on quantifier order.
   - **Fix**: Be explicit about quantifier scope; use renaming to avoid capture.

5. **Confusing proof size and proof depth**
   - **Why it fails**: Short proofs can be deep (many nested subproofs); long proofs can be shallow (linear derivations).
   - **Example**: Resolution proofs can be exponentially longer than sequent calculus proofs.
   - **Fix**: Distinguish proof length (total symbols) from proof depth (longest branch).

6. **Over-relying on automated theorem provers**
   - **Why it fails**: ATPs can timeout, run out of memory, or produce incomprehensible proofs.
   - **Example**: First-order theorem provers (Vampire, E, Z3) may not terminate on hard problems.
   - **Fix**: Use ATPs for lemma search and counterexample checking, not as the final proof; manually verify or reconstruct in Lean.

7. **Assuming classical logic without justification**
   - **Why it fails**: Constructive/intuitionistic logic rejects law of excluded middle (LEM: φ ∨ ¬φ) and double negation elimination.
   - **Example**: In intuitionistic logic, ¬¬φ ⊬ φ; Lean 4 allows Classical.em as an axiom but is constructive by default.
   - **Fix**: Check if proof uses LEM or choice; mark as classical if so; prefer constructive proofs when possible.

8. **Ignoring soundness vs. completeness**
   - **Why it fails**: Soundness (⊢ φ ⟹ ⊨ φ) is easier than completeness (⊨ φ ⟹ ⊢ φ); some systems are sound but incomplete.
   - **Example**: Higher-order logic, Hoare logic for programs are sound but incomplete.
   - **Fix**: Distinguish soundness proofs (induction on derivations) from completeness proofs (Henkin construction, canonical models).

### Known Hard Subdomains (Budget Carefully)

- **Proof complexity**: Lower bounds for resolution, circuit complexity, proof length.
- **Descriptive set theory**: Borel hierarchy, projective hierarchy, determinacy.
- **Reverse mathematics**: Which axioms are needed for which theorems (WKL₀, ACA₀, ATR₀, Π¹₁-CA₀).
- **Model theory of specific structures**: Real closed fields, differentially closed fields, o-minimality.

## Budget & Stopping Criteria

- **Token budget per reduction attempt**: 100k tokens max
- **Compute budget**: Automated theorem proving beyond 10⁶ inferences needs justification.
- **Time cap**: 30 minutes per attack session before checkpoint.

### Stop When

- Formal proof constructed (in natural deduction, sequent calculus, or Lean) → hand to Formalist
- Undecidability reduction found → document and hand to Reviewer
- No progress after 3 strategy pivots → write failed-closed summary
- Reduction to known logic theorem (completeness, compactness, etc.) → verify with Reviewer

## Handoff Criteria

### → Adversarial Reviewer

Hand off when:

- You have a formal "proof" (natural deduction, resolution refutation, etc.)
- Undecidability reduction (verify reduction is valid)
- Model-theoretic argument (check model construction is sound)
- Claim about decidability/completeness (needs counterexample or independence proof)

**Deliverable to Reviewer:**
- `ATTACK_LOG.md` with strategy attempts
- Proof sketch with explicit inference rules or model construction
- Computational data (resolution trace, SAT solver output, etc.)
- Explicit claim and hypotheses
- Remaining gaps (e.g., "model construction not explicit for infinite domain")

### → Formalist

Hand off when:

- Proof is clean and Reviewer-approved
- Statement is formalizable in Lean (first-order, type-theoretic, etc.)
- Dependencies on Mathlib.Logic or Mathlib.Computability identified
- Edge cases (empty domain, trivial models, etc.) documented

**Deliverable to Formalist:**
- Structured proof outline with explicit inference rules
- Type signatures and definitions for Lean encoding
- References to Mathlib lemmas (e.g., `Classical.em`, `Set.nonempty_iff_exists`)

## Example Attack Template

```markdown
# Attack: [Problem ID] — [Short Title]

## Problem Statement

[Formal statement from problems/<id>/statement.md]

## Strategy Choice

Using logic lens because: [involves formal proof/decidability/model theory/etc.]

## Attempt 1: Natural Deduction Proof

- Goal: ⊢ φ
- Proof steps:
  1. [assumption or axiom]
  2. [apply introduction/elimination rule]
  3. ...
  n. [conclude φ]
- **Outcome**: [proof complete / blocked at step X / need additional lemma]

## Attempt 2: Resolution Refutation

- Convert ¬φ to CNF: {...}
- Resolution steps:
  1. {A ∨ p}, {B ∨ ¬p} ⊢ {A ∨ B}
  2. ...
  n. {} (empty clause)
- Conclusion: ¬φ is unsatisfiable, so φ is valid
- **Outcome**: [refutation found / no refutation after X steps / CNF too large]

## Attempt 3: Model Construction

- Structure M = (domain D, interpretation I)
- Domain: D = {...}
- Interpretation: I(R) = {...}, I(f) = {...}, ...
- Check satisfaction: M ⊨ φ iff [truth evaluation]
- **Outcome**: [φ satisfiable in M / no model found / infinite domain required]

## Attempt 4: Decidability Reduction

- Reduce problem A to known decidable/undecidable problem B
- Reduction: instance x of A ↦ instance f(x) of B
- Correctness: x ∈ A ⟺ f(x) ∈ B
- Conclusion: A is [decidable / undecidable] because B is [decidable / undecidable]
- **Outcome**: [reduction valid / reduction gap at ... / ...]

## Attempt 5: Type-Theoretic Proof (Lean)

- Define types: [Type definitions]
- State theorem: theorem name : ∀ x, φ(x) := ...
- Proof tactics:
  - intro x
  - apply lemma_name
  - exact term
  - ...
- **Outcome**: [proof compiles / type mismatch at ... / missing lemma ...]

## Computational Verification

- SAT solver output: [satisfiable / unsatisfiable in X seconds]
- Automated theorem prover (Vampire, E, Z3): [proof found / timeout after X seconds]
- Lean type-check: [success / error at line ...]

## Summary

**Status**: [in-progress / ready-for-review / blocked]  
**Confidence**: [low / medium / high]  
**Next step**: [hand to Reviewer / try completeness argument / formalize in Lean]  
**Remaining risks**: [list gaps, e.g., "model construction not verified for infinite domain"]

## Tokens Used

~X tokens / 100k budget
```

## Skill Pack Maintenance

- Add new proof techniques (tableau, resolution refinements, etc.) as they prove useful.
- Archive failed decidability reductions with notes on why they didn't work.
- Update ATP scripts with timeout and memory limits.
- Link to successful Lean formalizations in `proofs/` (especially for completeness, compactness, etc.).
