# Adversarial Review Checklist

**Purpose**: Prevent false "solved" claims through systematic skeptical review.

**Role**: Adversarial Reviewer breaks overconfident claims. Rubber stamps are forbidden.

---

## Review Protocol

### 1. BLOCKING ISSUES

Any item below **must** be resolved before status can advance to `claim-ready`.

#### A. Statement Integrity

- [ ] **Informal statement matches Lean theorem name(s)** exactly
  - Check: What problem was stated in the issue?
  - Check: What theorem(s) are claimed in the proof artifact?
  - Red flag: Names drift ("I proved a stronger result")
  
- [ ] **All hypotheses are explicit**
  - Check: Hidden assumptions in informal motivation
  - Check: Strengthened preconditions not in original statement
  - Red flag: "Obviously we can assume..." without justification

- [ ] **Edge cases enumerated**
  - Check: Boundary conditions tested or proven unreachable
  - Check: Zero, infinity, empty sets, degenerate cases
  - Red flag: "Works for the general case"

#### B. Lean Verification (if Lean artifact exists)

- [ ] **No hidden `sorry` / `admit` / `axiom`**
  ```bash
  # Run these checks:
  grep -r "sorry" proofs/
  grep -r "admit" proofs/
  lake build 2>&1 | grep -i "axiom"
  ```
  
- [ ] **Clean build log**
  - `lake build` exits 0
  - No warnings suppressed
  - No timeouts or incomplete elaboration
  
- [ ] **Theorem statement in Lean matches informal claim**
  - Check: Type signatures, universes, implicit arguments
  - Red flag: Lean proves weaker result with same name

#### C. Proof Hygiene

- [ ] **Computational evidence is not smuggled as proof**
  - Check: "Verified for n ≤ 10000" ≠ proven for all n
  - Check: Probabilistic checks labeled as heuristic, not proof
  - Red flag: "The pattern holds" without induction/limit argument

- [ ] **Gaps documented or filled**
  - Check: "Left to reader" items < 3 and each < 1 hour senior mathematician effort
  - Check: Non-trivial lemmas have citations or proofs
  - Red flag: "Straightforward generalization of [X]" without showing work

- [ ] **No circular reasoning**
  - Check: Lemma dependency graph is acyclic
  - Check: Informal motivation doesn't assume conclusion
  - Red flag: "Since the claim is true, we can deduce..."

#### D. Crackpottery Filters

🚨 **Immediate veto** if any apply:

- [ ] Mystical numerology (Gematria, "divine ratios," unexplained constants)
- [ ] Unbounded claims ("AI will solve this overnight," "Just add more tokens")
- [ ] Rejection of standard definitions without formal alternatives
- [ ] Appeals to authority over argument ("Einstein would agree")
- [ ] Conspiracy theories about mathematical establishment

---

### 2. RESIDUAL RISKS

Even if all blocking issues pass, document **non-blocking** concerns for board review.

- **Novelty uncertain**: Literature search incomplete; possible priority conflict
- **Informal motivation mismatch**: Lean statement correct but solves different problem than intended
- **Complexity explosion**: Proof technically valid but unmaintainable/unextendable
- **Axiom budget**: Uses classical choice/LEM where constructive proof was goal
- **Computational assumptions**: Proof correct but relies on unverified numerics
- **Scope creep**: Solved variant of problem, not original formulation

**Requirement**: Residual risks list must be **non-empty and honest**. If empty, explain why this is a perfect result (rare).

---

### 3. APPROVAL / VETO PROTOCOL

#### Approve (`claim-ready`)

- All blocking issues resolved ✅
- Residual risks documented and acceptable for board escalation
- Claim packet prepared via `mathforge claim prepare`

**Default recommendation: NO CLAIM**. Burden of proof is on the attack, not the reviewer.

#### Veto (force back to `in_progress` or `blocked`)

- Any blocking issue unresolved
- Dishonest residual risk list
- Crackpottery detected

**Veto authority**: Adversarial Reviewer may unilaterally downgrade status. Appeal to board (Paul) only.

#### Conditional (request fixes)

- Post detailed review comment
- Tag specific lines/files needing correction
- Set deadline or iteration budget
- If fixes not attempted within 2 heartbeats, veto

---

## Example Review

### Claim: "Proved Collatz holds for all n < 2^68"

**Blocking issues**:
- ❌ Computational verification is not a proof (filter C)
- ❌ Original problem is for **all** n, not bounded n (statement drift)

**Verdict**: VETO. Relabel as `status: heuristic` or reframe as "computational evidence."

---

### Claim: "Formalized and proved: perfect numbers and Mersenne primes"

**Blocking issues**:
- ✅ Lean builds clean
- ✅ Theorem matches classical statement
- ⚠️  Check: does Mathlib already contain this? (novelty risk)

**Residual risks**:
- Novelty uncertain; needs arXiv/Mathlib priority check
- Uses classical `decidable` instances; constructive version open

**Verdict**: Approve for `claim-ready` with residual risk disclosure to board.

---

## Reviewer Responsibilities

1. **Read the full artifact** (proof file, issue thread, attack logs)
2. **Run verification** (Lean build, grep checks, literature spot-check)
3. **Document findings** in issue comment with this checklist
4. **Issue verdict** with explicit approval or veto
5. **Update issue status** to match verdict

**Do NOT**:
- Rubber stamp because "looks plausible"
- Skip Lean build because "probably fine"
- Approve with empty residual risks
- Veto without specific blocking issue cited

---

**Last updated**: 2026-07-29  
**Owner**: Adversarial Reviewer role  
**Scope**: All mathforge proof claims before board escalation
