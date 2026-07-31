# Claim Policy

**Purpose**: Govern how Open Math Lab communicates mathematical results to the board and externally.

**Authority**: Board (Paul) is the **only** authority for external communication. No agent, researcher, or contributor may claim results publicly without explicit board approval.

---

## Default Position

**Default recommendation: NO CLAIM.**

The burden of proof is on the work artifact to demonstrate:
1. Mathematical correctness (via Lean proof or Adversarial Reviewer approval + explicit residual risks)
2. Novelty (literature search, priority check)
3. Significance (solves stated problem, not trivial variant)
4. Communication readiness (claim packet complete, risks disclosed)

---

## Claim Packet Preparation

All claim-ready work must go through `mathforge claim prepare`, which produces:

- **Statement**: Informal and formal (Lean) versions, with all hypotheses explicit
- **Proof artifact**: Lean file(s) with clean `lake build`, or informal proof with Reviewer approval
- **Verification report**: 
  - Lean build log (if applicable)
  - Adversarial review checklist completion
  - Grep checks for `sorry`/`admit`/`axiom`
- **Residual risks**: Non-empty, honest list of:
  - Novelty uncertainty
  - Computational assumptions
  - Axiom use (classical vs constructive)
  - Scope differences from original problem
  - Informal motivation mismatch
  - Literature priority conflicts
- **Attack log**: Summary of failed approaches, dead ends, feasibility evolution
- **Recommendation**: Explicit claim/no-claim with justification

**Requirement**: Residual risks must be **non-empty and honest**. If the list is empty, the claim packet must explain why this is a perfect, risk-free result (extremely rare).

---

## Veto Protocol

### Who Can Veto

**Adversarial Reviewer** has **unilateral veto authority** to:
- Block status advancement to `claim-ready`
- Force status back from `claim-ready` to `in_progress` or `blocked`
- Refuse to approve claim packets

**Board (Paul)** retains ultimate veto at every stage.

### Veto Grounds

#### Automatic / Immediate Veto

Any of the following triggers **immediate veto** without debate:

1. **Crackpottery detected**:
   - Mystical numerology, "divine ratios," unexplained constants
   - Unbounded AI/compute claims ("will solve overnight")
   - Rejection of standard definitions without formal alternatives
   - Appeals to authority over argument
   - Conspiracy theories about mathematical establishment

2. **Epistemic dishonesty**:
   - Hidden `sorry` / `admit` / axioms not disclosed
   - Computational verification labeled as proof
   - Residual risks list empty or obviously incomplete
   - Statement drift (claim different from what was proven)

3. **Technical blocking issues** (see REVIEW_CHECKLIST.md):
   - Lean build fails
   - Informal statement doesn't match Lean theorem
   - Hidden assumptions or missing edge cases
   - Circular reasoning in proof

#### Conditional Veto (Request Fixes)

Reviewer may issue **conditional veto** with specific fix requests:

- Post detailed review comment on issue
- Tag specific lines/files/gaps needing correction
- Set iteration budget or deadline (typically 1-2 heartbeats)
- If fixes not attempted or progress stalled, upgrade to full veto

**Timeline**: If no fix attempt within 2 heartbeats after conditional veto, status downgrades to `blocked` or `in_progress`.

### Veto Process

1. **Document findings**: Post issue comment with:
   - REVIEW_CHECKLIST.md items marked
   - Specific blocking issues cited
   - Verdict: VETO or CONDITIONAL
   - Required fixes (if conditional)

2. **Update status**:
   - From `claim-ready` → `in_progress` (fixable issues)
   - From `claim-ready` → `blocked` (needs external dependency or board decision)
   - Prevent advancement if currently `in_progress`

3. **Notify stakeholders**:
   - Comment tags Attack Lead or responsible agent
   - Board receives notification for all vetoes (automatic via Paperclip)

### Appeal Process

**Appeals go to board (Paul) only.**

- Adversarial Reviewer veto is presumed correct
- Attack Lead or researcher may appeal by:
  - Posting structured rebuttal on issue
  - Requesting board review via issue comment
  - Providing additional evidence (new Lean proofs, literature citations, corrected gaps)
- Board decides: uphold veto, override, or request third-party review

**No automatic override**. The veto stands until board explicitly reverses it.

---

## Claim Approval Path

### Status Progression

```
in_progress → (Adversarial Review) → claim-ready → (Board Review) → approved → external communication
```

**Gates**:
1. **Adversarial Review** (docs/REVIEW_CHECKLIST.md): All blocking issues resolved, residual risks documented
2. **Claim Packet**: `mathforge claim prepare` completes successfully
3. **Board Approval**: Paul reviews packet + residual risks, decides external communication

### Approval Criteria

**Adversarial Reviewer** approves to `claim-ready` only if:
- ✅ All blocking issues resolved (REVIEW_CHECKLIST.md sections 1A-1D)
- ✅ Residual risks documented honestly and non-empty (section 2)
- ✅ Claim packet prepared and complete
- ✅ No crackpottery, no epistemic dishonesty
- ✅ Default recommendation is **still** no claim unless mathematical significance + novelty are clear

**Board** approves external communication only if:
- ✅ Adversarial Reviewer approved
- ✅ Residual risks acceptable (Board's risk tolerance)
- ✅ Communication timing and venue appropriate
- ✅ Priority / novelty verified (arXiv search, Mathlib check, literature review)
- ✅ Reputational risk acceptable

---

## External Communication Rules

**Forbidden without board approval**:
- Posting to arXiv, viXra, or preprint servers
- Emailing mathematical societies or researchers claiming results
- Tweeting, blogging, or social media posts about "solved" problems
- Opening pull requests to external repos (e.g., Mathlib) with result claims
- Submitting to journals or conferences

**Allowed**:
- Internal issue comments, logs, work artifacts
- Draft claim packets for board review
- Literature searches and problem catalogs (descriptive, not claiming)
- Collaboration with board-approved external reviewers (after disclosure agreement)

**Penalty for violation**: Immediate removal from Open Math Lab project access.

---

## Residual Risk Categories

### Technical Risks

- **Axiom use**: Classical choice, Law of Excluded Middle, Propositional Extensionality
  - Impact: May not align with constructive mathematics goals
  - Mitigation: Document; consider constructive variant as follow-up

- **Computational assumptions**: Unverified numerics, probabilistic checks, bounded search
  - Impact: Proof depends on external computation correctness
  - Mitigation: Formalize computation in Lean or label as heuristic

- **Complexity explosion**: Proof technically valid but unmaintainable
  - Impact: Hard to extend, verify, or explain
  - Mitigation: Refactor for clarity; document decision tradeoffs

### Scope Risks

- **Statement drift**: Proved variant of problem, not original formulation
  - Impact: Claim may overstate what was actually shown
  - Mitigation: Clarify "we proved X, not Y"; explain relationship

- **Informal motivation mismatch**: Lean statement correct but solves different problem
  - Impact: Misleading to non-formalist audience
  - Mitigation: Write careful natural-language summary with limitations

- **Scope creep**: Generalized or restricted problem without justification
  - Impact: May not address original research question
  - Mitigation: Document why scope changed; propose follow-up for original

### Novelty Risks

- **Literature incomplete**: Didn't find prior work, but may exist
  - Impact: Claim priority incorrectly; duplicate effort
  - Mitigation: Deeper search (arXiv, MathSciNet, Zentralblatt, Mathlib); disclose uncertainty

- **Mathlib overlap**: Theorem may already exist in Mathlib under different name
  - Impact: Wasted effort; false novelty claim
  - Mitigation: Grep Mathlib; ask Lean Zulip; cite if found

- **Trivial corollary**: Result follows easily from known theorem
  - Impact: Overstates contribution
  - Mitigation: Cite parent result; frame as formalization exercise, not novel math

---

## Examples

### Example 1: Clean Approval

**Claim**: "Formalized Bertrand's Postulate in Lean 4 (not in Mathlib)"

**Review findings**:
- ✅ Lean builds clean, no `sorry`
- ✅ Statement matches classical Bertrand's Postulate
- ✅ Mathlib search: not present (as of 2026-07-29)
- ✅ Uses standard Mathlib tactics, no exotic axioms

**Residual risks**:
- Novelty: Mathlib may add this before we publish (monitor `mathlib4` repo)
- Scope: Proved for `n ≥ 25`; classical version is `n ≥ 1` (documented in proof comments)

**Verdict**: Approve `claim-ready`. Board may approve external communication with risk disclosure.

---

### Example 2: Conditional Veto

**Claim**: "Proved Goldbach Conjecture for even n < 10^8"

**Review findings**:
- ❌ Computational verification, not proof
- ❌ Original problem is for **all** even n > 2
- ⚠️  Lean code exists but only formalizes "verified via computation"

**Conditional veto**:
- Relabel as `status: heuristic` OR
- Reframe claim as "Computational evidence for Goldbach up to 10^8" OR
- Prove the computation itself is correct (formalize verification algorithm in Lean)

**Deadline**: 1 heartbeat to choose path and update claim.

**Outcome**: If no fix attempt → full veto, status → `in_progress`.

---

### Example 3: Immediate Veto (Crackpottery)

**Claim**: "Proved Riemann Hypothesis using sacred geometry and Fibonacci spirals"

**Review findings**:
- 🚨 Mystical numerology (sacred geometry)
- 🚨 No formal definitions, no Lean code
- 🚨 "Proof" is philosophical essay with unexplained constants

**Verdict**: **IMMEDIATE VETO**. Status → `blocked` pending board review of whether to continue this research direction at all.

**Board escalation**: Recommend closing issue and blacklisting this approach.

---

## Reviewer Accountability

**Adversarial Reviewer role** is a **trust position**:

- Rubber-stamping is a firing offense (figuratively)
- Must read full artifacts, run Lean builds, document findings
- Must maintain **honest residual risk lists**
- May not approve empty or obviously incomplete reviews

**Board oversight**:
- Random audits of approved claim packets
- Veto override tracking (frequent overrides → reviewer recalibration)
- Community feedback (if results published and later found flawed)

**Consequences for bad reviews**:
- Reputational harm to Open Math Lab
- Wasted board / external reviewer time
- Potential retraction costs

**Protection for good-faith vetoes**:
- Reviewer is **never** penalized for vetoing weak claims
- False negatives (vetoing valid work) are recoverable via appeal
- False positives (approving invalid work) are costly and hard to fix

**Default bias**: When in doubt, veto. The board can override; the mathematical community cannot un-see a retracted claim.

---

## Tooling Integration

### `mathforge claim prepare`

Command-line tool (to be implemented) that:

1. Collects proof artifacts from `proofs/` directory
2. Runs Lean build and captures log
3. Executes grep checks for `sorry`, `admit`, axioms
4. Loads REVIEW_CHECKLIST.md and prompts Reviewer for each item
5. Generates claim packet markdown with all sections
6. Saves to `claims/YYYY-MM-DD-{problem-slug}.md`
7. Outputs board-ready summary

**Usage**:
```bash
mathforge claim prepare --issue OPE-42 --proof proofs/bertrand/bertrand.lean
```

**Output** (example):
```
Claim packet generated: claims/2026-07-29-bertrand-postulate.md

Summary:
  Status: claim-ready
  Residual risks: 2 (novelty uncertainty, scope restriction)
  Recommendation: Approve for board review
  Next step: Tag @board for external communication decision
```

### Status Labels

Issues use these labels for claim workflow:

- `status: informal` — proof sketch, not verified
- `status: heuristic` — computational evidence, not proof
- `in_progress` — active work, not ready for review
- `in_review` — under Adversarial Review
- `claim-ready` — passed review, awaiting board decision
- `approved` — board approved external communication
- `blocked` — veto or external dependency

---

## Document History

- **2026-07-29**: Initial version (OPE-10)
- **Owner**: Adversarial Reviewer role, Board (Paul)
- **Scope**: All mathforge proof claims

---

## Related Documents

- [REVIEW_CHECKLIST.md](./REVIEW_CHECKLIST.md) — Detailed review dimensions and blocking criteria
- [AGENTS.md](../../companies/.../AGENTS.md) — Role definitions and mission constraints
- [mathforge CLI docs](../skills/README.md) — Tooling for claim preparation (to be created)

---

**Key Principle**: Epistemic honesty over speed. A late correct claim is better than a fast false one.
