# Lean 4 Formal Verification Plan

**Status**: Toolchain INSTALLED ✓ — Basic build passing  
**Owner**: Formalist  
**Last updated**: 2026-07-31  
**Installation**: See `docs/LEAN_INSTALL_LOG.md` for full details

---

## Executive Summary

This document outlines the strategy for integrating Lean 4 formal verification into the Open Math Lab's mathforge product. The goal is to provide **machine-checkable proof gates** for mathematical claims, moving from fluent-but-informal English "proofs" to verified theorems.

**Key principle**: Until a Lean build checks a theorem (exit code 0, no `sorry` in critical path), the claim remains `status: informal` or `status: heuristic`.

---

## Why Lean 4?

1. **Machine verification**: Human-readable text is not proof; type-checked Lean code is.
2. **Mathlib ecosystem**: Large library of formalized undergraduate/graduate mathematics.
3. **Active community**: Lean Zulip chat, growing research adoption, tooling momentum.
4. **Epistemic honesty**: Forces explicit assumptions, catches hidden gaps, blocks rubber-stamp "solved" claims.

**Alternatives considered**:
- Coq: Mature but steeper learning curve for classical mathematics
- Isabelle/HOL: Strong automation, less active pure-math community
- Metamath: Ultra-simple kernel, minimal library, less ergonomic

**Decision**: Lean 4 (v4.10.0 pinned) + Mathlib 4.

---

## Repository Layout

### Current Structure

```
open-math-lab/
├── docs/
│   ├── LEAN_PLAN.md              # This file
│   └── REVIEW_CHECKLIST.md       # Adversarial review guide
├── proofs/
│   └── lean-project/             # Lean 4 workspace (scaffold exists)
│       ├── lean-toolchain        # Version pin: v4.10.0
│       ├── lakefile.lean         # Build config + Mathlib dep
│       ├── ProofLab.lean         # Top-level module
│       ├── Main.lean             # Optional executable
│       ├── ProofLab/
│       │   └── Basic.lean        # Stub (trivial examples)
│       ├── .gitignore            # Build artifacts
│       └── README.md             # Installation + build instructions
└── skills/
    └── (attack strategies, verification helpers)
```

### Future: Per-Problem Organization

When formalizing a specific problem (e.g., `proofs/goldbach-weak/`):

```
proofs/goldbach-weak/
├── STATEMENT.md                  # Informal problem statement
├── FEASIBILITY.md                # Scout's assessment
├── STRATEGY.md                   # Attack lead's plan
├── attempts/
│   ├── 01-analytic-reduction/
│   │   ├── NOTES.md
│   │   └── dead-end-reason.txt
│   └── 02-sieve-bound/
│       ├── NOTES.md
│       └── partial-progress.txt
├── lean/
│   └── GoldbachWeak.lean         # Formal statement in Lean
├── BUILD_LOG.txt                 # `lake build` output (if formalized)
└── STATUS.md                     # Current claim status
```

**Lean code location**:
- **Shared library code**: `proofs/lean-project/ProofLab/<Domain>.lean` (e.g., `NumberTheory.lean`, `Combinatorics.lean`)
- **Problem-specific formalization**: Either inline in shared library (if reusable) or as standalone files symlinked/imported into the Lean project

**Rationale**: Problem-specific directories keep attempt logs, notes, and informal work co-located with the statement; Lean code lives in the unified build tree for dependency sharing.

---

## Lean Toolchain Installation

**STATUS**: ✅ INSTALLED (2026-07-31, OPE-17)

### Installed Versions
- **elan** 4.2.3 (b6cec7e10 2026-06-08)
- **lean** 4.10.0 (matches `lean-toolchain` pin)
- **lake** 5.0.0-c375e19

### Installation Location
- elan home: `C:\Users\paulb\.elan`
- Binaries: `C:\Users\paulb\.elan\bin` (added to user PATH)
- Toolchain: User-local (not system-wide) ✓

### How to Rebuild on This Machine

**From PowerShell**:
```powershell
# Ensure elan is on PATH
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"

# Navigate to Lean project
cd proofs\lean-project

# Build
lake build

# Exit code 0 = success
```

**From Bash (if available)**:
```bash
export PATH="$HOME/.elan/bin:$PATH"
cd proofs/lean-project
lake build
```

### First Build Results
- **Exit code**: 0 (SUCCESS)
- **Duration**: ~3 minutes (Mathlib cache download + build)
- **Build log**: `proofs/lean-project/BUILD_LOG.txt`
- **Modules built**: ProofLab.Basic, Main executable
- **Mathlib**: 4878 .olean files fetched from cache (100% success)

### Known Limitations (as of 2026-07-31)
- `ProofLab/ErdosWoods.lean` and `ProofLab/SumFree.lean` have import path mismatches with Mathlib v4.10.0
- These files are commented out in `ProofLab.lean` pending import fixes
- `ProofLab/Basic.lean` builds successfully with no `sorry` — installation verified ✓

### Installation Non-Compliance Check
- [x] NOT installed system-wide (user-local only)
- [x] NOT committed `lake-packages/`, `build/`, `.lake/` to git
- [x] Installation succeeded (no blockers)
- [x] Full installation log at `docs/LEAN_INSTALL_LOG.md`

---

## Formalization Workflow

### 1. Problem Selection & Informal Statement

**Owner**: Problem Scout (curates), Research Director (approves)

- Scout writes `STATEMENT.md` in plain English + LaTeX
- Feasibility score: likelihood of formal statement, proof sketch, literature hints
- Example: "Prove there are infinitely many primes p ≡ 1 (mod 4)" → HIGH feasibility (Mathlib has quadratic reciprocity, Dirichlet's theorem machinery)

### 2. Lean Statement Formalization

**Owner**: Formalist (this agent)

**Input**: Approved `STATEMENT.md`  
**Output**: Lean code that **states** the theorem (not necessarily proves it)

**Steps**:
1. Search Mathlib for existing definitions (primes, congruences, infinitude)
2. Import relevant modules (e.g., `Mathlib.NumberTheory.Primes.Basic`)
3. Write `theorem <name> : <Lean-type-expressing-statement> := sorry`
4. Verify it type-checks: `lake build` with `sorry` is OK at this stage
5. Document in problem's `lean/` directory + link in `ProofLab.lean`
6. Commit with message: `"Formalize statement: <problem-id>"`

**Handoff**: Statement is now a compile-time contract. Attack Lead works modulo this API.

### 3. Proof Attempt

**Owner**: Attack Lead (writes proof), Formalist (checks syntax/builds)

**Input**: Formalized statement with `sorry`  
**Output**: Proof attempt (may still have `sorry` gaps) + build log

**Tactics**:
- `rfl` (reflexivity), `simp` (simplification), `ring` (polynomial ring solver)
- `linarith` (linear arithmetic), `omega` (Presburger arithmetic)
- `exact <term>`, `apply <lemma>`, `rw [<equation>]` (rewriting)
- Mathlib search: `#check`, `exact?`, `apply?`, `rw?`

**Iterations**:
- Attack Lead edits `.lean` file, Formalist runs `lake build`
- Build errors → fix syntax, missing imports, type mismatches
- `sorry` gaps → document as "partial progress" in attempt notes
- Budget exhausted → freeze attempt, write dead-end log

**Critical**: Do NOT claim success if `sorry` remains in the proof term.

### 4. Adversarial Review

**Owner**: Adversarial Reviewer

**Trigger**: Attack Lead claims "proof complete"

**Checks**:
1. `grep -r sorry proofs/lean-project/` → FAIL if hits in claimed theorem
2. `lake build` exit code 0 → FAIL if non-zero
3. Review proof for accidental axiom use (`Classical.choice` OK if justified, `Classical.axiomOfChoice` needs justification)
4. Check statement matches informal `STATEMENT.md` (no hidden assumptions)
5. Test edge cases: empty set, n=0, degenerate geometry, etc.

**Outcomes**:
- **PASS**: Mark `status: formal`, archive build log, update issue to `done`
- **FAIL**: Document gaps, block issue, assign back to Attack Lead or Formalist
- **PARTIAL**: Accept as `status: informal-with-verified-lemmas` if useful lemmas proven

### 5. Claim Preparation (if board requests)

**Owner**: Research Director (compiles packet), Board (decides)

**Input**: `status: formal` + build log + adversarial review PASS  
**Output**: Claim packet for board review (NOT auto-posted externally)

Default recommendation: **No external claim** unless explicitly directed by board.

---

## Build & CI Conventions

### Local Development

**Before commit**:
```bash
cd proofs/lean-project/
lake build                # Must exit 0
grep -r sorry ProofLab/   # Must be empty for formal claims
```

**After Lean edits**:
- Commit `.lean` files, `lakefile.lean`, `lean-toolchain`
- Do NOT commit `build/`, `.lake/`, `lake-packages/`
- Include `BUILD_LOG.txt` snippet in problem directory if claiming formal proof

### CI (Future Work)

**Blocked until**:
- Lean installation stable on developer machine
- Decision on GitHub Actions vs. local-only verification

**Proposed CI**:
1. GitHub Actions workflow: `lean-check.yml`
2. Runs on: push to `main`, PRs touching `proofs/lean-project/`
3. Steps:
   - Install elan/lake via cached action
   - `lake build` in `proofs/lean-project/`
   - Fail if exit code ≠ 0 or `sorry` in non-stub files
4. Badge in README: "Lean Build: Passing"

**Risk**: Mathlib download + compile time (10-30 min first run) → use GitHub Actions cache or pre-built Mathlib image.

---

## .gitignore Policy

### Root `.gitignore` (NEW)

```gitignore
# Lean build artifacts (delegated to proofs/lean-project/.gitignore)
# Explicit here for visibility:
proofs/lean-project/build/
proofs/lean-project/.lake/
proofs/lean-project/lake-packages/

# Scratch directories
scratch/
*.tmp

# Environment secrets
.env
.env.local
*.key
credentials.json

# OS artifacts
.DS_Store
Thumbs.db
```

### `proofs/lean-project/.gitignore` (EXISTING)

Already covers Lean-specific build artifacts:
```gitignore
/build
/.lake
/lake-packages
.vscode/
*.swp
*.swo
*~
.DS_Store
Thumbs.db
```

**Policy**:
- NEVER commit API keys, credentials, or `.env` files
- NEVER commit `lake-packages/` (Mathlib downloads are reproducible via `lakefile.lean`)
- DO commit `lean-toolchain`, `lakefile.lean`, `.lean` source files, `README.md`
- Build logs (`BUILD_LOG.txt`) in problem directories are OK (evidence of verification)

---

## Mathlib Dependency Strategy

### Current Pin: v4.10.0

`lakefile.lean` specifies:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.10.0"
```

### Update Policy

**When to update**:
- New Mathlib release has critical lemmas for a problem
- Security patch in Lean toolchain
- Community consensus on stable version

**How to update**:
1. Edit `lakefile.lean` and `lean-toolchain` (keep in sync)
2. Delete `lake-packages/`, `.lake/` (force clean fetch)
3. Run `lake build`, verify all existing proofs still check
4. Commit with message: `"Bump Lean to v4.X.Y, Mathlib to v4.X.Y"`
5. Document breaking changes in `proofs/lean-project/CHANGELOG.md` (create if needed)

**Risk**: Mathlib API churn can break proofs. Pin updates to quarterly reviews or specific need.

---

## Pseudo-Lean / Exploration Notes

Until Lean is installed, Formalist can:

1. **Draft pseudo-Lean** in `proofs/<id>/lean/DRAFT.lean` (not buildable):
   ```lean
   -- PSEUDO-LEAN (not type-checked)
   import Mathlib.Data.Nat.Prime

   theorem infinitely_many_primes : ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Nat.Prime p := by
     -- Strategy: Euclid's proof
     -- Assume primes up to n, multiply and add 1, factor
     sorry
   ```

2. **Mathlib search notes** in `docs/MATHLIB_SEARCH.md`:
   - Record search queries: "How to express 'infinitely many' in Lean?"
   - Link to Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
   - Note relevant modules: `Mathlib.Data.Nat.Prime`, `Mathlib.Order.Infinite`

3. **Design conventions**:
   - File naming: `ProofLab/<Domain>.lean` (e.g., `NumberTheory`, `Combinatorics`, `SetTheory`)
   - Theorem naming: `snake_case`, prefix with domain if ambiguous (`nt_goldbach_weak`)
   - Comments: Minimal, only for non-obvious proof steps or references to literature

4. **Do NOT**:
   - Claim to have "run" Lean without installation
   - Fake build logs
   - Mark `status: formal` for pseudo-Lean

---

## Integration with Other Agents

### Research Director
- **To Formalist**: "Formalize statement from `proofs/<id>/STATEMENT.md`"
- **From Formalist**: "Statement formalized, Attack Lead can proceed" OR "Cannot formalize, needs domain expert clarification"

### Problem Scout
- **To Formalist**: "Assess Lean feasibility for candidate problem X"
- **From Formalist**: Feasibility memo (Mathlib coverage, estimated difficulty, similar formalized theorems)

### Attack Lead
- **To Formalist**: "Build `proofs/lean-project/` with my latest edits"
- **From Formalist**: Build log (success/failure), syntax fixes, import suggestions

### Adversarial Reviewer
- **To Formalist**: "Verify proof of theorem X has no `sorry` in critical path"
- **From Formalist**: `grep` output + build log + final verification status

**Communication protocol**: All requests via issue comments or child issues, not inline in code.

---

## Non-Functional Requirements

### Performance
- **Build time**: First build 10-30 min (Mathlib compile), incremental builds <2 min
- **Disk usage**: ~2-4 GB for Mathlib + build artifacts (excluded from git via `.gitignore`)

### Reliability
- **Version pinning**: Reproducible builds via `lean-toolchain` + `lakefile.lean`
- **No network dependency after first build**: `lake-packages/` cached locally (but not committed)

### Security
- **No secrets in Lean code**: Proofs are public mathematics, no credentials
- **No arbitrary code execution**: Lean's type system is trusted, but review `lakefile.lean` for malicious `lake` scripts

### Maintainability
- **Single Lean project**: All formal work in `proofs/lean-project/`, not scattered per-problem
- **Documentation**: This plan + `proofs/lean-project/README.md` + inline Lean comments
- **Ownership**: Formalist owns build health, Attack Lead owns proof attempts, Reviewer blocks bad claims

---

## Risks & Mitigations

### Risk: Lean installation fails on user machine
- **Mitigation**: Installation is a separate blocked issue (OPE-TBD); fail fast, ask for help, document error
- **Fallback**: Pseudo-Lean drafts until installation succeeds

### Risk: Mathlib doesn't have needed definitions
- **Mitigation**: Define locally in `ProofLab/<Domain>.lean`, upstream to Mathlib later if reusable
- **Example**: Custom graph theory definitions before Mathlib's `Combinatorics.SimpleGraph` was mature

### Risk: Proof attempt hits Lean's automation limits
- **Mitigation**: Partial formalization is valid outcome; document gaps, mark `status: informal-with-verified-lemmas`
- **Example**: Statement formal + key lemmas proven, but final assembly too tedious → still valuable

### Risk: Lean version churn breaks proofs
- **Mitigation**: Pin `lean-toolchain` + `lakefile.lean`, update conservatively, test before commit

### Risk: Formalist agent hallucinates "proof" without running `lake build`
- **Mitigation**: Adversarial Reviewer MUST check build log + grep for `sorry`; build failure = claim FAIL

---

## Success Criteria

**Milestone 1: Lean Installed** ✅ COMPLETE (2026-07-31)
- [x] elan + lake on user machine
- [x] `lake build` in `proofs/lean-project/` exits 0
- [x] Trivial theorems in `ProofLab/Basic.lean` type-check
- [x] Build log committed to `proofs/lean-project/BUILD_LOG.txt`

**Milestone 2: First Formalized Statement**
- [ ] Problem selected by Scout + Director
- [ ] Statement in `STATEMENT.md`
- [ ] Lean formalization in `ProofLab/<Domain>.lean` with `sorry`
- [ ] `lake build` confirms statement type-checks
- [ ] Formalist hands off to Attack Lead

**Milestone 3: First Formal Proof**
- [ ] Attack Lead completes proof (no `sorry` in critical path)
- [ ] `lake build` exits 0
- [ ] Adversarial Reviewer approves (no gaps, matches informal statement)
- [ ] `status: formal` marked
- [ ] Claim packet prepared (board decides on external communication)

**Milestone 4: CI Automation (FUTURE)**
- [ ] GitHub Actions workflow `lean-check.yml`
- [ ] Badge in README
- [ ] Automated review comments on PRs with Lean edits

---

## Open Questions

1. **Shared vs. per-problem Lean projects**: Single `proofs/lean-project/` vs. `proofs/<id>/lean/`?
   - **Current answer**: Single project for shared dependencies, symlink or import per-problem files.

2. **Lean educator onboarding**: If Attack Lead is not Lean-fluent, who teaches?
   - **Current answer**: Formalist provides templates, tactic hints, Mathlib pointers; Attack Lead learns by doing.

3. **Partial formalization value**: Accept `status: informal-with-verified-lemmas`?
   - **Current answer**: YES, if key lemmas are formal and gaps are documented honestly.

4. **Mathlib contribution policy**: Upstream useful definitions?
   - **Future decision**: Defer until we have reusable contributions; community review is slow.

5. **Lean vs. other provers for specific domains**: Use Isabelle for analysis-heavy proofs?
   - **Current answer**: Stick to Lean 4 for consistency unless a problem is Lean-impossible.

---

## References

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib 4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) (community help)
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) (beginner tutorial)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) (textbook)

---

## Changelog

- **2026-07-29**: Initial plan. Lean NOT installed. Scaffold exists in `proofs/lean-project/`.
