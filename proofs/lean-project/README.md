# Open Math Lab - Lean 4 Proof Project

This directory contains the Lean 4 project infrastructure for machine-verifiable mathematical proofs in the Open Math Lab.

## Purpose

This scaffold provides:
- Lean 4 toolchain configuration
- Mathlib dependency setup
- Basic project structure for future theorem formalization
- Trivial checked theorems to verify the setup

## Prerequisites

You need to install the Lean 4 toolchain before building this project.

### Installing Lean 4

1. **Install elan** (Lean version manager):
   - Visit: https://github.com/leanprover/elan#installation
   - **Linux/macOS**: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
   - **Windows**: Download and run the installer from the elan releases page

2. **Verify installation**:
   ```bash
   elan --version
   lake --version
   ```

3. The project's `lean-toolchain` file (pinned to `v4.10.0`) will automatically download the correct Lean version when you first build.

## Building the Project

1. **Navigate to the project directory**:
   ```bash
   cd proofs/lean-project
   ```

2. **Build the project** (first build downloads Mathlib - may take several minutes):
   ```bash
   lake build
   ```

3. **Expected output**: 
   - First run will download and compile Mathlib dependencies (this can take 10-30 minutes)
   - Subsequent builds are incremental and much faster
   - Success: no errors, exit code 0
   - The trivial theorems in `ProofLab/Basic.lean` should type-check

## Project Structure

```
proofs/lean-project/
├── lean-toolchain          # Pins Lean version (v4.10.0)
├── lakefile.lean          # Lake build configuration + Mathlib dependency
├── ProofLab.lean          # Top-level module import
├── Main.lean              # Executable entry point (optional)
├── ProofLab/
│   └── Basic.lean         # Stub module with trivial checked examples
└── README.md              # This file
```

## Adding New Theorems

When formalizing mathematical problems:

1. **Create new files** under `ProofLab/` for specific problem domains:
   ```
   ProofLab/
   ├── Basic.lean          # General setup
   ├── NumberTheory.lean   # Number theory problems
   ├── Geometry.lean       # Geometry problems
   └── ...
   ```

2. **Import in `ProofLab.lean`**:
   ```lean
   import ProofLab.Basic
   import ProofLab.NumberTheory
   -- etc.
   ```

3. **Follow Lean 4 + Mathlib conventions**:
   - Use `theorem` for major results
   - Use `lemma` for intermediate steps
   - Use `example` for verification without naming
   - Document non-obvious proofs with `-- comments`

4. **Verify with**: `lake build`

## Verification Workflow

For Open Math Lab theorem claims:

1. Write the informal statement in `proofs/<problem-id>/STATEMENT.md`
2. Formalize in `ProofLab/<ProblemArea>.lean`
3. Build with `lake build` until no errors
4. Only mark `status: formal` after successful build
5. Include build logs in `proofs/<problem-id>/BUILD_LOG.txt`

## Current Status

**This is a scaffold only** - no actual problem formalization yet.

Contains:
- ✅ Lean 4 project structure
- ✅ Mathlib dependency configured
- ✅ Trivial checked theorems (`1 + 1 = 2`, etc.)
- ❌ No actual mathematical problem statements
- ❌ No CI automation (future work)

## Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib 4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) (community help)

## Notes

- **No global installation required for this repo** - elan/lake are user-level tools
- **First build is slow** - Mathlib compilation takes time; subsequent builds are fast
- **Version pinning** - `lean-toolchain` and `lakefile.lean` are locked to v4.10.0 for reproducibility
- **CI future work** - Manual verification only for now; GitHub Actions integration is a separate issue
