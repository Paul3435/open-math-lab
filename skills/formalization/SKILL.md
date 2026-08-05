# Formalization Skill Pack

## Purpose

Convert a mathematical target (statement, proof sketch, or verified computation) into a
machine-checked Lean 4 + Mathlib artifact in `proofs/lean-project/`. Owned by the **Formalist**.

## When to use this pack

- A candidate has a precise, pinned statement (see `docs/LEAN_PLAN.md`) and you want a
  machine-checkable gate instead of an informal proof.
- A computational run passed and you want the corresponding definition/result type-checked.
- You need to check **before** an attack whether a theorem already exists in the local Mathlib
  pin — a novelty / de-duplication screen (GAP-4).
- Reviewers flagged `sorry` use or definition drift; you need a clean, sorry-free build.

## ProofLab layout (single source of truth)

- Project root: `proofs/lean-project/` (Lake, `lean-toolchain` pinned v4.10.0, Mathlib dep).
- Modules import pattern (see `ProofLab.lean`, `Main.lean`).
- New theorems go in `ProofLab/<ProblemArea>.lean` and are imported top-level so `lake build`
  covers them.
- Do **not** edit infra/toolchain without a ticket (OPE-17 installed elan+lake; keep user-local).

## Mathlib module discovery (do this FIRST)

Before writing any theorem, grep the **locally pinned** Mathlib for existing results:

```bash
cd proofs/lean-project && grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib --include=*.lean
```

(or `lake env lean`, `#check` / `#find` in the editor). The on-disk pin is authoritative — a
theorem that exists in a newer Mathlib is NOT in our pin. Treat "Mathlib gap" claims as
unverified until grepped against the local pin (lab lesson OPE-25).

## Statement hygiene

- Pin definitions and both sides of the statement to a cited source BEFORE writing Lean.
- Check early degenerate cases (e.g. n=2 for partition identities) — swapped sides often
  fail at small n (lab lesson OPE-21/OPE-26).
- Use `theorem` for major results, `lemma` for intermediate steps, `example` for checks.
- Name freely but keep top-level imports clean; add a header comment naming the target (e.g.
  "Erdős (1965) Z_p averaging proof — OPE-23").

## Tactics to prefer

`omega` for linear arithmetic, `nlinarith` for nonlinear, `norm_num`/`ring` for algebra,
`linarith`, `simp`/`aesop` for goals they close. Use `by_cases`, `Nat.mod_eq_of_lt`,
`Nat.mod_eq_sub_mod`, `Nat.sub_lt_right_of_lt_add` for modular/order reasoning (patterns
already validated in `ErdosSumFree.lean`). Keep goals small; extract hard steps as lemmas.

## `sorry` / completeness policy (non-negotiable gate)

- A file with `sorry` is **never** a review-ready proof. Remove every `sorry` before handing
  to Adversarial Reviewer.
- "Compute pass + Lean `sorry` = review block" (lab lesson). If a `sorry` remains, mark the
  claim `informal` / `heuristic`, not `formal`.
- A proof is `formal` / claim-ready only after a **successful `lake build`** with exit 0 and
  zero `sorry`.

## Build & verify

```bash
cd proofs/lean-project
lake build                  # must exit 0, no errors
# capture log for artifact
lake build > ../ProofLab/BUILD_LOG.txt 2>&1
```

## Checklist BEFORE claiming progress

- [ ] Statement pinned to real source, degenerate cases checked
- [ ] No `sorry` in the file
- [ ] `lake build` exits 0 (log attached)
- [ ] Result NOT already in local Mathlib (grepped) — else tag `formalize-only`/`known`
- [ ] `status: formal` only after successful build; otherwise `informal`/`heuristic`

## Anti-patterns

- Grepping the internet Mathlib instead of the local pin
- Removing `sorry` "in the wrong theorem" so it type-checks but proves nothing (review trap)
- Claiming novelty for a theorem that is already in Mathlib
- Editing the Lean toolchain / global install without a ticket

## Maintenance

- Promote tactics/lemma patterns that recur (e.g. the `middle_third_sumfree` modular lemma)
  into shared helper files or this pack.
- Record each successful formalization backlink in `catalog/` (e.g. `formalization_target`).