# Experimental Skill Pack

## Purpose

Standard for computational experimentation feeding mathforge attacks: small-case enumeration,
OEIS cross-checks, SAT/SMT routes, reproducible certificates, and a clear compute-vs-proof
policy. Owned by the **Attack Lead**.

## When to use this pack

- The target admits a decidable finite check (enumerate small cases, search for
  counterexamples / witnesses).
- You want to *screen* a candidate cheaply before spending proof effort — e.g. verify the
  first N cases of a conjectured formula or inequality.
- You need reproducible evidence (witness files, certificates) that Adversarial Reviewer and
  the board can re-run.
- OEIS/literature lookup to detect a **known sequence or theorem** before an attack is funded
  (GAP-4 novelty screen).

## Policy: compute is evidence, not proof

- A passing computational run NEVER proves a general statement. Label results
  `heuristic`/`informal` unless a Lean build checks the theorem.
- "Confusing computational evidence with proof" is a lab anti-pattern; reviewers block
  compute-only claims.
- Computational checks are a *gate and a sanity check*, not a deliverable claim on their own.

## Workflow

1. **Small-case enumeration first**: write `verify_<problem>.py` under `attacks/<attack>/`,
   cover the first 10–20 cases, and record exact counts/ranges.
2. **OEIS cross-check**: for sequences, `curl https://oeis.org/search?q=<terms>`; a match to
   a known sequence is a strong prior that the result is classical — flag it in the log.
3. **SAT/SMT** when a search has constraints: encode small instances, record the solver,
   version, and runtime.
4. **Certificates**: emit machine-readable witness files (JSON), e.g. `witness_5.json` style;
   reviewers re-run or at least re-parse them.
5. **Isomorphism care**: enumerate canonical forms, not raw objects, and cross-check counts
   with a second method when representation counts are ambiguous (lab lesson from graceful
   caterpillars: 2,142 → 560 after removing duplicates).
6. **Record compute-vs-proof split** in the attack log: what the run established, what remains
   for Lean.

## Reproducibility checklist

- [ ] Script committed under `attacks/<attack>/`
- [ ] Deterministic seed / bounded ranges recorded
- [ ] Output (counts, witnesses, failures) written to files in the attack dir
- [ ] OEIS/known-theorem check result logged
- [ ] Run is re-runnable by Adversarial Reviewer or a fresh agent

## Before declaring progress

- [ ] Compute + Lean `sorry` = review block; escalate to Formalist before any claim
- [ ] Known/classical result → tag `known-classical`, do NOT re-fund as novel (GAP-4)
- [ ] State in the log: which part is computation, which is proof

## Anti-patterns

- Chasing higher bounds with no bound on tokens/time (stop at budget; hand off)
- Presenting an enumerator's "no counterexamples found" as a theorem
- Ignoring OEIS hits that show the sequence is classical
- Non-reproducible one-off scripts that die with the scratch dir

## Maintenance

- Archive dead-end techniques with "why it failed" notes.
- Promote reusable enumerator patterns (mod-3 construction checks, AHU canonical forms,
  certificate JSON schema) into this pack.