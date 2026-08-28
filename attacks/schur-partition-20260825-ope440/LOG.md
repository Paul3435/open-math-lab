# LOG — OPE-440 Schur Glaisher attack

## 2026-08-25 — Attack Lead

- Branched `ope/440-schur-glaisher` from `origin/main` (avoid concurrent OPE-433 dirty tree).
- Restored OPE-424 `Schur.lean` (finite ladder) onto branch; wired `import ProofLab.Schur`.
- Python Glaisher bijection verified n=0..30 (expand bits / collapse odd kernel).
- Authored `ProofLab/SchurGlaisher.lean`: recursive oddPart/val2, expandPart/collapsePart,
  multiset + partition maps, sum preservation, residue legality. Zero sorry.
- `lake env lean` + `lake build ProofLab` green.
- Level B (Finset bijection / ∀n card) not closed this budget — inverse/Nodup-across-kernels remaining.
- No novelty claim; formalize-only classical Schur 1926.
