# Attack log — schur-number

| when | agent | strategy | result |
|------|-------|----------|--------|
| 2026-08-08 | Attack Lead | Formalize-only via `native_decide`: k-colourings of `{1,…,n}` as `f : Fin n → Fin k`, monochromatic-solution predicate `HasMonoSchur` (`∃ x y, x+y=z` same colour, x=y allowed, standard Schur sum-free convention), certified exhaustive decision | **S(2)=4, S(3)=13 landed, Lean ZERO-sorry** (`ProofLab/SchurNumber.lean`): `schur2_lower` (classes {1,4}/{2,3} on `Fin 4`) + `schur2_le_4` (every 2-colouring of `Fin 5` has mono solution) ⇒ S(2)=4, least-forcing N=5; `schur3_lower` (classes {1,4,7,10,13}/{2,3,11,12}/{5,6,8,9} on `Fin 13`) + `schur3_le_13` (every 3-colouring of `Fin 14` has mono solution) ⇒ S(3)=13, least-forcing N=14. `lake env lean ProofLab/SchurNumber.lean` exit 0. |

## Status

- **Done, zero `sorry`, `lake env lean` green:** S(2)=4 and S(3)=13.
- **Convention pinned** in `STATEMENT.md` / Lean docstring: a colour class is
  sum-free when it contains no `x+y=z` with **`x=y` allowed** (standard
  Schur convention matching S(2)=4, S(3)=13 and the classical forcing N=5/14).

## Convention divergence note (issue brief)

The OPE-46 brief and the older `STATEMENT.md` phrasing said "distinct `x, y`".
Under that **distinct-only** reading, `[1,14]` is **not** 3-Schur-forcing (a
3-colouring of `[1,14]` exists with no monochromatic `x+y=z`, verified
computationally), so `S(3)` would not equal 13.  The correct classical
convention (x=y allowed) gives the intended `S(2)=4`, `S(3)=13`.  **Lean and
STATEMENT.md now pin the standard convention; the "distinct" phrasing is a
known defect in the original brief, flagged for the reviewer/board.**

## Residual / notes

- `S(3) ≤ 13` upper bound proved by exhaustive `native_decide` over all
  `3^14 ≈ 4.8M` colourings (≈2 min compile+run on this host).  A hand proof
  (classical forcing) is possible but unnecessary for the certificate.
- `S(4)=44` (Heule 2018, SAT-certified) out of scope — would need a SAT
  certificate, not a bare enumeration.
- Not wired into Mathlib (no `SchurNumber` content exists there); left
  self-contained in `ProofLab`.

