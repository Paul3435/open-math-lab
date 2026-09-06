/-
Hou–Zeng odd-prime + Fibonacci + Catalan, Level A only (encoding + n≤30
witnesses). Formalize-only bounded slice — **not** the prize.

status: open problem, encoding+witness only, **no novelty claim**,
**default no claim**. Do **not** describe this as collecting US$1,000 /
US$200. Do **not** email Hou or Zeng.

Mathlib v4.10.0 pin `a719ba5c3115` has `Nat.Prime`, `Nat.fib`
(`Data/Nat/Fib/Basic.lean`; `fib 0 = 0`, `1 = 1`, `2 = 1`, `3 = 2`),
and `catalan` (`Combinatorics/Enumerative/Catalan.lean`; `catalan 0 = 1`,
`1 = 1`, `2 = 2`) as **infra**. ZERO named Hou–Zeng / A154404 /
`prime + Fibonacci + Catalan` theorem under `Mathlib/` or `Archive/`.
Completing a bounded encoding + small-n witnesses is the gap. Do **not**
import `Archive.*` or `google-deepmind/formal-conjectures`. Do **not**
re-prove `Nat.Prime` / `Nat.fib` / `catalan`.

Pin: `catalog/problems/hou-zeng-pfc/STATEMENT.md` (OPE-1043; Scout
OPE-1028 leftover slot #2; Director OPE-1042). Encoding: every
`5 ≤ n ≤ N` is an odd prime plus a positive Fibonacci plus a Catalan.
`s ≥ 2` pins positivity (`Nat.fib 0 = 0`; `Nat.fib 1 = Nat.fib 2 = 1`).
**Landmine:** OEIS A154404 Maple starts `Fibo(1)=1`, `Fibo(2)=2` —
`Fibo(2)=2` is `Nat.fib 3`, not `Nat.fib 2`. Odd prime means `p ≠ 2`.
`n = 5 = 3 + 1 + 1` must work. Zero `sorry`.

This is **not** Sun's two-Fibonacci conjecture (`n = p + F_s + F_t`).
This is **not** Goldbach / weak Goldbach / Crocker prime+two-powers-of-two.
This is **not** sun-135 (Director OPE-1042 REJECT: proved 2021; cash not
live). This is **not** krenn-gu (Level A #101 + Level B #102 landed).
This is **not** expander-mixing / mason-stothers / zsigmondy-theorem /
erdos-ramsey-lower / descartes-rule-of-signs / e-irrational /
n-fold-inclusion-exclusion / wolstenholme-theorem / lovasz-local-lemma /
korselt-carmichael / vosper / heron / euclid-euler / bipartite / moore /
stirling / kst / pentagonal / sunflower / CNS / kk / oddtown / cayley /
mycielski / friendship / havel / menger / greedy / Brooks / Dilworth /
Eulerian / König / Dirac / EKR. Leave OPE-403 alone.

Level A (this module, **not** labelled Hou–Zeng / **not** the prize):
encoding compiles; `n ≤ 30` via explicit witnesses + `native_decide`.
Zero sorry.
Level B Python overlap verifier raising `N` is **out of this ticket**.
Namesake `∀ n>4` is **out of v1**. Not sorry-ed.

Transcribed classical Hou–Zeng 2009-01-09 conjecture (OEIS A154404;
Sun arXiv:0901.3075 Remark 1.14; PPL 013). Computationally verified to
`5×10^13` (McNeil) — the $200 counterexample is **not** a one-wave
target. No novelty claim. Default no claim.
-/
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ProofLab.HouZeng

/-! ## Indexing landmine (OEIS Maple `Fibo` vs `Nat.fib`) -/

/-- Mathlib `Nat.fib` table used by the encoding. Glue, **not** labelled
Hou–Zeng. `Nat.fib 3 = 2` is OEIS Maple `Fibo(2)`. -/
theorem fib_index_table :
    Nat.fib 0 = 0 ∧ Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧ Nat.fib 3 = 2 ∧
      Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧ Nat.fib 6 = 8 ∧ Nat.fib 7 = 13 ∧
      Nat.fib 8 = 21 := by
  native_decide

/-- OEIS A154404 Maple `Fibo(2) = 2` is `Nat.fib 3`, not `Nat.fib 2`. -/
theorem oeis_fibo_two_eq_nat_fib_three : Nat.fib 3 = 2 := by
  native_decide

/-- Mathlib `catalan` table used by the encoding. Glue, **not** labelled
Hou–Zeng. -/
theorem catalan_index_table :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧ catalan 3 = 5 ∧
      catalan 4 = 14 := by
  native_decide

/-! ## Encoding (not labelled Hou–Zeng) -/

/-- Odd prime: `Nat.Prime` and `p ≠ 2`. Infra reuse, not a re-proof. -/
def IsOddPrime (p : ℕ) : Prop := Nat.Prime p ∧ p ≠ 2

instance (p : ℕ) : Decidable (IsOddPrime p) := by
  dsimp [IsOddPrime]
  infer_instance

/-- Bounded Hou–Zeng summand predicate. **Not** labelled Hou–Zeng / **not**
the prize. `s ≥ 2` so the Fibonacci summand is positive (`Nat.fib 0 = 0`).
Catalan index `t ≥ 0` is free on `ℕ` (`catalan 0 = 1`). -/
def IsOddPrimeFibCatalan (n p s t : ℕ) : Prop :=
  Nat.Prime p ∧ p ≠ 2 ∧ 2 ≤ s ∧ n = p + Nat.fib s + catalan t

instance (n p s t : ℕ) : Decidable (IsOddPrimeFibCatalan n p s t) := by
  dsimp [IsOddPrimeFibCatalan]
  infer_instance

/-! ## Level A witnesses — `5 ≤ n ≤ 30` (not labelled Hou–Zeng) -/

/-- Explicit `(p, s, t)` for each `5 ≤ n ≤ 30`. Lookup only; **not** the
prize. Default triple is unused (out of range). -/
def witness : ℕ → ℕ × ℕ × ℕ
  | 5 => (3, 2, 0)
  | 6 => (3, 2, 2)
  | 7 => (3, 3, 2)
  | 8 => (3, 4, 2)
  | 9 => (3, 2, 3)
  | 10 => (3, 3, 3)
  | 11 => (3, 4, 3)
  | 12 => (3, 6, 0)
  | 13 => (3, 5, 3)
  | 14 => (5, 6, 0)
  | 15 => (5, 5, 3)
  | 16 => (3, 6, 3)
  | 17 => (3, 7, 0)
  | 18 => (3, 2, 4)
  | 19 => (3, 3, 4)
  | 20 => (3, 4, 4)
  | 21 => (3, 7, 3)
  | 22 => (3, 5, 4)
  | 23 => (5, 7, 3)
  | 24 => (5, 5, 4)
  | 25 => (3, 6, 4)
  | 26 => (3, 8, 2)
  | 27 => (5, 6, 4)
  | 28 => (5, 8, 2)
  | 29 => (3, 8, 3)
  | 30 => (3, 7, 4)
  | _ => (0, 0, 0)

/-- Required small case: `5 = 3 + Nat.fib 2 + catalan 0 = 3 + 1 + 1`.
Glue, **not** labelled Hou–Zeng. -/
theorem hou_zeng_five :
    ∃ p s t : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ 2 ≤ s ∧
      5 = p + Nat.fib s + catalan t :=
  ⟨3, 2, 0, by native_decide⟩

/-- Level A bounded encoding. **Not** labelled Hou–Zeng, **not** the prize.
Zero `sorry`. Namesake `∀ n>4` is out of v1 and is not sorry-ed. -/
theorem hou_zeng_le_N :
    ∀ n, 5 ≤ n → n ≤ 30 →
      ∃ p s t : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ 2 ≤ s ∧
        n = p + Nat.fib s + catalan t := by
  intro n h5 h30
  refine ⟨(witness n).1, (witness n).2.1, (witness n).2.2, ?_⟩
  interval_cases n <;> native_decide

end ProofLab.HouZeng
