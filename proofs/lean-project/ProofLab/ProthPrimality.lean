/-
Proth-form + witness on named integers — Level A only
(`3 = 1·2¹+1` / `5 = 1·2²+1` / `13 = 3·2²+1` with witness `2`).
**Not labelled Proth.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `ZMod` / `Pow` / `Odd` /
`Nat.Prime` as **infra**. ZERO named Proth theorem / `proth` /
`ProthWitness` / `prothPrime` / Pépin / Pocklington under
`Mathlib/` or `Archive/` or `ProofLab/`. Completing the Level A
form+witness on `3` / `5` / `13` is the gap this ticket lands.
The Level B namesake `proth_primality` (Proth form + witness ⇒
`Nat.Prime`) is **out of this ticket** and is **not** sorry-ed.
Pépin / Fermat numbers / Gauss–Wantzel / Pocklington as namesake
are residual of this id.

Pin: `catalog/problems/proth-primality/STATEMENT.md`
(OPE-1305; Scout OPE-1294 leftover slot #2; Director OPE-1304).
Encoding: `IsProth` / `ProthWitness` via Mathlib `ZMod` / `Pow` /
`Odd`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `euler_criterion` (`LegendreSymbol/Basic.lean` L58:
prime-modulus quadratic residuosity, **different direction**).
**USE `ZMod` / `pow` glue; do not re-prove; do not cite as Proth.**
This is **not** `lucas_lehmer_sufficiency` (`LucasLehmer.lean` L476)
— already-in different Mersenne test. Do **not** cite as Proth.
This is **not** Korselt / Carmichael
(`ProofLab/KorseltCarmichael.lean`, consumed). Compositeness
criterion ≠ Proth sufficiency.
This is **not** Euclid–Euler even perfect / Mersenne
(`ProofLab/EuclidEulerPerfect.lean`, consumed).
This is **not** Wantzel / Gauss–Wantzel / Fermat-prime regular
polygons (`ProofLab/WantzelConstructible.lean`, consumed #133).
Fermat `2^{2^m}+1` is a special Proth family — residual of this
id. Do **not** sorry Pépin / Gauss–Wantzel.
This is **not** Frucht graph Aut (`ProofLab/FruchtGraphAut.lean`,
consumed #150). Do **not** prove Frucht here.
This is **not** platonic-solids (`ProofLab/PlatonicSolids.lean`,
PR #147) / egyptian-fractions (`ProofLab/EgyptianFractions.lean`,
PR #148).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the Proth-form + witness predicate on named integers:
`3 = 1·2¹+1` witness `2`, `5 = 1·2²+1` witness `2`, and
`13 = 3·2²+1` witness `2`, **not labelled Proth**. Odd `k` and
`k < 2ⁿ` are load-bearing. `ZMod` power `= -1` is load-bearing.

Level A: `3` / `5` / `13` form+witness. Optional extra: `9` is
Proth form and composite. **Not** labelled Proth.

Transcribed classical argument (F. Proth, *Theoremes sur les
nombres premiers*, Comptes rendus 87 (1878) 926). Compact form:
Wikipedia *Proth's theorem*. Type pin: `IsProth` / `ProthWitness`
/ `ZMod` pow `= -1`. `euler_criterion` is a different
prime-modulus theorem. Lucas–Lehmer is a different already-in
Mersenne test. No novelty claim. Default no claim.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.ProthPrimality

/-! ## Level A: 3 / 5 / 13 form+witness 2
(not labelled Proth) -/

/-- Proth form `N = k·2ⁿ+1` with `k` odd, `n > 0`, and `k < 2ⁿ`.
Encoding; **not** labelled Proth. Does **not** re-prove `Odd` /
`Nat.Prime`. -/
def IsProth (N k n : ℕ) : Prop :=
  N = k * 2 ^ n + 1 ∧ Odd k ∧ 0 < n ∧ k < 2 ^ n

/-- Modular witness `a^{(N-1)/2} ≡ −1 (mod N)`. Encoding; **not**
labelled Proth. Uses Mathlib `ZMod` / `Pow`; does **not** re-prove
`euler_criterion` / `lucas_lehmer_sufficiency`. -/
def ProthWitness (N a : ℕ) : Prop :=
  0 < a ∧ ((a : ZMod N) ^ ((N - 1) / 2) = -1)

/-- `3 = 1·2¹+1` with witness `2`. Glue; **not** labelled Proth. -/
theorem proth_three : IsProth 3 1 1 ∧ ProthWitness 3 2 := by
  refine ⟨⟨rfl, odd_one, Nat.succ_pos 0, ?lt⟩, ⟨Nat.succ_pos 1, ?w⟩⟩
  · decide
  · -- `(2 : ZMod 3) ^ 1 = 2 = -1`
    change (2 : ZMod 3) ^ 1 = -1
    rw [pow_one, eq_neg_iff_add_eq_zero]
    decide

/-- `5 = 1·2²+1` with witness `2`. Glue; **not** labelled Proth. -/
theorem proth_five : IsProth 5 1 2 ∧ ProthWitness 5 2 := by
  refine ⟨⟨rfl, odd_one, Nat.succ_pos 1, ?lt⟩, ⟨Nat.succ_pos 1, ?w⟩⟩
  · decide
  · -- `(2 : ZMod 5) ^ 2 = 4 = -1`
    change (2 : ZMod 5) ^ 2 = -1
    rw [sq, eq_neg_iff_add_eq_zero]
    decide

/-- `13 = 3·2²+1` with witness `2`. Glue; **not** labelled Proth. -/
theorem proth_thirteen : IsProth 13 3 2 ∧ ProthWitness 13 2 := by
  refine ⟨⟨rfl, ?odd, Nat.succ_pos 1, ?lt⟩, ⟨Nat.succ_pos 1, ?w⟩⟩
  · exact ⟨1, rfl⟩
  · decide
  · -- `(2 : ZMod 13) ^ 6 = 64 = -1`
    -- 2^6 = 64, 64 + 1 = 65 = 5 * 13
    change (2 : ZMod 13) ^ 6 = -1
    rw [eq_neg_iff_add_eq_zero]
    decide

/-- Optional extra: `9 = 1·2³+1` is Proth *form* but composite.
Not the converse; do not claim unattested composites.
Glue; **not** labelled Proth. -/
theorem nine_isProth_not_prime : IsProth 9 1 3 ∧ ¬ Nat.Prime 9 := by
  refine ⟨⟨rfl, odd_one, Nat.succ_pos 2, ?lt⟩, ?comp⟩
  · decide
  · decide

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem proth_primality {N k n a : ℕ}
      (h : IsProth N k n) (w : ProthWitness N a) :
      Nat.Prime N
Pépin / Fermat numbers / Gauss–Wantzel / Pocklington extras
are residual of this id, not extra namesakes.
-/

end ProofLab.ProthPrimality
