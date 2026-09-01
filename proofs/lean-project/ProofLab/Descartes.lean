/-
Descartes' rule of signs (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Polynomial.coeff` / `natDegree` / `eval` / `IsRoot` /
`Polynomial.roots` as a `Multiset` (`Algebra/Polynomial/Roots.lean`) and
`Real.sign`. ZERO named Descartes / `signChanges` / rule-of-signs bound under
`Mathlib/` or `Archive/`. Completing the namesake is the gap. Wiedijk 100.yaml
#100 has only an external github link (Timeroot `lean-descartes-signs`) — **not**
a Mathlib `decl`. Do **not** import that file. Do **not** import `Archive.*`.

Pin: `catalog/problems/descartes-rule-of-signs/STATEMENT.md` (OPE-843; Scout
OPE-838 recommended prime; Director OPE-842). Encoding: `ℝ[X]`,
`Polynomial.roots` filter `0 < ·`, `signChanges` on nonzero `coeff` from degree
0 up (zeros skipped). Multiplicity via `Multiset` is load-bearing. Zero `sorry`.
Do not import `Archive.*`.

This is **not** the rational root theorem (`RationalRoot.lean` already Mathlib).
This is **not** Eisenstein (`irreducible_of_eisenstein_criterion` already Mathlib).
This is **not** Gauss's lemma. This is **not** FTA (`Complex.exists_root`).
This is **not** Rolle / MVT (`exists_deriv_eq_slope` already Mathlib — use, do
not re-prove). This is **not** Chebyshev `T_n(cos θ) = cos(nθ)`.
This is **not** Budan–Fourier / Sturm / Eneström–Kakeya / Gauss–Lucas.
This is **not** n-fold PIE (consumed PR #88).
This is **not** Wolstenholme (consumed #89 honest partial).
This is **not** e-irrational / e-transcendental / π-irrational.
Leave OPE-403 alone.

v1 is the **inequality** (positive real roots with multiplicity ≤ coefficient
sign changes). The even-difference strengthening is **not** required for the
namesake and is **not** a second theorem.

Level A `same_sign_coeff_no_positive_root` is the zero-change vanishing
(all nonzero coefficients the same sign ⇒ no positive root), via `eval`
positivity on `(0, ∞)`. **Not** labelled Descartes.
Level B namesake `descartes_rule_of_signs` is **not** sorry-ed: Segner's
lemma (multiplying by `X − C a` for `a > 0` raises `signChanges` by at least
one) did not close this heartbeat. Honest partial. `signChanges` is the only
new def.

Transcribed classical argument (Descartes, *La Géométrie*, 1637; Wiedijk 100
Theorem 100). Compact form: Wikipedia *Descartes' rule of signs* — the
inequality. Timeroot external Lean is **not** Mathlib.
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Polynomial List
open scoped Classical

noncomputable section

namespace ProofLab.Descartes

/-! ## Sign-change count (only new def) -/

/-- Number of sign changes in a list of real numbers, consecutive pairs.
Zeros are **not** skipped here — callers pass the already-filtered nonzero
coefficient list. -/
def signChangesAux : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a * b < 0 then 1 else 0) + signChangesAux (b :: t)

/-- Nonzero coefficients of `p`, from degree 0 up through `natDegree`.
Zeros in the coefficient list are skipped (classical Descartes convention). -/
def nonzeroCoeffs (p : ℝ[X]) : List ℝ :=
  (List.range (p.natDegree + 1)).filterMap fun i =>
    if p.coeff i = 0 then none else some (p.coeff i)

/-- Number of sign changes in nonzero coefficients of `p`, from degree 0 up,
zeros skipped. -/
def signChanges (p : ℝ[X]) : ℕ :=
  signChangesAux (nonzeroCoeffs p)

@[simp] lemma signChangesAux_nil : signChangesAux [] = 0 := rfl

@[simp] lemma signChangesAux_singleton (a : ℝ) : signChangesAux [a] = 0 := rfl

lemma signChangesAux_cons_cons (a b : ℝ) (t : List ℝ) :
    signChangesAux (a :: b :: t) =
      (if a * b < 0 then 1 else 0) + signChangesAux (b :: t) :=
  rfl

lemma signChangesAux_eq_zero_of_nonneg_products :
    ∀ l : List ℝ,
      (∀ a ∈ l, ∀ b ∈ l, 0 ≤ a * b) → signChangesAux l = 0
  | [] => fun _ => rfl
  | [_] => fun _ => rfl
  | a :: b :: t => by
    intro h
    have hab : 0 ≤ a * b := h a (mem_cons_self _ _) b (mem_cons_of_mem _ (mem_cons_self _ _))
    have hneg : ¬ a * b < 0 := not_lt.mpr hab
    rw [signChangesAux_cons_cons, if_neg hneg, zero_add]
    refine signChangesAux_eq_zero_of_nonneg_products (b :: t) ?_
    intro x hx y hy
    exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)

lemma mem_nonzeroCoeffs {p : ℝ[X]} {a : ℝ} (ha : a ∈ nonzeroCoeffs p) :
    ∃ i, p.coeff i = a ∧ a ≠ 0 := by
  simp only [nonzeroCoeffs, mem_filterMap, mem_range] at ha
  obtain ⟨i, _hi, hopt⟩ := ha
  by_cases hz : p.coeff i = 0
  · simp [hz] at hopt
  · simp [hz] at hopt
    rw [hopt] at hz
    exact ⟨i, hopt, hz⟩

lemma coeff_mem_nonzeroCoeffs {p : ℝ[X]} {i : ℕ} (hi : p.coeff i ≠ 0) :
    p.coeff i ∈ nonzeroCoeffs p := by
  simp only [nonzeroCoeffs, mem_filterMap, mem_range]
  refine ⟨i, Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi), ?_⟩
  simp [hi]

lemma signChanges_eq_zero_of_same_sign {p : ℝ[X]}
    (hsign : ∀ i j, p.coeff i ≠ 0 → p.coeff j ≠ 0 → 0 ≤ p.coeff i * p.coeff j) :
    signChanges p = 0 := by
  unfold signChanges
  refine signChangesAux_eq_zero_of_nonneg_products _ ?_
  intro a ha b hb
  obtain ⟨i, rfl, hia⟩ := mem_nonzeroCoeffs ha
  obtain ⟨j, rfl, hjb⟩ := mem_nonzeroCoeffs hb
  exact hsign i j hia hjb

lemma mul_nonneg_of_chain {a b c : ℝ} (hb : b ≠ 0)
    (hab : 0 ≤ a * b) (hbc : 0 ≤ b * c) : 0 ≤ a * c := by
  have hbb : 0 < b * b := mul_self_pos.mpr hb
  have hprod : 0 ≤ (a * c) * (b * b) := by nlinarith
  exact nonneg_of_mul_nonneg_left hprod hbb

lemma same_sign_of_signChangesAux_eq_zero (l : List ℝ)
    (hnz : ∀ x ∈ l, x ≠ 0) (hV : signChangesAux l = 0) :
    ∀ x ∈ l, ∀ y ∈ l, 0 ≤ x * y := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a l ih =>
    match l with
    | [] =>
      intro x hx y hy
      have hx' : x = a := by simpa using hx
      have hy' : y = a := by simpa using hy
      rw [hx', hy']
      nlinarith
    | b :: t =>
      have hab0 : ¬ a * b < 0 := by
        rw [signChangesAux_cons_cons] at hV
        intro hlt
        simp [hlt] at hV
      have hab : 0 ≤ a * b := not_lt.mp hab0
      have hVt : signChangesAux (b :: t) = 0 := by
        rw [signChangesAux_cons_cons, if_neg hab0, zero_add] at hV
        exact hV
      have hnz' : ∀ z ∈ b :: t, z ≠ 0 := fun z hz => hnz z (mem_cons_of_mem _ hz)
      have ih' := ih hnz' hVt
      have hb0 : b ≠ 0 := hnz b (mem_cons_of_mem _ (mem_cons_self _ _))
      intro x hx y hy
      have hx' : x = a ∨ x ∈ b :: t := mem_cons.mp hx
      have hy' : y = a ∨ y ∈ b :: t := mem_cons.mp hy
      rcases hx' with hxa | hxbt
      · rcases hy' with hya | hybt
        · rw [hxa, hya]; nlinarith
        · rw [hxa]
          rcases mem_cons.mp hybt with hyb | hyt
          · rw [hyb]; exact hab
          · exact mul_nonneg_of_chain hb0 hab
              (ih' b (mem_cons_self _ _) y (mem_cons_of_mem _ hyt))
      · rcases hy' with hya | hybt
        · rw [hya]
          rcases mem_cons.mp hxbt with hxb | hxt
          · rw [hxb, mul_comm]; exact hab
          · have := mul_nonneg_of_chain hb0 hab
              (ih' b (mem_cons_self _ _) x (mem_cons_of_mem _ hxt))
            rwa [mul_comm]
        · exact ih' x hxbt y hybt

lemma ne_zero_of_mem_nonzeroCoeffs {p : ℝ[X]} {a : ℝ}
    (ha : a ∈ nonzeroCoeffs p) : a ≠ 0 := by
  obtain ⟨_, _, h⟩ := mem_nonzeroCoeffs ha
  exact h

lemma same_sign_of_signChanges_eq_zero {p : ℝ[X]}
    (hV : signChanges p = 0) (i j : ℕ)
    (hi : p.coeff i ≠ 0) (hj : p.coeff j ≠ 0) :
    0 ≤ p.coeff i * p.coeff j :=
  same_sign_of_signChangesAux_eq_zero (nonzeroCoeffs p)
    (fun x hx => ne_zero_of_mem_nonzeroCoeffs hx) hV _
    (coeff_mem_nonzeroCoeffs hi) _ (coeff_mem_nonzeroCoeffs hj)

/-! ## Level A — same-sign coefficients ⇒ no positive root (not labelled Descartes) -/

/-- If every coefficient is nonnegative and `p ≠ 0`, then `eval x p > 0` for
`x > 0`. Engine, not labelled Descartes. -/
theorem eval_pos_of_nonneg_coeff {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ n, 0 ≤ p.coeff n) {x : ℝ} (hx : 0 < x) : 0 < eval x p := by
  rw [eval_eq_sum, sum_def]
  refine lt_of_le_of_ne ?_ ?_
  · exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (h n) (pow_nonneg (le_of_lt hx) n)
  · intro h0
    have hmem : p.natDegree ∈ p.support := by
      rw [mem_support_iff]
      exact leadingCoeff_ne_zero.mpr hp
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg
          (fun n _ => mul_nonneg (h n) (pow_nonneg (le_of_lt hx) n))).1
        h0.symm p.natDegree hmem
    have hpos : 0 < p.leadingCoeff * x ^ p.natDegree :=
      mul_pos (lt_of_le_of_ne (h p.natDegree) (leadingCoeff_ne_zero.mpr hp).symm)
        (pow_pos hx _)
    exact hpos.ne' hterm

/-- If every coefficient is nonpositive and `p ≠ 0`, then `eval x p < 0` for
`x > 0`. Engine, not labelled Descartes. -/
theorem eval_neg_of_nonpos_coeff {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ n, p.coeff n ≤ 0) {x : ℝ} (hx : 0 < x) : eval x p < 0 := by
  have hneg : (-p) ≠ 0 := neg_ne_zero.mpr hp
  have hnn : ∀ n, 0 ≤ (-p).coeff n := by
    intro n
    rw [coeff_neg, neg_nonneg]
    exact h n
  have := eval_pos_of_nonneg_coeff hneg hnn hx
  rw [eval_neg] at this
  linarith

lemma coeff_nonneg_of_same_sign_pos_leading {p : ℝ[X]} (hp : p ≠ 0)
    (hsign : ∀ i j, p.coeff i ≠ 0 → p.coeff j ≠ 0 → 0 ≤ p.coeff i * p.coeff j)
    (hle : 0 < p.leadingCoeff) (n : ℕ) : 0 ≤ p.coeff n := by
  by_cases hn : p.coeff n = 0
  · simp [hn]
  · have hprod : 0 ≤ p.coeff n * p.leadingCoeff :=
      hsign n p.natDegree hn (leadingCoeff_ne_zero.mpr hp)
    nlinarith

lemma coeff_nonpos_of_same_sign_neg_leading {p : ℝ[X]} (hp : p ≠ 0)
    (hsign : ∀ i j, p.coeff i ≠ 0 → p.coeff j ≠ 0 → 0 ≤ p.coeff i * p.coeff j)
    (hle : p.leadingCoeff < 0) (n : ℕ) : p.coeff n ≤ 0 := by
  by_cases hn : p.coeff n = 0
  · simp [hn]
  · have hprod : 0 ≤ p.coeff n * p.leadingCoeff :=
      hsign n p.natDegree hn (leadingCoeff_ne_zero.mpr hp)
    nlinarith

/-- All nonzero coefficients the same sign ⇒ no positive real root.
Uses `eval` positivity on `(0, ∞)`. **Not** labelled Descartes.
`p ≠ 0` is load-bearing (the zero polynomial is a root everywhere). -/
theorem same_sign_coeff_no_positive_root {p : ℝ[X]} (hp : p ≠ 0)
    (hsign : ∀ i j, p.coeff i ≠ 0 → p.coeff j ≠ 0 → 0 ≤ p.coeff i * p.coeff j)
    {x : ℝ} (hx : 0 < x) : ¬ IsRoot p x := by
  intro hx0
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rcases lt_trichotomy 0 p.leadingCoeff with hpos | hzero | hneg
  · have := eval_pos_of_nonneg_coeff hp
        (coeff_nonneg_of_same_sign_pos_leading hp hsign hpos) hx
    rw [IsRoot.def] at hx0
    exact this.ne' hx0
  · exact hlc hzero.symm
  · have := eval_neg_of_nonpos_coeff hp
        (coeff_nonpos_of_same_sign_neg_leading hp hsign hneg) hx
    rw [IsRoot.def] at hx0
    exact this.ne hx0

/-- Zero sign-changes ⇒ no positive real root. Glue: `signChanges = 0` iff
same-sign (on nonzero coefficients). **Not** labelled Descartes. -/
theorem no_positive_root_of_signChanges_eq_zero {p : ℝ[X]} (hp : p ≠ 0)
    (hV : signChanges p = 0) {x : ℝ} (hx : 0 < x) : ¬ IsRoot p x :=
  same_sign_coeff_no_positive_root hp (same_sign_of_signChanges_eq_zero hV) hx

end ProofLab.Descartes
