/-
Schwartz–Zippel — Level A only (n=1 / constants / card_roots' glue).
**Not labelled Schwartz–Zippel.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `MvPolynomial.eval` / `totalDegree` / `degreeOf` /
`finSuccEquiv` / `Polynomial.card_roots'` and ZERO named Schwartz–Zippel
/ Zippel lemma. Completing the Level A n=1 / constants / card_roots'
glue is the gap this ticket lands. The Level B namesake
`schwartz_zippel` (multivariate induction on `n` via `finSuccEquiv`;
zeros in `S^n` ≤ `totalDegree * |S|^{n-1}`) is **out of this ticket**
and is **not** sorry-ed. Alon–Füredi / PIT / non-domain versions are
residual.

Pin: `catalog/problems/schwartz-zippel/STATEMENT.md` (OPE-1115; Scout
OPE-1110 prime; Director OPE-1114). Encoding: Mathlib `eval` /
`totalDegree` / `Finset`. Zero `sorry`. Do not import `Archive.*`.

This is **not** combinatorial Nullstellensatz
(`ProofLab/CombinatorialNullstellensatz.lean`
`combinatorial_nullstellensatz`, PR #71) — leading-monomial
nonvanishing on a box, per-variable `degreeOf`; **USE MvPolynomial
encoding**, **do not re-prove `combinatorial_nullstellensatz`**, do
not revive CNS. This is **not** Chevalley–Warning (already Mathlib
`FieldTheory/ChevalleyWarning.lean` `char_dvd_card_solutions`). This
is **not** Alon–Füredi / PIT / Schwartz–Zippel over non-domains.
This is **not** hadamard-det (the leftover). This is **not** Ore
Level B / `konig_edge_chromatic` / AES Level B / ostrowski-q Level B
/ frobenius-real-division Level B / noether-normalization Level B /
krenn-gu / hou-zeng-pfc / sun-135. Do not re-prime the consumed mill.
Leave OPE-403 alone.

v1 is the finite-box counting form over a field, `n ≥ 1` only.
**Do not label any theorem Schwartz–Zippel.** `1 ≤ n` is load-bearing
(`n = 0` is constants; `Nat` power `S.card ^ (n-1)` is the wrong
shape). `f ≠ 0` is load-bearing (the zero polynomial vanishes
everywhere). `totalDegree` is load-bearing (CNS used per-variable
`degreeOf` — do **not** swap). `Field F` is load-bearing
(`card_roots'` needs an integral domain). `DecidableEq F` is
load-bearing for `Finset` membership.

Level A: `n = 1` is a univariate polynomial. The `Finset` of roots in
`S` injects into `p.roots` (forgetting multiplicity), and
`card_roots'` gives `≤ natDegree ≤ totalDegree`. A nonzero constant
(`totalDegree = 0`) never vanishes. **Not** labelled Schwartz–Zippel.

Transcribed classical argument (DeMillo–Lipton 1978 / Zippel 1979 /
Schwartz, J. ACM 27 (1980) 701–717). Compact form: Wikipedia
*Schwartz–Zippel lemma*. Combinatorial Nullstellensatz and
Chevalley–Warning are different (consumed / already-in) theorems, not
this claim.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

open MvPolynomial Finset

noncomputable section
open Classical

namespace ProofLab.SchwartzZippel

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Level A: univariate `card_roots'` glue (not labelled Schwartz–Zippel) -/

/-- The `Finset` of roots of a nonzero univariate `p` inside `S` injects
into `p.roots` (forgetting multiplicity), so its card is `≤ natDegree`
via Mathlib `Polynomial.card_roots'`. Glue; **not** labelled
Schwartz–Zippel. -/
theorem card_roots_in_le_natDegree (p : Polynomial F) (hp : p ≠ 0) (S : Finset F) :
    (S.filter (fun a => p.eval a = 0)).card ≤ p.natDegree := by
  have hsub : S.filter (fun a => p.eval a = 0) ⊆ p.roots.toFinset := by
    intro a ha
    rw [mem_filter] at ha
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ha.2)
  refine (card_le_card hsub).trans ?_
  exact (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

/-! ## Level A: nonzero constants never vanish (not labelled Schwartz–Zippel) -/

/-- A nonzero constant polynomial never vanishes. Glue; **not** labelled
Schwartz–Zippel. -/
theorem eval_C_ne_zero {σ : Type*} {c : F} (hc : c ≠ 0) (x : σ → F) :
    eval x (C c : MvPolynomial σ F) ≠ 0 := by
  simpa [eval_C] using hc

/-- `totalDegree = 0` means every monomial in the support is `0`, so `f`
is the constant `C (coeff 0)`. Glue. -/
theorem eq_C_of_totalDegree_eq_zero {σ : Type*} [DecidableEq σ]
    (f : MvPolynomial σ F) (hdeg : f.totalDegree = 0) :
    f = C (f.coeff 0) := by
  ext m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_C]
  · have hm0 : coeff m f = 0 := by
      by_contra hne
      have hmem : m ∈ f.support := mem_support_iff.mpr hne
      have hle : m.sum (fun _ e => e) ≤ 0 := by
        rw [← hdeg]
        exact le_totalDegree hmem
      have : m = 0 := by
        ext i
        by_contra hi
        have hisup : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
        have hmi : m i ≤ m.sum (fun _ e => e) :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hisup
        have : 0 < m i := Nat.pos_of_ne_zero hi
        omega
      exact hm this
    rw [hm0, coeff_C, if_neg (Ne.symm hm)]

/-- A nonzero polynomial of `totalDegree = 0` is a nonzero constant, so
it never vanishes. Glue; **not** labelled Schwartz–Zippel. -/
theorem eval_ne_zero_of_totalDegree_eq_zero {σ : Type*} [DecidableEq σ]
    (f : MvPolynomial σ F) (hf : f ≠ 0) (hdeg : f.totalDegree = 0) (x : σ → F) :
    eval x f ≠ 0 := by
  have hfC : f = C (f.coeff 0) := eq_C_of_totalDegree_eq_zero f hdeg
  have hc : f.coeff 0 ≠ 0 := by
    intro h0
    apply hf
    rw [hfC, h0, map_zero]
  rw [hfC]
  exact eval_C_ne_zero hc x

/-! ## Level A: `n = 1` via `finSuccEquiv` (not labelled Schwartz–Zippel) -/

/-- Identify `MvPolynomial (Fin 1) F` with `Polynomial F` by peeling the
unique variable via `finSuccEquiv` and evaluating the empty tail.
Encoding glue; **not** labelled Schwartz–Zippel. -/
def toUnivariate (f : MvPolynomial (Fin 1) F) : Polynomial F :=
  Polynomial.map (eval (isEmptyElim : Fin 0 → F)) (MvPolynomial.finSuccEquiv F 0 f)

theorem eval_eq_toUnivariate_eval (f : MvPolynomial (Fin 1) F) (a : F) :
    eval (fun _ : Fin 1 => a) f = (toUnivariate f).eval a := by
  have hfun : (fun _ : Fin 1 => a) = Fin.cons a (isEmptyElim : Fin 0 → F) := by
    ext i
    rw [Fin.eq_zero i, Fin.cons_zero]
  rw [hfun, toUnivariate, eval_eq_eval_mv_eval']

theorem eval_empty_injective :
    Function.Injective (eval (isEmptyElim : Fin 0 → F)) := by
  intro p q h
  have hp : p = C (p.coeff 0) := eq_C_of_isEmpty p
  have hq : q = C (q.coeff 0) := eq_C_of_isEmpty q
  rw [hp, eval_C] at h
  rw [hq, eval_C] at h
  rw [hp, hq, h]

theorem toUnivariate_ne_zero {f : MvPolynomial (Fin 1) F} (hf : f ≠ 0) :
    toUnivariate f ≠ 0 := by
  intro h
  have hmap :
      Polynomial.map (eval (isEmptyElim : Fin 0 → F)) (MvPolynomial.finSuccEquiv F 0 f) =
        Polynomial.map (eval (isEmptyElim : Fin 0 → F)) 0 := by
    rw [toUnivariate] at h
    rw [h, Polynomial.map_zero]
  have : MvPolynomial.finSuccEquiv F 0 f = 0 :=
    Polynomial.map_injective (eval (isEmptyElim : Fin 0 → F)) eval_empty_injective hmap
  have hf0 : f = 0 := by
    apply (MvPolynomial.finSuccEquiv F 0).injective
    rw [this, map_zero]
  exact hf hf0

theorem toUnivariate_natDegree_le_totalDegree (f : MvPolynomial (Fin 1) F) :
    (toUnivariate f).natDegree ≤ f.totalDegree := by
  calc (toUnivariate f).natDegree
      ≤ (MvPolynomial.finSuccEquiv F 0 f).natDegree := by
          unfold toUnivariate
          exact Polynomial.natDegree_map_le
            (f := eval (isEmptyElim : Fin 0 → F)) (MvPolynomial.finSuccEquiv F 0 f)
    _ = f.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv f
    _ ≤ f.totalDegree := degreeOf_le_totalDegree f 0

/-- `n = 1`: zeros of a nonzero `f ∈ F[x]` inside `S` have card
`≤ totalDegree`. Identify with `Polynomial` via `finSuccEquiv`; apply
`card_roots'`. Glue; **not** labelled Schwartz–Zippel. -/
theorem card_zeros_fin_one_le_totalDegree
    (f : MvPolynomial (Fin 1) F) (hf : f ≠ 0) (S : Finset F) :
    (S.filter (fun a => eval (fun _ : Fin 1 => a) f = 0)).card ≤ f.totalDegree := by
  have hp : toUnivariate f ≠ 0 := toUnivariate_ne_zero hf
  have hfilter :
      S.filter (fun a => eval (fun _ : Fin 1 => a) f = 0) =
        S.filter (fun a => (toUnivariate f).eval a = 0) := by
    refine filter_congr fun a _ => ?_
    simp [eval_eq_toUnivariate_eval]
  rw [hfilter]
  exact (card_roots_in_le_natDegree (toUnivariate f) hp S).trans
    (toUnivariate_natDegree_le_totalDegree f)

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
  theorem schwartz_zippel
      {n : ℕ} (hn : 1 ≤ n)
      (f : MvPolynomial (Fin n) F) (hf : f ≠ 0) (S : Finset F) :
      ((Fintype.piFinset fun _ : Fin n => S).filter
          (fun x => eval x f = 0)).card
        ≤ f.totalDegree * S.card ^ (n - 1)
Induction on `n` via `finSuccEquiv`: write `f` as a polynomial in the
last variable; for each tail in `S^{n-1}` either the leading coefficient
vanishes (IH) or the univariate in the last variable has at most `deg`
roots in `S`. Do not sorry the namesake. Alon–Füredi / PIT / non-domain
versions remain residual. Do not re-prove `combinatorial_nullstellensatz`
/ `char_dvd_card_solutions`.
-/

end ProofLab.SchwartzZippel
