/-
Mason–Stothers theorem (polynomial ABC), formalize-only.

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `Polynomial.wronskian` / `wronskian_eq_of_sum_zero` /
`degree_wronskian_lt_add` / `natDegree_wronskian_lt_add`
(`RingTheory/Polynomial/Wronskian.lean`, Baek–Lee 2024) as **infra**.
ZERO named Mason–Stothers / polynomial ABC / `n₀(abc)` bound under
`Mathlib/` or `Archive/`. Completing the affine `max deg + 1 ≤ n₀(abc)`
is the gap. Do **not** import `Archive.*`.

Pin: `catalog/problems/mason-stothers/STATEMENT.md` (OPE-876; Scout
OPE-870 recommended prime; Director OPE-875). Encoding:
`Polynomial.roots.toFinset.card` for `n₀`, Mathlib `wronskian` as the
engine. Zero `sorry`. Do not import `Archive.*`.

This is **not** integer abc (open — refuse).
This is **not** number-theoretic FLT (Wiedijk 33).
This is **not** Descartes rule of signs (consumed #91 — coeff sign
changes, a different theorem).
This is **not** Sturm / Budan–Fourier / Gauss–Lucas / Niven cosine.
This is **not** combinatorial Nullstellensatz (consumed #71) /
Schwartz–Zippel / Alon–Füredi.
This is **not** Zsigmondy / Bang / LTE / Artin (consumed #95).
This is **not** erdos-ramsey-lower (consumed #94).
This is **not** expander-mixing (OPE-870 leftover, unassigned).
Do **not** re-prove `wronskian` / `wronskian_eq_of_sum_zero` /
`degree_wronskian_lt_add` / `Separable` / Eisenstein / FTA.
Leave OPE-403 alone.

v1 is the affine inequality over an algebraically closed field of
characteristic zero. Prefer `+ 1 ≤ n₀` so ℕ subtraction is not
load-bearing. `CharZero`, `IsAlgClosed`, `IsCoprime a b`, and
not-both-constant are load-bearing (all-constant counterexample:
`1+1=2`, `n₀=0`).

Level A `wronskian_ne_zero_of_coprime` is **not** labelled Mason:
coprime not-both-constant polynomials have nonzero Wronskian.
Glue: `wronskian_eq_of_add` via already-upstream
`wronskian_add_right` / `wronskian_self_eq_zero`.
Level B namesake `mason_stothers` is Snyder AMM 2000 multiplicity
counting: `(X − r)^{m_r−1}` divides `W` at each root of `abc`, so
`deg W + 1 ≤ n₀(abc)` together with `deg W < deg a + deg b`.

Transcribed classical argument (Stothers Quart. J. Math. 1981;
Mason LMS 96 1984; Snyder Amer. Math. Monthly 107 (2000)).
No novelty claim. Default no claim.
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Polynomial Finset
open scoped Classical Polynomial

noncomputable section

namespace ProofLab.MasonStothers

variable {k : Type*} [Field k]

/-! ## Pin (match STATEMENT.md exactly) -/

/-- `n₀(f)` = number of distinct roots. Over an algebraically closed
field this enumerates all geometric roots. -/
def distinctRootCount (f : k[X]) : ℕ := f.roots.toFinset.card

/-! ## Level A: Wronskian of a coprime not-both-constant pair is
nonzero. **Not** labelled Mason. -/

/-- If `a` divides `a'` in characteristic zero, then `a` is constant. -/
lemma natDegree_eq_zero_of_dvd_derivative [CharZero k] {a : k[X]}
    (ha0 : a ≠ 0) (hdvd : a ∣ derivative a) : a.natDegree = 0 := by
  obtain ⟨q, hq⟩ := hdvd
  by_cases hq0 : q = 0
  · have : derivative a = 0 := by rw [hq, hq0, mul_zero]
    exact natDegree_eq_zero_of_derivative_eq_zero this
  · have hdeg : (derivative a).natDegree = a.natDegree + q.natDegree := by
      rw [hq, natDegree_mul ha0 hq0]
    by_contra hpos
    have hlt : (derivative a).natDegree < a.natDegree :=
      natDegree_derivative_lt hpos
    have : a.natDegree < a.natDegree := by
      have : a.natDegree ≤ (derivative a).natDegree := by
        rw [hdeg]; exact Nat.le_add_right _ _
      exact lt_of_le_of_lt this hlt
    exact (lt_irrefl _) this

/-- Level A. **Not** labelled Mason. Uses Mathlib `wronskian`; does
not re-prove the degree bound. -/
theorem wronskian_ne_zero_of_coprime [CharZero k] {a b : k[X]}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hcop : IsCoprime a b)
    (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0) :
    wronskian a b ≠ 0 := by
  intro hw
  have hmul : a * derivative b = derivative a * b := by
    have : a * derivative b - derivative a * b = 0 := hw
    exact sub_eq_zero.mp this
  have hdvd : a ∣ derivative a :=
    hcop.dvd_of_dvd_mul_right (by rw [← hmul]; exact dvd_mul_right _ _)
  have ha_const : a.natDegree = 0 :=
    natDegree_eq_zero_of_dvd_derivative ha0 hdvd
  have hb_pos : b.natDegree ≠ 0 :=
    hnonconst.resolve_left (fun h => h ha_const)
  have ha' : derivative a = 0 := derivative_of_natDegree_zero ha_const
  have : a * derivative b = 0 := by rw [hmul, ha', zero_mul]
  have hb' : derivative b = 0 :=
    (mul_eq_zero.mp this).resolve_left ha0
  have : b.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hb'
  exact hb_pos this

/-- Glue, not namesake. `W(a,b) = W(a,c) = −W(b,c)` when `a + b = c`.
Uses already-upstream bilinearity; does not re-prove Wronskian degree. -/
lemma wronskian_eq_of_add {a b c : k[X]} (hsum : a + b = c) :
    wronskian a b = wronskian a c ∧ wronskian a b = -wronskian b c := by
  constructor
  · have : wronskian a c = wronskian a (a + b) := by rw [hsum]
    rw [this, wronskian_add_right, wronskian_self_eq_zero, zero_add]
  · have : wronskian b c = wronskian b (a + b) := by rw [hsum]
    rw [this, wronskian_add_right, wronskian_self_eq_zero, add_zero,
      ← wronskian_neg_eq]

/-- Pairwise coprimeness of `{a,b,c}` from `IsCoprime a b` and `a+b=c`. -/
lemma isCoprime_of_add_left {a b c : k[X]} (hsum : a + b = c)
    (hcop : IsCoprime a b) : IsCoprime a c := by
  have := hcop.add_mul_left_right (1 : k[X])
  simpa [mul_one, add_comm, hsum] using this

lemma isCoprime_of_add_right {a b c : k[X]} (hsum : a + b = c)
    (hcop : IsCoprime a b) : IsCoprime b c := by
  have := hcop.symm.add_mul_left_right (1 : k[X])
  simpa [mul_one, add_comm, add_left_comm, hsum] using this

/-! ## Distinct-root arithmetic -/

lemma disjoint_roots_of_isCoprime {p q : k[X]} (h : IsCoprime p q)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    Disjoint p.roots.toFinset q.roots.toFinset := by
  rw [Finset.disjoint_left]
  intro r hrP hrQ
  have hpR : IsRoot p r := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hrP)
  have hqR : IsRoot q r := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hrQ)
  have : aeval r p ≠ 0 ∨ aeval r q ≠ 0 := aeval_ne_zero_of_isCoprime h r
  cases this with
  | inl hp0 => exact hp0 (by simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hpR)
  | inr hq0 => exact hq0 (by simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using hqR)

lemma card_roots_mul_of_coprime {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hcop : IsCoprime p q) :
    distinctRootCount (p * q) = distinctRootCount p + distinctRootCount q := by
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  simp only [distinctRootCount]
  rw [roots_mul hpq, Multiset.toFinset_add]
  exact Finset.card_union_of_disjoint (disjoint_roots_of_isCoprime hcop hp hq)

lemma card_roots_mul_three {a b c : k[X]}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c) :
    distinctRootCount (a * b * c) =
      distinctRootCount a + distinctRootCount b + distinctRootCount c := by
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hcop_ab_c : IsCoprime (a * b) c := hac.mul_left hbc
  rw [card_roots_mul_of_coprime hab0 hc0 hcop_ab_c,
    card_roots_mul_of_coprime ha0 hb0 hab, add_assoc]

lemma sum_count_eq_card {α : Type*} [DecidableEq α] (s : Multiset α) :
    s.toFinset.sum (fun x => s.count x) = Multiset.card s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.toFinset_cons, Multiset.card_cons]
    by_cases ha : a ∈ s.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      have hsum :
          (s.toFinset.sum fun x => (a ::ₘ s).count x) =
            s.toFinset.sum (fun x => s.count x) + 1 := by
        have hite :
            (s.toFinset.sum fun x => if x = a then 1 else 0) = 1 := by
          simp [Finset.sum_ite_eq, ha]
        calc
          (s.toFinset.sum fun x => (a ::ₘ s).count x)
            = s.toFinset.sum fun x => s.count x + if x = a then 1 else 0 := by
                refine Finset.sum_congr rfl fun x _ => ?_
                simp [Multiset.count_cons]
          _ = s.toFinset.sum (fun x => s.count x) +
                s.toFinset.sum fun x => if x = a then 1 else 0 :=
              Finset.sum_add_distrib
          _ = s.toFinset.sum (fun x => s.count x) + 1 := by rw [hite]
      rw [hsum, ih]
    · rw [Finset.sum_insert ha]
      have hnotin : a ∉ s := mt Multiset.mem_toFinset.mpr ha
      have hca : s.count a = 0 := Multiset.count_eq_zero.mpr hnotin
      have hleft : (a ::ₘ s).count a = 1 := by simp [Multiset.count_cons, hca]
      have hrest :
          (s.toFinset.sum fun x => (a ::ₘ s).count x) = Multiset.card s := by
        rw [← ih]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : x ≠ a := fun h => ha (h ▸ hx)
        simp [Multiset.count_cons, hne]
      rw [hleft, hrest, add_comm]

lemma sum_rootMultiplicity_eq_card_roots (f : k[X]) :
    f.roots.toFinset.sum (fun r => f.rootMultiplicity r) =
      Multiset.card f.roots := by
  classical
  simp_rw [← count_roots]
  exact sum_count_eq_card f.roots

lemma sum_rootMultiplicity_sub_one (f : k[X]) (hf : f ≠ 0) :
    f.roots.toFinset.sum (fun r => f.rootMultiplicity r - 1) +
        f.roots.toFinset.card =
      Multiset.card f.roots := by
  classical
  have hpos : ∀ r ∈ f.roots.toFinset, 1 ≤ f.rootMultiplicity r := by
    intro r hr
    have : 0 < f.rootMultiplicity r :=
      (rootMultiplicity_pos hf).2
        (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
    exact Nat.succ_le_of_lt this
  have hsum :
      f.roots.toFinset.sum (fun r => f.rootMultiplicity r - 1) +
          f.roots.toFinset.card =
        f.roots.toFinset.sum (fun r => f.rootMultiplicity r) := by
    have hcard : f.roots.toFinset.card =
        f.roots.toFinset.sum fun _ => 1 := by
      simp [Finset.sum_const]
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => Nat.sub_add_cancel (hpos r hr)
  rw [hsum, sum_rootMultiplicity_eq_card_roots]

lemma natDegree_eq_card_roots_of_algClosed [IsAlgClosed k] (f : k[X]) :
    f.natDegree = Multiset.card f.roots := by
  simpa [Polynomial.map_id] using
    (natDegree_eq_card_roots (i := RingHom.id k) (IsAlgClosed.splits f))

/-! ## Snyder multiplicity: `(X − r)^{m−1}` divides the Wronskian. -/

lemma pow_rootMultiplicity_sub_one_dvd_wronskian
    {a b : k[X]} (r : k) :
    (X - C r) ^ (a.rootMultiplicity r - 1) ∣ wronskian a b := by
  have ha : (X - C r) ^ (a.rootMultiplicity r - 1) ∣ a :=
    (pow_dvd_pow _ (Nat.sub_le _ _)).trans (pow_rootMultiplicity_dvd a r)
  have ha' : (X - C r) ^ (a.rootMultiplicity r - 1) ∣ derivative a :=
    pow_sub_one_dvd_derivative_of_pow_dvd (pow_rootMultiplicity_dvd a r)
  have h1 : (X - C r) ^ (a.rootMultiplicity r - 1) ∣ a * derivative b :=
    ha.mul_right _
  have h2 : (X - C r) ^ (a.rootMultiplicity r - 1) ∣ derivative a * b :=
    ha'.mul_right _
  simpa [wronskian] using dvd_sub h1 h2

lemma prod_X_sub_C_pow_dvd {s : Finset k} (m : k → ℕ) {w : k[X]} :
    (∀ r ∈ s, (X - C r) ^ m r ∣ w) →
      (∏ r ∈ s, (X - C r) ^ m r) ∣ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro; simp
  · intro r s hr ih h
    rw [Finset.prod_insert hr]
    have hcop :
        IsCoprime ((X - C r) ^ m r) (∏ x ∈ s, (X - C x) ^ m x) := by
      refine IsCoprime.prod_right fun x hx => ?_
      have hne : r ≠ x := fun e => hr (e ▸ hx)
      exact (isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr hne).isUnit).pow
    exact hcop.mul_dvd (h r (mem_insert_self _ _))
      (ih fun x hx => h x (mem_insert_of_mem hx))

/-- Squareful kernel of `f`: `∏ (X − r)^{m_r − 1}` over distinct roots. -/
def squarefulPart (f : k[X]) : k[X] :=
  ∏ r ∈ f.roots.toFinset, (X - C r) ^ (f.rootMultiplicity r - 1)

lemma squarefulPart_dvd_wronskian_left {a b : k[X]} :
    squarefulPart a ∣ wronskian a b :=
  prod_X_sub_C_pow_dvd _ fun r _ =>
    pow_rootMultiplicity_sub_one_dvd_wronskian r

lemma squarefulPart_dvd_wronskian_right {a b : k[X]} :
    squarefulPart b ∣ wronskian a b := by
  have : squarefulPart b ∣ wronskian b a := squarefulPart_dvd_wronskian_left
  rw [← wronskian_neg_eq b a]
  exact dvd_neg.mpr this

lemma squarefulPart_monic_factors (f : k[X]) :
    ∀ r ∈ f.roots.toFinset,
      ((X - C r) ^ (f.rootMultiplicity r - 1)).Monic :=
  fun r _ => (monic_X_sub_C r).pow _

lemma natDegree_squarefulPart (f : k[X]) :
    (squarefulPart f).natDegree =
      f.roots.toFinset.sum fun r => f.rootMultiplicity r - 1 := by
  classical
  rw [squarefulPart,
    natDegree_prod_of_monic f.roots.toFinset
      (fun r => (X - C r) ^ (f.rootMultiplicity r - 1))
      (squarefulPart_monic_factors f)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(monic_X_sub_C r).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma natDegree_squarefulPart_eq [IsAlgClosed k] {f : k[X]} (hf : f ≠ 0) :
    (squarefulPart f).natDegree = f.natDegree - distinctRootCount f := by
  have hsum := sum_rootMultiplicity_sub_one f hf
  rw [natDegree_squarefulPart]
  unfold distinctRootCount
  rw [← natDegree_eq_card_roots_of_algClosed f] at hsum
  exact Nat.eq_sub_of_add_eq hsum

lemma squarefulPart_ne_zero (f : k[X]) : squarefulPart f ≠ 0 := by
  classical
  refine prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ ?_
  exact X_sub_C_ne_zero r

lemma isCoprime_squarefulPart {p q : k[X]} (h : IsCoprime p q)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    IsCoprime (squarefulPart p) (squarefulPart q) := by
  classical
  refine IsCoprime.prod_left fun r hr => IsCoprime.prod_right fun s hs => ?_
  by_cases hne : r = s
  · subst hne
    have : ¬ (r ∈ q.roots.toFinset) := by
      have hd := disjoint_roots_of_isCoprime h hp hq
      exact Finset.disjoint_left.mp hd hr
    exact (this hs).elim
  · exact (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hne).isUnit).pow

lemma squareful_three_dvd_wronskian {a b c : k[X]}
    (hsum : a + b = c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b) :
    squarefulPart a * squarefulPart b * squarefulPart c ∣ wronskian a b := by
  have hac := isCoprime_of_add_left hsum hab
  have hbc := isCoprime_of_add_right hsum hab
  have hWac : wronskian a b = wronskian a c := (wronskian_eq_of_add hsum).1
  have h1 : squarefulPart a ∣ wronskian a b :=
    squarefulPart_dvd_wronskian_left
  have h2 : squarefulPart b ∣ wronskian a b :=
    squarefulPart_dvd_wronskian_right
  have h3 : squarefulPart c ∣ wronskian a b := by
    have : squarefulPart c ∣ wronskian a c :=
      squarefulPart_dvd_wronskian_right (a := a) (b := c)
    rwa [← hWac] at this
  have habs : IsCoprime (squarefulPart a) (squarefulPart b) :=
    isCoprime_squarefulPart hab ha0 hb0
  have h12 : squarefulPart a * squarefulPart b ∣ wronskian a b :=
    habs.mul_dvd h1 h2
  have hcop_ab_c : IsCoprime (squarefulPart a * squarefulPart b)
      (squarefulPart c) :=
    (isCoprime_squarefulPart hac ha0 hc0).mul_left
      (isCoprime_squarefulPart hbc hb0 hc0)
  exact hcop_ab_c.mul_dvd h12 h3

lemma natDegree_squareful_three [IsAlgClosed k] {a b c : k[X]}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : IsCoprime a b) (hac : IsCoprime a c) (hbc : IsCoprime b c) :
    (squarefulPart a * squarefulPart b * squarefulPart c).natDegree =
      a.natDegree + b.natDegree + c.natDegree -
        distinctRootCount (a * b * c) := by
  have hne_ab : squarefulPart a * squarefulPart b ≠ 0 :=
    mul_ne_zero (squarefulPart_ne_zero _) (squarefulPart_ne_zero _)
  have hne : squarefulPart a * squarefulPart b * squarefulPart c ≠ 0 :=
    mul_ne_zero hne_ab (squarefulPart_ne_zero _)
  have hcop_ab : IsCoprime (squarefulPart a) (squarefulPart b) :=
    isCoprime_squarefulPart hab ha0 hb0
  rw [natDegree_mul hne_ab (squarefulPart_ne_zero _),
    natDegree_mul (squarefulPart_ne_zero _) (squarefulPart_ne_zero _),
    natDegree_squarefulPart_eq ha0, natDegree_squarefulPart_eq hb0,
    natDegree_squarefulPart_eq hc0, card_roots_mul_three ha0 hb0 hc0 hab hac hbc]
  have hle_a : distinctRootCount a ≤ a.natDegree := by
    unfold distinctRootCount
    rw [natDegree_eq_card_roots_of_algClosed a]
    exact Multiset.toFinset_card_le _
  have hle_b : distinctRootCount b ≤ b.natDegree := by
    unfold distinctRootCount
    rw [natDegree_eq_card_roots_of_algClosed b]
    exact Multiset.toFinset_card_le _
  have hle_c : distinctRootCount c ≤ c.natDegree := by
    unfold distinctRootCount
    rw [natDegree_eq_card_roots_of_algClosed c]
    exact Multiset.toFinset_card_le _
  rw [tsub_add_tsub_comm hle_a hle_b]
  exact tsub_add_tsub_comm (add_le_add hle_a hle_b) hle_c

/-! ## Level B namesake -/

/-- Mason–Stothers (polynomial ABC), affine form. Snyder Wronskian
counting. **No novelty claim.** Not integer abc. Not FLT. -/
theorem mason_stothers [CharZero k] [IsAlgClosed k] {a b c : k[X]}
    (hsum : a + b = c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hcop : IsCoprime a b)
    (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0) :
    max a.natDegree (max b.natDegree c.natDegree) + 1
      ≤ distinctRootCount (a * b * c) := by
  have hac := isCoprime_of_add_left hsum hcop
  have hbc := isCoprime_of_add_right hsum hcop
  have hw : wronskian a b ≠ 0 :=
    wronskian_ne_zero_of_coprime ha0 hb0 hcop hnonconst
  have hWac : wronskian a b = wronskian a c := (wronskian_eq_of_add hsum).1
  have hWbc : wronskian a b = -wronskian b c := (wronskian_eq_of_add hsum).2
  have hwac : wronskian a c ≠ 0 := by rwa [← hWac]
  have hwbc : wronskian b c ≠ 0 := by
    intro h; exact hw (by simp [hWbc, h])
  have hdvd :=
    squareful_three_dvd_wronskian hsum ha0 hb0 hc0 hcop
  have hdeg_prod :
      (squarefulPart a * squarefulPart b * squarefulPart c).natDegree
        ≤ (wronskian a b).natDegree :=
    natDegree_le_of_dvd hdvd hw
  have hdeg_eq :=
    natDegree_squareful_three ha0 hb0 hc0 hcop hac hbc
  have hWlt_ab : (wronskian a b).natDegree < a.natDegree + b.natDegree :=
    natDegree_wronskian_lt_add hw
  have hWlt_ac : (wronskian a b).natDegree < a.natDegree + c.natDegree := by
    have := natDegree_wronskian_lt_add hwac
    rwa [← hWac] at this
  have hWlt_bc : (wronskian a b).natDegree < b.natDegree + c.natDegree := by
    have := natDegree_wronskian_lt_add hwbc
    have hdeg : (wronskian b c).natDegree = (wronskian a b).natDegree := by
      rw [hWbc, natDegree_neg]
    rwa [hdeg] at this
  have hbound :
      a.natDegree + b.natDegree + c.natDegree - distinctRootCount (a * b * c)
        ≤ (wronskian a b).natDegree := by
    rwa [← hdeg_eq]
  have hle_n0 :
      distinctRootCount (a * b * c) ≤
        a.natDegree + b.natDegree + c.natDegree := by
    have hle_a : distinctRootCount a ≤ a.natDegree := by
      unfold distinctRootCount
      rw [natDegree_eq_card_roots_of_algClosed a]
      exact Multiset.toFinset_card_le _
    have hle_b : distinctRootCount b ≤ b.natDegree := by
      unfold distinctRootCount
      rw [natDegree_eq_card_roots_of_algClosed b]
      exact Multiset.toFinset_card_le _
    have hle_c : distinctRootCount c ≤ c.natDegree := by
      unfold distinctRootCount
      rw [natDegree_eq_card_roots_of_algClosed c]
      exact Multiset.toFinset_card_le _
    have hcard := card_roots_mul_three ha0 hb0 hc0 hcop hac hbc
    rw [hcard]
    exact add_le_add (add_le_add hle_a hle_b) hle_c
  -- deg a + deg b + deg c − n₀ ≤ deg W < deg a + deg b  ⇒  deg c + 1 ≤ n₀
  have hc_le : c.natDegree + 1 ≤ distinctRootCount (a * b * c) := by
    have : a.natDegree + b.natDegree + c.natDegree -
        distinctRootCount (a * b * c) < a.natDegree + b.natDegree :=
      lt_of_le_of_lt hbound hWlt_ab
    omega
  have ha_le : a.natDegree + 1 ≤ distinctRootCount (a * b * c) := by
    have : a.natDegree + b.natDegree + c.natDegree -
        distinctRootCount (a * b * c) < b.natDegree + c.natDegree :=
      lt_of_le_of_lt hbound hWlt_bc
    omega
  have hb_le : b.natDegree + 1 ≤ distinctRootCount (a * b * c) := by
    have : a.natDegree + b.natDegree + c.natDegree -
        distinctRootCount (a * b * c) < a.natDegree + c.natDegree :=
      lt_of_le_of_lt hbound hWlt_ac
    omega
  cases' le_total a.natDegree (max b.natDegree c.natDegree) with hAB hAB
  · rw [max_eq_right hAB]
    cases' le_total b.natDegree c.natDegree with hBC hBC
    · rw [max_eq_right hBC]; exact hc_le
    · rw [max_eq_left hBC]; exact hb_le
  · rw [max_eq_left hAB]; exact ha_le

end ProofLab.MasonStothers
