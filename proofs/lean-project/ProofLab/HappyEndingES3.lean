import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Tactic

/-!
# Happy Ending ES(3)=5 — OPE-403 plumbing + OPE-410 finish wave

**Literature:** Erdős–Szekeres 1935; Esther Klein. Formalize-only; **no novelty claim**.
**Pin:** `problems/happy-ending-es3/STATEMENT.md`

## Delivered (zero `sorry` / `admit` / custom `axiom`)

1. `orient` on `ℝ × ℝ` + swap/cycle/self identities + bary sum identity
2. `orient_affine3` — affine in the last slot
3. barycentric coordinates, sum-to-one, reconstruction
4. `mem_convexHull_triangle_of_bary_nonneg`
5. `not_mem_segment_of_orient`
6. `InConvexPosition4` (STATEMENT convex-position definition)
7. `IsHullVertex`, `exists_hull_vertex`, `hullVertices`
8. `convexIndependent_hull_vertices`
9. `es_three_eq_five_of_hull_card_ge_four` (hull ≥ 4 case)
10. `EsThreeEqFiveStatement` / `GeneralPosition` predicates (1:1 with STATEMENT)
11. **F1** `inConvexPosition4_iff_convexIndependent` (OPE-410)
12. `exists_hull_vertex_min` (lex-min dual; OPE-410 hull progress)

## Residual (OPE-410)

- `GP ∧ card≥3 ⇒ hull.card ≥ 3` (third vertex via max-orient / off-line)
- Triangle + 2-interior separating-line orientation bash
- Full `es_three_eq_five` discharging `EsThreeEqFiveStatement`

ES(4)=9 out of scope.
-/

namespace ProofLab.HappyEndingES3

open scoped BigOperators
open Classical
open Set Finset

abbrev P := ℝ × ℝ

/-! ## Orientation -/

def orient (a b c : P) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

lemma orient_swap_right (a b c : P) : orient a c b = -orient a b c := by
  unfold orient; ring

lemma orient_swap_left (a b c : P) : orient b a c = -orient a b c := by
  unfold orient; ring

lemma orient_cycle (a b c : P) : orient b c a = orient a b c := by
  unfold orient; ring

lemma orient_cycle' (a b c : P) : orient c a b = orient a b c := by
  unfold orient; ring

/-- `orient x b c = orient b c x`. -/
lemma orient_last_cycle (x b c : P) : orient x b c = orient b c x :=
  (orient_cycle x b c).symm

@[simp] lemma orient_self_left (a b : P) : orient a a b = 0 := by unfold orient; ring
@[simp] lemma orient_self_mid (a b : P) : orient a b a = 0 := by unfold orient; ring
@[simp] lemma orient_self_right (a b : P) : orient a b b = 0 := by unfold orient; ring

lemma orient_bary_sum (a b c x : P) :
    orient x b c + orient a x c + orient a b x = orient a b c := by
  unfold orient; ring

lemma orient_affine3 (p q : P) (wa wb wc : ℝ) (x y z : P) (hsum : wa + wb + wc = 1) :
    orient p q (wa • x + wb • y + wc • z) =
      wa * orient p q x + wb * orient p q y + wc * orient p q z := by
  unfold orient
  simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
  have hw : wa = 1 - wb - wc := by linarith
  rw [hw]
  ring

/-! ## Barycentric coordinates -/

noncomputable def baryA (a b c x : P) : ℝ := orient x b c / orient a b c
noncomputable def baryB (a b c x : P) : ℝ := orient a x c / orient a b c
noncomputable def baryC (a b c x : P) : ℝ := orient a b x / orient a b c

lemma bary_sum (a b c x : P) (h : orient a b c ≠ 0) :
    baryA a b c x + baryB a b c x + baryC a b c x = 1 := by
  simp only [baryA, baryB, baryC]
  field_simp [h]
  exact orient_bary_sum a b c x

lemma affine_combination_bary (a b c x : P) (h : orient a b c ≠ 0) :
    baryA a b c x • a + baryB a b c x • b + baryC a b c x • c = x := by
  apply Prod.ext
  · simp only [Prod.smul_fst, Prod.fst_add, baryA, baryB, baryC, smul_eq_mul]
    field_simp [h]; unfold orient; ring
  · simp only [Prod.smul_snd, Prod.snd_add, baryA, baryB, baryC, smul_eq_mul]
    field_simp [h]; unfold orient; ring

theorem mem_convexHull_triangle_of_bary_nonneg (a b c x : P) (h : orient a b c ≠ 0)
    (ha : 0 ≤ baryA a b c x) (hb : 0 ≤ baryB a b c x) (hc : 0 ≤ baryC a b c x) :
    x ∈ convexHull ℝ ({a, b, c} : Set P) := by
  let w : Fin 3 → ℝ := ![baryA a b c x, baryB a b c x, baryC a b c x]
  let z : Fin 3 → P := ![a, b, c]
  have hw₀ : ∀ i, 0 ≤ w i := by
    intro i; fin_cases i
    · simpa [w] using ha
    · simpa [w] using hb
    · simpa [w] using hc
  have hw₁ : ∑ i : Fin 3, w i = 1 := by
    simpa [w, Fin.sum_univ_three] using bary_sum a b c x h
  have hz : ∀ i, z i ∈ ({a, b, c} : Set P) := by
    intro i; fin_cases i <;> simp [z]
  have hx : ∑ i : Fin 3, w i • z i = x := by
    simpa [w, z, Fin.sum_univ_three] using affine_combination_bary a b c x h
  exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

lemma bary_of_affine3 (a b c : P) (h : orient a b c ≠ 0) (wa wb wc : ℝ)
    (hsum : wa + wb + wc = 1) (x : P) (hx : x = wa • a + wb • b + wc • c) :
    baryA a b c x = wa ∧ baryB a b c x = wb ∧ baryC a b c x = wc := by
  have hA : orient x b c = wa * orient a b c := by
    rw [orient_last_cycle, hx, orient_affine3 b c wa wb wc a b c hsum]
    simp [orient_cycle]
  have hB : orient a x c = wb * orient a b c := by
    have hcombo := orient_affine3 a c wa wb wc a b c hsum
    have hxac : orient a c x = wb * orient a c b := by
      rw [hx, hcombo]
      simp [orient_self_left, orient_self_right]
    calc
      orient a x c = -orient a c x := by rw [orient_swap_right]
      _ = -(wb * orient a c b) := by rw [hxac]
      _ = -(wb * (-orient a b c)) := by rw [orient_swap_right]
      _ = wb * orient a b c := by ring
  have hC : orient a b x = wc * orient a b c := by
    rw [hx, orient_affine3 a b wa wb wc a b c hsum]
    simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [baryA]; field_simp [h]; exact hA
  · simp only [baryB]; field_simp [h]; exact hB
  · simp only [baryC]; field_simp [h]; exact hC

theorem not_mem_segment_of_orient (a b c : P) (h : orient a b c ≠ 0) :
    a ∉ convexHull ℝ ({b, c} : Set P) := by
  intro ha
  by_cases hbc : b = c
  · subst hbc
    have : a ∈ ({b} : Set P) := by rwa [convexHull_pair, segment_same] at ha
    have hab : a = b := by simpa using this
    subst hab
    exact h (by simp)
  · have ha' : a ∈ convexHull ℝ (({b, c} : Finset P) : Set P) := by
      have : (({b, c} : Finset P) : Set P) = {b, c} := by ext; simp
      rwa [this]
    obtain ⟨w, _hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp ha'
    have hsum : w b + w c = 1 := by rw [← hw1]; simp [hbc]
    have hmass' : a = w b • b + w c • c := by rw [← hmass]; simp [hbc, add_comm]
    have hx : a = (0 : ℝ) • a + w b • b + w c • c := by
      simp [hmass']
    have hs : (0 : ℝ) + w b + w c = 1 := by simpa using hsum
    obtain ⟨hA, _, _⟩ := bary_of_affine3 a b c h 0 (w b) (w c) hs a hx
    have h1 : baryA a b c a = 1 := by simp only [baryA]; field_simp [h]
    exact absurd (h1.symm.trans hA) one_ne_zero

/-! ## Convex position (STATEMENT) -/

/-- None of the four lies in the convex hull of the other three. -/
def InConvexPosition4 (a b c d : P) : Prop :=
  a ∉ convexHull ℝ ({b, c, d} : Set P) ∧
  b ∉ convexHull ℝ ({a, c, d} : Set P) ∧
  c ∉ convexHull ℝ ({a, b, d} : Set P) ∧
  d ∉ convexHull ℝ ({a, b, c} : Set P)

/-! ## Hull vertices -/

def IsHullVertex (s : Finset P) (p : P) : Prop :=
  p ∈ s ∧ p ∉ convexHull ℝ ((s : Set P) \ {p})

lemma erase_coe (s : Finset P) (p : P) :
    ((s : Set P) \ {p}) = ↑(s.erase p) := by
  ext x; simp [and_comm]

lemma weighted_eq_of_sum_eq {s : Finset P} (w f g : P → ℝ)
    (hle : ∀ y ∈ s, w y * f y ≤ w y * g y)
    (heq : ∑ y ∈ s, w y * f y = ∑ y ∈ s, w y * g y) :
    ∀ y ∈ s, w y * f y = w y * g y := by
  intro y hy
  have hsub : ∑ t ∈ s, (w t * g t - w t * f t) = 0 := by
    simp [sum_sub_distrib, heq]
  have hnn : ∀ t ∈ s, 0 ≤ w t * g t - w t * f t := by
    intro t ht; linarith [hle t ht]
  have h0 := (sum_eq_zero_iff_of_nonneg hnn).1 hsub y hy
  linarith

theorem exists_hull_vertex (s : Finset P) (hs : s.Nonempty) :
    ∃ p, IsHullVertex s p := by
  obtain ⟨p₀, hp₀, hmax0⟩ := s.exists_max_image (fun p : P => p.1) hs
  let s2 : Finset P := s.filter (fun q => q.1 = p₀.1)
  have hs2 : s2.Nonempty := ⟨p₀, by simp [s2, hp₀]⟩
  obtain ⟨q, hq, hmax1⟩ := s2.exists_max_image (fun p : P => p.2) hs2
  have hq_s : q ∈ s := (mem_filter.mp hq).1
  have hq1 : q.1 = p₀.1 := (mem_filter.mp hq).2
  refine ⟨q, hq_s, ?_⟩
  intro hconv
  rw [erase_coe] at hconv
  obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
  have hfst : q.1 = ∑ y ∈ s.erase q, w y * y.1 := by
    have := congr_arg Prod.fst hmass
    simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using this.symm
  have hsnd : q.2 = ∑ y ∈ s.erase q, w y * y.2 := by
    have := congr_arg Prod.snd hmass
    simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using this.symm
  have hy1_le : ∀ y ∈ s.erase q, y.1 ≤ q.1 := by
    intro y hy
    have := hmax0 y (mem_of_mem_erase hy)
    linarith [hq1]
  have hle1 : ∀ y ∈ s.erase q, w y * y.1 ≤ w y * q.1 := fun y hy =>
    mul_le_mul_of_nonneg_left (hy1_le y hy) (hw0 y hy)
  have hrhs1 : ∑ y ∈ s.erase q, w y * q.1 = q.1 := by simp [← sum_mul, hw1]
  have heq1 : ∑ y ∈ s.erase q, w y * y.1 = ∑ y ∈ s.erase q, w y * q.1 := by
    linarith [hfst, hrhs1]
  have hpair1 := weighted_eq_of_sum_eq w (fun y => y.1) (fun _ => q.1) hle1 heq1
  have hy1_eq : ∀ y ∈ s.erase q, w y ≠ 0 → y.1 = q.1 := by
    intro y hy hwne
    exact mul_left_cancel₀ hwne (by linarith [hpair1 y hy])
  have hle2 : ∀ y ∈ s.erase q, w y * y.2 ≤ w y * q.2 := by
    intro y hy
    by_cases hwne : w y = 0
    · simp [hwne]
    · have hy1eq := hy1_eq y hy hwne
      have y_in_s2 : y ∈ s2 := by
        simp only [s2, mem_filter, mem_of_mem_erase hy, true_and]
        linarith [hq1, hy1eq]
      exact mul_le_mul_of_nonneg_left (hmax1 y y_in_s2) (hw0 y hy)
  have hrhs2 : ∑ y ∈ s.erase q, w y * q.2 = q.2 := by simp [← sum_mul, hw1]
  have heq2 : ∑ y ∈ s.erase q, w y * y.2 = ∑ y ∈ s.erase q, w y * q.2 := by
    linarith [hsnd, hrhs2]
  have hpair2 := weighted_eq_of_sum_eq w (fun y => y.2) (fun _ => q.2) hle2 heq2
  have hy_eq : ∀ y ∈ s.erase q, w y ≠ 0 → y = q := by
    intro y hy hwne
    apply Prod.ext
    · exact hy1_eq y hy hwne
    · exact mul_left_cancel₀ hwne (by linarith [hpair2 y hy])
  obtain ⟨y, hy, hypos⟩ : ∃ y ∈ s.erase q, 0 < w y := by
    by_contra H
    push_neg at H
    have hz : ∀ y ∈ s.erase q, w y = 0 := fun y hy => le_antisymm (H y hy) (hw0 y hy)
    have : ∑ y ∈ s.erase q, w y = 0 := sum_eq_zero hz
    linarith [hw1]
  have yeq := hy_eq y hy (ne_of_gt hypos)
  have hy' := hy
  rw [yeq] at hy'
  exact absurd hy' (not_mem_erase q s)

theorem convexIndependent_hull_vertices (s : Finset P) (t : Set P)
    (ht : t ⊆ (s : Set P)) (hhull : ∀ p ∈ t, IsHullVertex s p) :
    ConvexIndependent ℝ ((↑) : t → P) := by
  rw [convexIndependent_set_iff_not_mem_convexHull_diff]
  intro x hx hconv
  have hV := hhull x hx
  have mono : t \ {x} ⊆ (s : Set P) \ {x} := by
    intro y hy; exact ⟨ht hy.1, hy.2⟩
  exact hV.2 (convexHull_mono mono hconv)

/-! ## Statement predicates -/

def GeneralPosition (s : Finset P) : Prop :=
  ∀ ⦃x y z : P⦄, x ∈ s → y ∈ s → z ∈ s → x ≠ y → y ≠ z → x ≠ z → orient x y z ≠ 0

def EsThreeEqFiveStatement : Prop :=
  ∀ s : Finset P, s.card = 5 → GeneralPosition s →
    ∃ t : Finset P, t ⊆ s ∧ t.card = 4 ∧
      ConvexIndependent ℝ (fun x : (↑t : Set P) => (x : P))

noncomputable def hullVertices (s : Finset P) : Finset P :=
  s.filter fun p => (p ∉ convexHull ℝ ((s : Set P) \ {p}))

lemma mem_hullVertices {s : Finset P} {p : P} :
    p ∈ hullVertices s ↔ IsHullVertex s p := by
  constructor
  · intro h
    refine ⟨mem_filter.mp h |>.1, mem_filter.mp h |>.2⟩
  · intro h
    exact mem_filter.mpr ⟨h.1, h.2⟩

lemma hullVertices_subset (s : Finset P) : (hullVertices s : Set P) ⊆ (s : Set P) := by
  intro p hp
  exact (mem_hullVertices.mp (by exact hp)).1

theorem hullVertices_nonempty (s : Finset P) (hs : s.Nonempty) :
    (hullVertices s).Nonempty := by
  obtain ⟨p, hp⟩ := exists_hull_vertex s hs
  exact ⟨p, mem_hullVertices.mpr hp⟩

/-- Partial ES(3)=5: ≥ 4 hull vertices ⇒ convex 4-subset. -/
theorem es_three_eq_five_of_hull_card_ge_four (s : Finset P)
    (_hcard : s.card = 5) (_hgp : GeneralPosition s)
    (hH : 4 ≤ (hullVertices s).card) :
    ∃ t : Finset P, t ⊆ s ∧ t.card = 4 ∧
      ConvexIndependent ℝ (fun x : (↑t : Set P) => (x : P)) := by
  obtain ⟨t, htH, ht4⟩ := exists_subset_card_eq hH
  refine ⟨t, ?_, ht4, ?_⟩
  · intro x hx; exact (mem_hullVertices.mp (htH hx)).1
  · have ht_set : (↑t : Set P) ⊆ (↑s : Set P) := by
      intro x hx; exact (mem_hullVertices.mp (htH hx)).1
    have hh : ∀ p ∈ (↑t : Set P), IsHullVertex s p := by
      intro p hp; exact mem_hullVertices.mp (htH hp)
    exact convexIndependent_hull_vertices s (↑t) ht_set hh

/-! ## F1: InConvexPosition4 ↔ ConvexIndependent (OPE-410 / review finding F1) -/

lemma card_at_most_three (x y z : P) : ({x, y, z} : Finset P).card ≤ 3 := by
  calc
    ({x, y, z} : Finset P).card ≤ ({y, z} : Finset P).card + 1 := Finset.card_insert_le _ _
    _ ≤ ({z} : Finset P).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ ≤ 1 + 1 + 1 := by
        have : ({z} : Finset P).card = 1 := Finset.card_singleton z
        linarith
    _ = 3 := by norm_num

lemma ne_four_of_card_le_three {s : Finset P} (h : s.card ≤ 3) : s.card ≠ 4 := by omega

lemma pairwise_of_card4 {a b c d : P}
    (h : ({a, b, c, d} : Finset P).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  -- Collision of any pair collapses the literal 4-set to a triple (card ≤ 3).
  have collapse4 {u v w : P} (heqS : ({a, b, c, d} : Finset P) = ({u, v, w} : Finset P)) :
      False :=
    ne_four_of_card_le_three (card_at_most_three u v w) (heqS ▸ h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact collapse4 (by simp [heq, Finset.insert_eq_of_mem] : ({a, b, c, d} : Finset P) = ({a, c, d} : Finset P))
  · intro heq
    apply collapse4 (u := a) (v := b) (w := d)
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, heq]
    constructor <;> intro hmem <;> aesop
  · intro heq
    apply collapse4 (u := a) (v := b) (w := c)
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, heq]
    constructor <;> intro hmem <;> aesop
  · intro heq
    apply collapse4 (u := a) (v := b) (w := d)
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, heq]
    constructor <;> intro hmem <;> aesop
  · intro heq
    apply collapse4 (u := a) (v := b) (w := c)
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, heq]
    constructor <;> intro hmem <;> aesop
  · intro heq
    apply collapse4 (u := a) (v := b) (w := c)
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, heq]
    constructor <;> intro hmem <;> aesop

private lemma mem_finset4 {a b c d x : P} :
    x ∈ ({a, b, c, d} : Finset P) ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by simp

lemma coe_set4_diff_a {a b c d : P} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    ((({a, b, c, d} : Finset P) : Set P) \ {a}) = ({b, c, d} : Set P) := by
  ext x; constructor
  · intro hx
    have : x = a ∨ x = b ∨ x = c ∨ x = d := (mem_finset4).1 hx.1
    rcases this with rfl | rfl | rfl | rfl
    · exact (hx.2 rfl).elim
    · simp
    · simp
    · simp
  · intro hx
    rcases (show x = b ∨ x = c ∨ x = d by simpa using hx) with rfl | rfl | rfl
    · exact ⟨by simp [mem_finset4, hab.symm], hab.symm⟩
    · exact ⟨by simp [mem_finset4, hac.symm], hac.symm⟩
    · exact ⟨by simp [mem_finset4, had.symm], had.symm⟩

lemma coe_set4_diff_b {a b c d : P} (hab : a ≠ b) (hbc : b ≠ c) (hbd : b ≠ d) :
    ((({a, b, c, d} : Finset P) : Set P) \ {b}) = ({a, c, d} : Set P) := by
  ext x; constructor
  · intro hx
    rcases (mem_finset4 (a := a) (b := b) (c := c) (d := d)).1 hx.1 with rfl | rfl | rfl | rfl
    · simp
    · exact (hx.2 rfl).elim
    · simp
    · simp
  · intro hx
    rcases (show x = a ∨ x = c ∨ x = d by simpa using hx) with rfl | rfl | rfl
    · exact ⟨by simp [mem_finset4], hab⟩
    · exact ⟨by simp [mem_finset4, hbc.symm], hbc.symm⟩
    · exact ⟨by simp [mem_finset4, hbd.symm], hbd.symm⟩

lemma coe_set4_diff_c {a b c d : P} (hac : a ≠ c) (hbc : b ≠ c) (hcd : c ≠ d) :
    ((({a, b, c, d} : Finset P) : Set P) \ {c}) = ({a, b, d} : Set P) := by
  ext x; constructor
  · intro hx
    rcases (mem_finset4 (a := a) (b := b) (c := c) (d := d)).1 hx.1 with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact (hx.2 rfl).elim
    · simp
  · intro hx
    rcases (show x = a ∨ x = b ∨ x = d by simpa using hx) with rfl | rfl | rfl
    · exact ⟨by simp [mem_finset4], hac⟩
    · exact ⟨by simp [mem_finset4], hbc⟩
    · exact ⟨by simp [mem_finset4, hcd.symm], hcd.symm⟩

lemma coe_set4_diff_d {a b c d : P} (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((({a, b, c, d} : Finset P) : Set P) \ {d}) = ({a, b, c} : Set P) := by
  ext x; constructor
  · intro hx
    rcases (mem_finset4 (a := a) (b := b) (c := c) (d := d)).1 hx.1 with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact (hx.2 rfl).elim
  · intro hx
    rcases (show x = a ∨ x = b ∨ x = c by simpa using hx) with rfl | rfl | rfl
    · exact ⟨by simp [mem_finset4], had⟩
    · exact ⟨by simp [mem_finset4], hbd⟩
    · exact ⟨by simp [mem_finset4], hcd⟩

/-- F1: STATEMENT convex-position definition ↔ Mathlib `ConvexIndependent` on the 4-set. -/
theorem inConvexPosition4_iff_convexIndependent (a b c d : P)
    (h4 : ({a, b, c, d} : Finset P).card = 4) :
    InConvexPosition4 a b c d ↔
      ConvexIndependent ℝ (fun x : (({a, b, c, d} : Finset P) : Set P) => (x : P)) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := pairwise_of_card4 h4
  rw [convexIndependent_set_iff_not_mem_convexHull_diff]
  constructor
  · intro h x hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d := (mem_finset4).1 (by simpa using hx)
    rcases hx' with rfl | rfl | rfl | rfl
    · rw [coe_set4_diff_a hab hac had]; exact h.1
    · rw [coe_set4_diff_b hab hbc hbd]; exact h.2.1
    · rw [coe_set4_diff_c hac hbc hcd]; exact h.2.2.1
    · rw [coe_set4_diff_d had hbd hcd]; exact h.2.2.2
  · intro h
    constructor
    · rw [← coe_set4_diff_a hab hac had]; exact h a (by simp)
    constructor
    · rw [← coe_set4_diff_b hab hbc hbd]; exact h b (by simp)
    constructor
    · rw [← coe_set4_diff_c hac hbc hcd]; exact h c (by simp)
    · rw [← coe_set4_diff_d had hbd hcd]; exact h d (by simp)

/-- Convenience: `InConvexPosition4` yields the finset form used by `EsThreeEqFiveStatement`. -/
theorem exists_convexIndependent_of_inConvexPosition4 (a b c d : P)
    (h4 : ({a, b, c, d} : Finset P).card = 4)
    (h : InConvexPosition4 a b c d) :
    ∃ t : Finset P, t ⊆ ({a, b, c, d} : Finset P) ∧ t.card = 4 ∧
      ConvexIndependent ℝ (fun x : (↑t : Set P) => (x : P)) := by
  refine ⟨{a, b, c, d}, Finset.Subset.rfl, h4, ?_⟩
  exact (inConvexPosition4_iff_convexIndependent a b c d h4).1 h

/-! ## Hull-card lower bounds (OPE-410 item 1 progress) -/

/-- Lex-min point (min x, then min y) is a hull vertex — dual of `exists_hull_vertex`. -/
theorem exists_hull_vertex_min (s : Finset P) (hs : s.Nonempty) :
    ∃ p, IsHullVertex s p := by
  obtain ⟨p₀, hp₀, hmin0⟩ := s.exists_min_image (fun p : P => p.1) hs
  let s2 : Finset P := s.filter (fun q => q.1 = p₀.1)
  have hs2 : s2.Nonempty := ⟨p₀, by simp [s2, hp₀]⟩
  obtain ⟨q, hq, hmin1⟩ := s2.exists_min_image (fun p : P => p.2) hs2
  have hq_s : q ∈ s := (mem_filter.mp hq).1
  have hq1 : q.1 = p₀.1 := (mem_filter.mp hq).2
  refine ⟨q, hq_s, ?_⟩
  intro hconv
  rw [erase_coe] at hconv
  obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
  have hfst : q.1 = ∑ y ∈ s.erase q, w y * y.1 := by
    have := congr_arg Prod.fst hmass
    simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using this.symm
  have hsnd : q.2 = ∑ y ∈ s.erase q, w y * y.2 := by
    have := congr_arg Prod.snd hmass
    simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using this.symm
  have hy1_ge : ∀ y ∈ s.erase q, q.1 ≤ y.1 := by
    intro y hy
    have := hmin0 y (mem_of_mem_erase hy)
    linarith [hq1]
  have hle1 : ∀ y ∈ s.erase q, w y * q.1 ≤ w y * y.1 := fun y hy =>
    mul_le_mul_of_nonneg_left (hy1_ge y hy) (hw0 y hy)
  have hlhs1 : ∑ y ∈ s.erase q, w y * q.1 = q.1 := by simp [← sum_mul, hw1]
  have heq1 : ∑ y ∈ s.erase q, w y * q.1 = ∑ y ∈ s.erase q, w y * y.1 := by
    linarith [hfst, hlhs1]
  have hpair1 := weighted_eq_of_sum_eq w (fun _ => q.1) (fun y => y.1) hle1 heq1
  have hy1_eq : ∀ y ∈ s.erase q, w y ≠ 0 → y.1 = q.1 := by
    intro y hy hwne
    exact mul_left_cancel₀ hwne (by linarith [hpair1 y hy])
  have hle2 : ∀ y ∈ s.erase q, w y * q.2 ≤ w y * y.2 := by
    intro y hy
    by_cases hwne : w y = 0
    · simp [hwne]
    · have hy1eq := hy1_eq y hy hwne
      have y_in_s2 : y ∈ s2 := by
        simp only [s2, mem_filter, mem_of_mem_erase hy, true_and]
        linarith [hq1, hy1eq]
      exact mul_le_mul_of_nonneg_left (hmin1 y y_in_s2) (hw0 y hy)
  have hlhs2 : ∑ y ∈ s.erase q, w y * q.2 = q.2 := by simp [← sum_mul, hw1]
  have heq2 : ∑ y ∈ s.erase q, w y * q.2 = ∑ y ∈ s.erase q, w y * y.2 := by
    linarith [hsnd, hlhs2]
  have hpair2 := weighted_eq_of_sum_eq w (fun _ => q.2) (fun y => y.2) hle2 heq2
  have hy_eq : ∀ y ∈ s.erase q, w y ≠ 0 → y = q := by
    intro y hy hwne
    apply Prod.ext
    · exact hy1_eq y hy hwne
    · exact mul_left_cancel₀ hwne (by linarith [hpair2 y hy])
  obtain ⟨y, hy, hypos⟩ : ∃ y ∈ s.erase q, 0 < w y := by
    by_contra H
    push_neg at H
    have hz : ∀ y ∈ s.erase q, w y = 0 := fun y hy => le_antisymm (H y hy) (hw0 y hy)
    have : ∑ y ∈ s.erase q, w y = 0 := sum_eq_zero hz
    linarith [hw1]
  have yeq := hy_eq y hy (ne_of_gt hypos)
  have hy' := hy
  rw [yeq] at hy'
  exact absurd hy' (not_mem_erase q s)

/-! ## Sanity -/

example : orient ((0 : ℝ), 0) (1, 0) (0, 1) = 1 := by
  unfold orient; norm_num

example : orient ((0 : ℝ), 0) (1, 0) (2, 0) = 0 := by
  unfold orient; norm_num

end ProofLab.HappyEndingES3
