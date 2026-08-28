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
12. `exists_hull_vertex_min` (lex-min dual; OPE-410)
13. `proj` / orient-proj sums / `isHullVertex_of_max_orient_proj`
14. `exists_third_hull_vertex`, `hullVertices_card_ge_two`, `hullVertices_card_ge_three_of_gp`

## Delivered OPE-410 finish

15. Support-line hull criteria (`isHullVertex_of_orient_nonneg/nonpos`)
16. `both_sides_of_non_hull`, `inConvexPosition4_of_same_side_pair`
17. `es_three_eq_five_of_hull_card_eq_three` (separating-line bash)
18. Full **`es_three_eq_five`** discharging `EsThreeEqFiveStatement`

ES(4)=9 out of scope. **No claim** (classical 1935).
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


/-! ## Orientation affine sums + hull-card lower bounds (OPE-410) -/

/-- Projection of `x - a` onto `b - a`. -/
def proj (a b x : P) : ℝ :=
  (x.1 - a.1) * (b.1 - a.1) + (x.2 - a.2) * (b.2 - a.2)

lemma orient_sum_of_weight_one (a b : P) (s : Finset P) (w : P → ℝ)
    (hw1 : ∑ y ∈ s, w y = 1) :
    orient a b (∑ y ∈ s, w y • y) = ∑ y ∈ s, w y * orient a b y := by
  unfold orient
  have h1 : (∑ y ∈ s, w y • y).1 = ∑ y ∈ s, w y * y.1 := by
    simp [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
  have h2 : (∑ y ∈ s, w y • y).2 = ∑ y ∈ s, w y * y.2 := by
    simp [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
  rw [h1, h2]
  have hy2 : (∑ y ∈ s, w y * y.2) - a.2 = ∑ y ∈ s, w y * (y.2 - a.2) := by
    calc
      (∑ y ∈ s, w y * y.2) - a.2
          = (∑ y ∈ s, w y * y.2) - a.2 * (∑ y ∈ s, w y) := by rw [hw1]; ring
      _ = (∑ y ∈ s, w y * y.2) - ∑ y ∈ s, a.2 * w y := by simp [mul_sum]
      _ = ∑ y ∈ s, (w y * y.2 - a.2 * w y) := by rw [← sum_sub_distrib]
      _ = ∑ y ∈ s, w y * (y.2 - a.2) := by congr 1; ext y; ring
  have hy1 : (∑ y ∈ s, w y * y.1) - a.1 = ∑ y ∈ s, w y * (y.1 - a.1) := by
    calc
      (∑ y ∈ s, w y * y.1) - a.1
          = (∑ y ∈ s, w y * y.1) - a.1 * (∑ y ∈ s, w y) := by rw [hw1]; ring
      _ = (∑ y ∈ s, w y * y.1) - ∑ y ∈ s, a.1 * w y := by simp [mul_sum]
      _ = ∑ y ∈ s, (w y * y.1 - a.1 * w y) := by rw [← sum_sub_distrib]
      _ = ∑ y ∈ s, w y * (y.1 - a.1) := by congr 1; ext y; ring
  rw [hy2, hy1, mul_sum, mul_sum, ← sum_sub_distrib]
  congr 1; ext y; ring

lemma proj_sum_of_weight_one (a b : P) (s : Finset P) (w : P → ℝ)
    (hw1 : ∑ y ∈ s, w y = 1) :
    proj a b (∑ y ∈ s, w y • y) = ∑ y ∈ s, w y * proj a b y := by
  unfold proj
  have h1 : (∑ y ∈ s, w y • y).1 = ∑ y ∈ s, w y * y.1 := by
    simp [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
  have h2 : (∑ y ∈ s, w y • y).2 = ∑ y ∈ s, w y * y.2 := by
    simp [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
  rw [h1, h2]
  have hy1 : (∑ y ∈ s, w y * y.1) - a.1 = ∑ y ∈ s, w y * (y.1 - a.1) := by
    calc
      (∑ y ∈ s, w y * y.1) - a.1
          = (∑ y ∈ s, w y * y.1) - a.1 * (∑ y ∈ s, w y) := by rw [hw1]; ring
      _ = (∑ y ∈ s, w y * y.1) - ∑ y ∈ s, a.1 * w y := by simp [mul_sum]
      _ = ∑ y ∈ s, (w y * y.1 - a.1 * w y) := by rw [← sum_sub_distrib]
      _ = ∑ y ∈ s, w y * (y.1 - a.1) := by congr 1; ext y; ring
  have hy2 : (∑ y ∈ s, w y * y.2) - a.2 = ∑ y ∈ s, w y * (y.2 - a.2) := by
    calc
      (∑ y ∈ s, w y * y.2) - a.2
          = (∑ y ∈ s, w y * y.2) - a.2 * (∑ y ∈ s, w y) := by rw [hw1]; ring
      _ = (∑ y ∈ s, w y * y.2) - ∑ y ∈ s, a.2 * w y := by simp [mul_sum]
      _ = ∑ y ∈ s, (w y * y.2 - a.2 * w y) := by rw [← sum_sub_distrib]
      _ = ∑ y ∈ s, w y * (y.2 - a.2) := by congr 1; ext y; ring
  rw [hy1, hy2, sum_mul, sum_mul, ← sum_add_distrib]
  congr 1; ext y; ring

lemma eq_of_orient_eq_proj_eq {a b x y : P} (hab : a ≠ b)
    (ho : orient a b x = orient a b y) (hp : proj a b x = proj a b y) :
    x = y := by
  dsimp [orient, proj] at ho hp
  have hdet : (b.1 - a.1) * (x.2 - y.2) - (b.2 - a.2) * (x.1 - y.1) = 0 := by linarith
  have hdot : (b.1 - a.1) * (x.1 - y.1) + (b.2 - a.2) * (x.2 - y.2) = 0 := by linarith
  have hab' : b.1 ≠ a.1 ∨ b.2 ≠ a.2 := by
    by_contra h; push_neg at h
    exact hab (Prod.ext (by linarith) (by linarith))
  have hsumsq :
      ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) = 0 := by
    have hid :
        ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) =
          ((b.1 - a.1) * (x.1 - y.1) + (b.2 - a.2) * (x.2 - y.2)) ^ 2 +
            ((b.1 - a.1) * (x.2 - y.2) - (b.2 - a.2) * (x.1 - y.1)) ^ 2 := by ring
    rw [hid, hdot, hdet]; ring
  have hnorm : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h
    cases hab' with
    | inl hx => nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx.symm)]
    | inr hy => nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hy.symm)]
  have hxy : (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 = 0 := by
    have hA : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hnorm)
    exact (mul_eq_zero.mp hsumsq).resolve_left (ne_of_gt hA)
  apply Prod.ext
  · have : (x.1 - y.1) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (x.2 - y.2)]
    nlinarith [sq_nonneg (x.1 - y.1)]
  · have : (x.2 - y.2) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (x.1 - y.1)]
    nlinarith [sq_nonneg (x.2 - y.2)]

/-- Point maximizing orient, then proj, is a hull vertex (a ≠ b). -/
theorem isHullVertex_of_max_orient_proj (s : Finset P) (a b p : P)
    (hp : p ∈ s) (hab : a ≠ b)
    (hO : ∀ q ∈ s, orient a b q ≤ orient a b p)
    (hD : ∀ q ∈ s, orient a b q = orient a b p → proj a b q ≤ proj a b p) :
    IsHullVertex s p := by
  refine ⟨hp, ?_⟩
  intro hconv
  rw [erase_coe] at hconv
  obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
  have hOeq : orient a b p = ∑ y ∈ s.erase p, w y * orient a b y := by
    have h := congr_arg (orient a b) hmass
    rw [orient_sum_of_weight_one a b (s.erase p) w hw1] at h
    exact h.symm
  have hleO : ∀ y ∈ s.erase p, w y * orient a b y ≤ w y * orient a b p := by
    intro y hy
    exact mul_le_mul_of_nonneg_left (hO y (mem_of_mem_erase hy)) (hw0 y hy)
  have hrhsO : ∑ y ∈ s.erase p, w y * orient a b p = orient a b p := by
    simp [← sum_mul, hw1]
  have heqO : ∑ y ∈ s.erase p, w y * orient a b y = ∑ y ∈ s.erase p, w y * orient a b p := by
    linarith [hOeq, hrhsO]
  have hpairO := weighted_eq_of_sum_eq w (fun y => orient a b y) (fun _ => orient a b p) hleO heqO
  have hyO : ∀ y ∈ s.erase p, w y ≠ 0 → orient a b y = orient a b p := by
    intro y hy hwne
    exact mul_left_cancel₀ hwne (by linarith [hpairO y hy])
  have hPeq : proj a b p = ∑ y ∈ s.erase p, w y * proj a b y := by
    have h := congr_arg (proj a b) hmass
    rw [proj_sum_of_weight_one a b (s.erase p) w hw1] at h
    exact h.symm
  have hleP : ∀ y ∈ s.erase p, w y * proj a b y ≤ w y * proj a b p := by
    intro y hy
    by_cases hwne : w y = 0
    · simp [hwne]
    · have hOy := hyO y hy hwne
      exact mul_le_mul_of_nonneg_left
        (hD y (mem_of_mem_erase hy) hOy) (hw0 y hy)
  have hrhsP : ∑ y ∈ s.erase p, w y * proj a b p = proj a b p := by
    simp [← sum_mul, hw1]
  have heqP : ∑ y ∈ s.erase p, w y * proj a b y = ∑ y ∈ s.erase p, w y * proj a b p := by
    linarith [hPeq, hrhsP]
  have hpairP := weighted_eq_of_sum_eq w (fun y => proj a b y) (fun _ => proj a b p) hleP heqP
  have hyP : ∀ y ∈ s.erase p, w y ≠ 0 → proj a b y = proj a b p := by
    intro y hy hwne
    exact mul_left_cancel₀ hwne (by linarith [hpairP y hy])
  obtain ⟨y, hy, hypos⟩ : ∃ y ∈ s.erase p, 0 < w y := by
    by_contra H
    push_neg at H
    have hz : ∀ y ∈ s.erase p, w y = 0 := fun y hy => le_antisymm (H y hy) (hw0 y hy)
    have : ∑ y ∈ s.erase p, w y = 0 := sum_eq_zero hz
    linarith [hw1]
  have hyeq : y = p :=
    eq_of_orient_eq_proj_eq hab (hyO y hy (ne_of_gt hypos)) (hyP y hy (ne_of_gt hypos))
  exact absurd (hyeq ▸ hy) (not_mem_erase p s)

/-- If a≠b are in s and some point is off the line ab, a third hull vertex exists. -/
theorem exists_third_hull_vertex (s : Finset P) (a b : P)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hex : ∃ c ∈ s, orient a b c ≠ 0) :
    ∃ p, IsHullVertex s p ∧ p ≠ a ∧ p ≠ b := by
  have oa : orient a b a = 0 := by unfold orient; ring
  have ob : orient a b b = 0 := by unfold orient; ring
  by_cases hpos : ∃ c ∈ s, 0 < orient a b c
  · obtain ⟨p0, hp0, hmaxO⟩ := s.exists_max_image (fun q => orient a b q) ⟨a, ha⟩
    let sO : Finset P := s.filter (fun q => orient a b q = orient a b p0)
    have hsO : sO.Nonempty := ⟨p0, by simp [sO, hp0]⟩
    obtain ⟨p, hp, hmaxD⟩ := sO.exists_max_image (fun q => proj a b q) hsO
    have hp_s : p ∈ s := (mem_filter.mp hp).1
    have hpO : orient a b p = orient a b p0 := (mem_filter.mp hp).2
    have hO : ∀ q ∈ s, orient a b q ≤ orient a b p := by
      intro q hq
      calc orient a b q ≤ orient a b p0 := hmaxO q hq
        _ = orient a b p := hpO.symm
    have hD : ∀ q ∈ s, orient a b q = orient a b p → proj a b q ≤ proj a b p := by
      intro q hq hqO
      have hqO' : q ∈ sO := by
        simp only [sO, mem_filter, hq, true_and]
        linarith [hqO, hpO]
      exact hmaxD q hqO'
    have hV := isHullVertex_of_max_orient_proj s a b p hp_s hab hO hD
    obtain ⟨c, hc, hcpos⟩ := hpos
    have hmaxpos : 0 < orient a b p := by
      have := hO c hc; linarith
    refine ⟨p, hV, ?_, ?_⟩
    · intro hpa; subst hpa; linarith [oa, hmaxpos]
    · intro hpb; subst hpb; linarith [ob, hmaxpos]
  · push_neg at hpos
    obtain ⟨c, hc, hc0⟩ := hex
    have hcneg : orient a b c < 0 := by
      have hle : orient a b c ≤ 0 := hpos c hc
      exact lt_of_le_of_ne hle hc0
    have hba : b ≠ a := hab.symm
    have orient_swap : ∀ q, orient b a q = -orient a b q := by
      intro q; unfold orient; ring
    obtain ⟨p0, hp0, hmaxO⟩ := s.exists_max_image (fun q => orient b a q) ⟨b, hb⟩
    let sO : Finset P := s.filter (fun q => orient b a q = orient b a p0)
    have hsO : sO.Nonempty := ⟨p0, by simp [sO, hp0]⟩
    obtain ⟨p, hp, hmaxD⟩ := sO.exists_max_image (fun q => proj b a q) hsO
    have hp_s : p ∈ s := (mem_filter.mp hp).1
    have hpO : orient b a p = orient b a p0 := (mem_filter.mp hp).2
    have hO : ∀ q ∈ s, orient b a q ≤ orient b a p := by
      intro q hq
      calc orient b a q ≤ orient b a p0 := hmaxO q hq
        _ = orient b a p := hpO.symm
    have hD : ∀ q ∈ s, orient b a q = orient b a p → proj b a q ≤ proj b a p := by
      intro q hq hqO
      have hqO' : q ∈ sO := by
        simp only [sO, mem_filter, hq, true_and]
        linarith [hqO, hpO]
      exact hmaxD q hqO'
    have hV := isHullVertex_of_max_orient_proj s b a p hp_s hba hO hD
    have hmaxpos : 0 < orient b a p := by
      have hcpos : 0 < orient b a c := by
        have := orient_swap c; linarith [hcneg]
      have := hO c hc; linarith
    have oa' : orient b a a = 0 := by unfold orient; ring
    have ob' : orient b a b = 0 := by unfold orient; ring
    refine ⟨p, hV, ?_, ?_⟩
    · intro hpa; subst hpa; linarith [oa', hmaxpos]
    · intro hpb; subst hpb; linarith [ob', hmaxpos]

/-- At least two hull vertices when `s` has two distinct points. -/
theorem hullVertices_card_ge_two (s : Finset P) (hs : 2 ≤ s.card) :
    2 ≤ (hullVertices s).card := by
  have hne : s.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hs)
  obtain ⟨pmax₀, hpmax₀, hmax0⟩ := s.exists_max_image (fun p : P => p.1) hne
  let sMax : Finset P := s.filter (fun q => q.1 = pmax₀.1)
  have hsMax : sMax.Nonempty := ⟨pmax₀, by simp [sMax, hpmax₀]⟩
  obtain ⟨xmax, hxmax, hmax1⟩ := sMax.exists_max_image (fun p : P => p.2) hsMax
  obtain ⟨pmin₀, hpmin₀, hmin0⟩ := s.exists_min_image (fun p : P => p.1) hne
  let sMin : Finset P := s.filter (fun q => q.1 = pmin₀.1)
  have hsMin : sMin.Nonempty := ⟨pmin₀, by simp [sMin, hpmin₀]⟩
  obtain ⟨xmin, hxmin, hmin1⟩ := sMin.exists_min_image (fun p : P => p.2) hsMin
  have xmaxV : IsHullVertex s xmax := by
    refine ⟨(mem_filter.mp hxmax).1, ?_⟩
    intro hconv
    rw [erase_coe] at hconv
    obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
    have hq1 : xmax.1 = pmax₀.1 := (mem_filter.mp hxmax).2
    have hfst : xmax.1 = ∑ y ∈ s.erase xmax, w y * y.1 := by
      have := congr_arg Prod.fst hmass
      simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using this.symm
    have hsnd : xmax.2 = ∑ y ∈ s.erase xmax, w y * y.2 := by
      have := congr_arg Prod.snd hmass
      simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using this.symm
    have hy1_le : ∀ y ∈ s.erase xmax, y.1 ≤ xmax.1 := by
      intro y hy; have := hmax0 y (mem_of_mem_erase hy); linarith [hq1]
    have hle1 : ∀ y ∈ s.erase xmax, w y * y.1 ≤ w y * xmax.1 := fun y hy =>
      mul_le_mul_of_nonneg_left (hy1_le y hy) (hw0 y hy)
    have hrhs1 : ∑ y ∈ s.erase xmax, w y * xmax.1 = xmax.1 := by simp [← sum_mul, hw1]
    have heq1 : ∑ y ∈ s.erase xmax, w y * y.1 = ∑ y ∈ s.erase xmax, w y * xmax.1 := by
      linarith [hfst, hrhs1]
    have hpair1 := weighted_eq_of_sum_eq w (fun y => y.1) (fun _ => xmax.1) hle1 heq1
    have hy1_eq : ∀ y ∈ s.erase xmax, w y ≠ 0 → y.1 = xmax.1 := by
      intro y hy hwne; exact mul_left_cancel₀ hwne (by linarith [hpair1 y hy])
    have hle2 : ∀ y ∈ s.erase xmax, w y * y.2 ≤ w y * xmax.2 := by
      intro y hy
      by_cases hwne : w y = 0
      · simp [hwne]
      · have hy1eq := hy1_eq y hy hwne
        have y_in : y ∈ sMax := by
          simp only [sMax, mem_filter, mem_of_mem_erase hy, true_and]
          linarith [hq1, hy1eq]
        exact mul_le_mul_of_nonneg_left (hmax1 y y_in) (hw0 y hy)
    have hrhs2 : ∑ y ∈ s.erase xmax, w y * xmax.2 = xmax.2 := by simp [← sum_mul, hw1]
    have heq2 : ∑ y ∈ s.erase xmax, w y * y.2 = ∑ y ∈ s.erase xmax, w y * xmax.2 := by
      linarith [hsnd, hrhs2]
    have hpair2 := weighted_eq_of_sum_eq w (fun y => y.2) (fun _ => xmax.2) hle2 heq2
    have hy_eq : ∀ y ∈ s.erase xmax, w y ≠ 0 → y = xmax := by
      intro y hy hwne
      apply Prod.ext
      · exact hy1_eq y hy hwne
      · exact mul_left_cancel₀ hwne (by linarith [hpair2 y hy])
    obtain ⟨y, hy, hypos⟩ : ∃ y ∈ s.erase xmax, 0 < w y := by
      by_contra H
      push_neg at H
      have hz : ∀ y ∈ s.erase xmax, w y = 0 := fun y hy => le_antisymm (H y hy) (hw0 y hy)
      have : ∑ y ∈ s.erase xmax, w y = 0 := sum_eq_zero hz
      linarith [hw1]
    have yeq := hy_eq y hy (ne_of_gt hypos)
    exact absurd (yeq ▸ hy) (not_mem_erase xmax s)
  have xminV : IsHullVertex s xmin := by
    refine ⟨(mem_filter.mp hxmin).1, ?_⟩
    intro hconv
    rw [erase_coe] at hconv
    obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
    have hq1 : xmin.1 = pmin₀.1 := (mem_filter.mp hxmin).2
    have hfst : xmin.1 = ∑ y ∈ s.erase xmin, w y * y.1 := by
      have := congr_arg Prod.fst hmass
      simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using this.symm
    have hsnd : xmin.2 = ∑ y ∈ s.erase xmin, w y * y.2 := by
      have := congr_arg Prod.snd hmass
      simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using this.symm
    have hy1_ge : ∀ y ∈ s.erase xmin, xmin.1 ≤ y.1 := by
      intro y hy; have := hmin0 y (mem_of_mem_erase hy); linarith [hq1]
    have hle1 : ∀ y ∈ s.erase xmin, w y * xmin.1 ≤ w y * y.1 := fun y hy =>
      mul_le_mul_of_nonneg_left (hy1_ge y hy) (hw0 y hy)
    have hlhs1 : ∑ y ∈ s.erase xmin, w y * xmin.1 = xmin.1 := by simp [← sum_mul, hw1]
    have heq1 : ∑ y ∈ s.erase xmin, w y * xmin.1 = ∑ y ∈ s.erase xmin, w y * y.1 := by
      linarith [hfst, hlhs1]
    have hpair1 := weighted_eq_of_sum_eq w (fun _ => xmin.1) (fun y => y.1) hle1 heq1
    have hy1_eq : ∀ y ∈ s.erase xmin, w y ≠ 0 → y.1 = xmin.1 := by
      intro y hy hwne; exact mul_left_cancel₀ hwne (by linarith [hpair1 y hy])
    have hle2 : ∀ y ∈ s.erase xmin, w y * xmin.2 ≤ w y * y.2 := by
      intro y hy
      by_cases hwne : w y = 0
      · simp [hwne]
      · have hy1eq := hy1_eq y hy hwne
        have y_in : y ∈ sMin := by
          simp only [sMin, mem_filter, mem_of_mem_erase hy, true_and]
          linarith [hq1, hy1eq]
        exact mul_le_mul_of_nonneg_left (hmin1 y y_in) (hw0 y hy)
    have hlhs2 : ∑ y ∈ s.erase xmin, w y * xmin.2 = xmin.2 := by simp [← sum_mul, hw1]
    have heq2 : ∑ y ∈ s.erase xmin, w y * xmin.2 = ∑ y ∈ s.erase xmin, w y * y.2 := by
      linarith [hsnd, hlhs2]
    have hpair2 := weighted_eq_of_sum_eq w (fun _ => xmin.2) (fun y => y.2) hle2 heq2
    have hy_eq : ∀ y ∈ s.erase xmin, w y ≠ 0 → y = xmin := by
      intro y hy hwne
      apply Prod.ext
      · exact hy1_eq y hy hwne
      · exact mul_left_cancel₀ hwne (by linarith [hpair2 y hy])
    obtain ⟨y, hy, hypos⟩ : ∃ y ∈ s.erase xmin, 0 < w y := by
      by_contra H
      push_neg at H
      have hz : ∀ y ∈ s.erase xmin, w y = 0 := fun y hy => le_antisymm (H y hy) (hw0 y hy)
      have : ∑ y ∈ s.erase xmin, w y = 0 := sum_eq_zero hz
      linarith [hw1]
    have yeq := hy_eq y hy (ne_of_gt hypos)
    exact absurd (yeq ▸ hy) (not_mem_erase xmin s)
  have hne_pm : xmin ≠ xmax := by
    intro heq
    have hx_all : ∀ q ∈ s, q.1 = xmin.1 := by
      intro q hq
      have hlo := hmin0 q hq
      have hhi := hmax0 q hq
      have hmin1eq : xmin.1 = pmin₀.1 := (mem_filter.mp hxmin).2
      have hmax1eq : xmax.1 = pmax₀.1 := (mem_filter.mp hxmax).2
      have : xmin.1 = xmax.1 := by rw [heq]
      linarith
    have hy_all : ∀ q ∈ s, q.2 = xmin.2 := by
      intro q hq
      have hx := hx_all q hq
      have qMin : q ∈ sMin := by
        simp only [sMin, mem_filter, hq, true_and]
        linarith [(mem_filter.mp hxmin).2]
      have qMax : q ∈ sMax := by
        simp only [sMax, mem_filter, hq, true_and]
        have : q.1 = pmax₀.1 := by
          have hxm := (mem_filter.mp hxmax).2
          have heq1 : xmin.1 = xmax.1 := by rw [heq]
          linarith [hx, (mem_filter.mp hxmin).2, hxm, heq1]
        exact this
      have hlo := hmin1 q qMin
      have hhi := hmax1 q qMax
      have : xmin.2 = xmax.2 := by rw [heq]
      linarith
    have hall : ∀ q ∈ s, q = xmin := fun q hq => Prod.ext (hx_all q hq) (hy_all q hq)
    have : s ⊆ ({xmin} : Finset P) := by intro q hq; simp [hall q hq]
    have : s.card ≤ 1 := (card_le_card this).trans (by simp)
    linarith
  have hsub : ({xmin, xmax} : Finset P) ⊆ hullVertices s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_hullVertices.mpr xminV
    · exact mem_hullVertices.mpr xmaxV
  have h2 : ({xmin, xmax} : Finset P).card = 2 := card_pair hne_pm
  exact le_trans (le_of_eq h2.symm) (card_le_card hsub)

/-- Under GP, a 3-point (or larger) set has at least 3 hull vertices. -/
theorem hullVertices_card_ge_three_of_gp (s : Finset P)
    (hs : 3 ≤ s.card) (hgp : GeneralPosition s) :
    3 ≤ (hullVertices s).card := by
  have h2le : 2 ≤ (hullVertices s).card :=
    hullVertices_card_ge_two s (le_trans (by norm_num : (2:ℕ) ≤ 3) hs)
  obtain ⟨t, ht_sub, ht2⟩ := exists_subset_card_eq h2le
  rw [card_eq_two] at ht2
  obtain ⟨a, b, hab, rfl⟩ := ht2
  have haH : a ∈ hullVertices s := ht_sub (by simp)
  have hbH : b ∈ hullVertices s := ht_sub (by simp)
  have ha : a ∈ s := (mem_hullVertices.mp haH).1
  have hb : b ∈ s := (mem_hullVertices.mp hbH).1
  obtain ⟨c0, hc0s, hc0ab⟩ : ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
    by_contra H
    push_neg at H
    have hsub : s ⊆ ({a, b} : Finset P) := by
      intro x hx
      have hx' : x = a ∨ x = b := by
        by_cases hxa : x = a
        · exact Or.inl hxa
        · exact Or.inr (H x hx hxa)
      simpa using hx'
    have hle : s.card ≤ 2 := by
      have : ({a, b} : Finset P).card = 2 := card_pair hab
      exact (card_le_card hsub).trans (by simp [this])
    linarith
  have hone : orient a b c0 ≠ 0 :=
    hgp ha hb hc0s hab hc0ab.2.symm hc0ab.1.symm
  obtain ⟨p, hpV, hpa, hpb⟩ :=
    exists_third_hull_vertex s a b ha hb hab ⟨c0, hc0s, hone⟩
  have hpH : p ∈ hullVertices s := mem_hullVertices.mpr hpV
  have hsub3 : ({a, b, p} : Finset P) ⊆ hullVertices s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haH
    · exact hbH
    · exact hpH
  have h3 : 3 ≤ ({a, b, p} : Finset P).card := by
    have hpn : p ∉ ({a, b} : Finset P) := by simp [hpa, hpb]
    have heq : ({a, b, p} : Finset P) = insert p ({a, b} : Finset P) := by
      ext x; simp; tauto
    have hcard : ({a, b, p} : Finset P).card = 3 := by
      rw [heq, card_insert_of_not_mem hpn, card_pair hab]
    exact le_of_eq hcard.symm
  exact le_trans h3 (card_le_card hsub3)


/-! ## Interior case: separating line through the non-hull pair (OPE-410) -/

private lemma sum3_orient (d e b c x : P) (w : P → ℝ)
    (hbx : b ≠ x) (hcx : c ≠ x) (hbc : b ≠ c) :
    ∑ y ∈ ({b, c, x} : Finset P), w y * orient d e y =
      w b * orient d e b + w c * orient d e c + w x * orient d e x := by
  simp [hbx, hcx, hbc, Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
  abel

private lemma sum3_w (b c x : P) (w : P → ℝ)
    (hbx : b ≠ x) (hcx : c ≠ x) (hbc : b ≠ c) :
    ∑ y ∈ ({b, c, x} : Finset P), w y = w b + w c + w x := by
  simp [hbx, hcx, hbc, Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
  abel

private lemma sum3_smul (b c x : P) (w : P → ℝ)
    (hbx : b ≠ x) (hcx : c ≠ x) (hbc : b ≠ c) :
    ∑ y ∈ ({b, c, x} : Finset P), w y • y = w b • b + w c • c + w x • x := by
  simp [hbx, hcx, hbc, Finset.sum_insert, Finset.mem_insert, Finset.sum_singleton]
  abel

/-- Support line: all `orient d e ≥ 0` ⇒ `d` is a hull vertex (under GP). -/
theorem isHullVertex_of_orient_nonneg (s : Finset P) (d e : P)
    (hd : d ∈ s) (he : e ∈ s) (hde : d ≠ e) (hgp : GeneralPosition s)
    (hnn : ∀ p ∈ s, 0 ≤ orient d e p) : IsHullVertex s d := by
  refine ⟨hd, ?_⟩
  intro hconv
  rw [erase_coe] at hconv
  obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
  have hode : orient d e d = 0 := by unfold orient; ring
  have hsum : ∑ y ∈ s.erase d, w y * orient d e y = 0 := by
    have h := congr_arg (orient d e) hmass
    rw [orient_sum_of_weight_one d e (s.erase d) w hw1] at h
    linarith [hode, h.symm]
  have hnn_all : ∀ t ∈ s.erase d, 0 ≤ w t * orient d e t := fun t ht =>
    mul_nonneg (hw0 t ht) (hnn t (mem_of_mem_erase ht))
  have hall0 := (sum_eq_zero_iff_of_nonneg hnn_all).1 hsum
  have only_e : ∀ z ∈ s.erase d, w z ≠ 0 → z = e := by
    intro z hz hwz
    have hoz : orient d e z = 0 := (mul_eq_zero.mp (hall0 z hz)).resolve_left hwz
    have hz_s : z ∈ s := mem_of_mem_erase hz
    have hz_ne_d : z ≠ d := ne_of_mem_erase hz
    by_contra hzne
    have hzne' : e ≠ z := fun h => hzne h.symm
    exact hgp hd he hz_s hde hzne' hz_ne_d.symm hoz
  have he_mem : e ∈ s.erase d := mem_erase.mpr ⟨hde.symm, he⟩
  have hwe : w e = 1 := by
    have hsupp : ∀ z ∈ s.erase d, z ≠ e → w z = 0 := by
      intro z hz hzne
      by_cases hwz : w z = 0
      · exact hwz
      · exact absurd (only_e z hz hwz) hzne
    have hrest : ∑ z ∈ (s.erase d).erase e, w z = 0 :=
      sum_eq_zero fun z hz => hsupp z (mem_of_mem_erase hz) (ne_of_mem_erase hz)
    have hsplit := sum_erase_add (s.erase d) w he_mem
    linarith [hw1, hrest, hsplit]
  have hsum_smul : ∑ z ∈ s.erase d, w z • z = w e • e := by
    have hsplit := (sum_erase_add (s.erase d) (fun z => w z • z) he_mem).symm
    have hrest : ∑ z ∈ (s.erase d).erase e, w z • z = 0 := by
      apply sum_eq_zero
      intro z hz
      have hwz0 : w z = 0 := by
        by_cases hwz : w z = 0
        · exact hwz
        · exact absurd (only_e z (mem_of_mem_erase hz) hwz) (ne_of_mem_erase hz)
      simp [hwz0]
    simpa [hrest] using hsplit
  have : d = e := by
    have := hmass.symm
    rw [hsum_smul, hwe, one_smul] at this
    exact this
  exact hde this

/-- Support line: all `orient d e ≤ 0` ⇒ `d` is a hull vertex (under GP). -/
theorem isHullVertex_of_orient_nonpos (s : Finset P) (d e : P)
    (hd : d ∈ s) (he : e ∈ s) (hde : d ≠ e) (hgp : GeneralPosition s)
    (hnp : ∀ p ∈ s, orient d e p ≤ 0) : IsHullVertex s d := by
  refine ⟨hd, ?_⟩
  intro hconv
  rw [erase_coe] at hconv
  obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp hconv
  have hode : orient d e d = 0 := by unfold orient; ring
  have hsum : ∑ y ∈ s.erase d, w y * orient d e y = 0 := by
    have h := congr_arg (orient d e) hmass
    rw [orient_sum_of_weight_one d e (s.erase d) w hw1] at h
    linarith [hode, h.symm]
  have hnp_all : ∀ t ∈ s.erase d, w t * orient d e t ≤ 0 := fun t ht =>
    mul_nonpos_of_nonneg_of_nonpos (hw0 t ht) (hnp t (mem_of_mem_erase ht))
  have hall0 : ∀ y ∈ s.erase d, w y * orient d e y = 0 := by
    intro y hy
    have hnegsum : ∑ t ∈ s.erase d, -(w t * orient d e t) = 0 := by
      simp [sum_neg_distrib, hsum]
    have hnn : ∀ t ∈ s.erase d, 0 ≤ -(w t * orient d e t) := fun t ht =>
      neg_nonneg.mpr (hnp_all t ht)
    linarith [(sum_eq_zero_iff_of_nonneg hnn).1 hnegsum y hy]
  have only_e : ∀ z ∈ s.erase d, w z ≠ 0 → z = e := by
    intro z hz hwz
    have hoz : orient d e z = 0 := (mul_eq_zero.mp (hall0 z hz)).resolve_left hwz
    have hz_s : z ∈ s := mem_of_mem_erase hz
    have hz_ne_d : z ≠ d := ne_of_mem_erase hz
    by_contra hzne
    have hzne' : e ≠ z := fun h => hzne h.symm
    exact hgp hd he hz_s hde hzne' hz_ne_d.symm hoz
  have he_mem : e ∈ s.erase d := mem_erase.mpr ⟨hde.symm, he⟩
  have hwe : w e = 1 := by
    have hsupp : ∀ z ∈ s.erase d, z ≠ e → w z = 0 := by
      intro z hz hzne
      by_cases hwz : w z = 0
      · exact hwz
      · exact absurd (only_e z hz hwz) hzne
    have hrest : ∑ z ∈ (s.erase d).erase e, w z = 0 :=
      sum_eq_zero fun z hz => hsupp z (mem_of_mem_erase hz) (ne_of_mem_erase hz)
    have hsplit := sum_erase_add (s.erase d) w he_mem
    linarith [hw1, hrest, hsplit]
  have hsum_smul : ∑ z ∈ s.erase d, w z • z = w e • e := by
    have hsplit := (sum_erase_add (s.erase d) (fun z => w z • z) he_mem).symm
    have hrest : ∑ z ∈ (s.erase d).erase e, w z • z = 0 := by
      apply sum_eq_zero
      intro z hz
      have hwz0 : w z = 0 := by
        by_cases hwz : w z = 0
        · exact hwz
        · exact absurd (only_e z (mem_of_mem_erase hz) hwz) (ne_of_mem_erase hz)
      simp [hwz0]
    simpa [hrest] using hsplit
  have : d = e := by
    have := hmass.symm
    rw [hsum_smul, hwe, one_smul] at this
    exact this
  exact hde this

/-- Non-hull endpoint ⇒ both open half-planes of `de` meet `s`. -/
theorem both_sides_of_non_hull (s : Finset P) (d e : P)
    (hd : d ∈ s) (he : e ∈ s) (hde : d ≠ e) (hgp : GeneralPosition s)
    (hdV : ¬IsHullVertex s d) :
    (∃ p ∈ s, orient d e p < 0) ∧ (∃ p ∈ s, 0 < orient d e p) := by
  constructor
  · by_contra H; push_neg at H
    exact hdV (isHullVertex_of_orient_nonneg s d e hd he hde hgp H)
  · by_contra H; push_neg at H
    exact hdV (isHullVertex_of_orient_nonpos s d e hd he hde hgp H)

/-- Same strict side of `de` + hull vertices `b`,`c` ⇒ `InConvexPosition4 b c d e`. -/
theorem inConvexPosition4_of_same_side_pair (s : Finset P) (b c d e : P)
    (hbV : IsHullVertex s b) (hcV : IsHullVertex s c)
    (hd : d ∈ s) (he : e ∈ s)
    (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) (hbc : b ≠ c)
    (hside : 0 < orient d e b * orient d e c) :
    InConvexPosition4 b c d e := by
  have hb_s := hbV.1
  have hc_s := hcV.1
  have same_sign :
      (0 < orient d e b ∧ 0 < orient d e c) ∨ (orient d e b < 0 ∧ orient d e c < 0) := by
    have := mul_pos_iff.mp hside; tauto
  constructor
  · intro hbconv
    have hsub : ({c, d, e} : Set P) ⊆ (s : Set P) \ {b} := by
      intro x hx
      rcases (show x = c ∨ x = d ∨ x = e by simpa using hx) with rfl | rfl | rfl
      · exact ⟨hc_s, fun h => hbc h.symm⟩
      · exact ⟨hd, fun h => hbd h.symm⟩
      · exact ⟨he, fun h => hbe h.symm⟩
    exact hbV.2 (convexHull_mono hsub hbconv)
  constructor
  · intro hcconv
    have hsub : ({b, d, e} : Set P) ⊆ (s : Set P) \ {c} := by
      intro x hx
      rcases (show x = b ∨ x = d ∨ x = e by simpa using hx) with rfl | rfl | rfl
      · exact ⟨hb_s, hbc⟩
      · exact ⟨hd, fun h => hcd h.symm⟩
      · exact ⟨he, fun h => hce h.symm⟩
    exact hcV.2 (convexHull_mono hsub hcconv)
  constructor
  · intro hdconv
    obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp (by
      have : (({b, c, e} : Finset P) : Set P) = ({b, c, e} : Set P) := by ext; simp
      rwa [← this] at hdconv)
    have hode : orient d e d = 0 := by unfold orient; ring
    have hoe : orient d e e = 0 := by unfold orient; ring
    have hsum : ∑ y ∈ ({b, c, e} : Finset P), w y * orient d e y = 0 := by
      have h := congr_arg (orient d e) hmass
      rw [orient_sum_of_weight_one d e _ w hw1] at h
      linarith [hode, h.symm]
    have hw_sum : w b * orient d e b + w c * orient d e c = 0 := by
      have hsum' := hsum
      rw [sum3_orient d e b c e w hbe hce hbc, hoe, mul_zero, add_zero] at hsum'
      exact hsum'
    have wb0 : w b = 0 := by
      rcases same_sign with ⟨hbpos, hcpos⟩ | ⟨hbneg, hcneg⟩
      · have : w b * orient d e b = 0 := by
          nlinarith [mul_nonneg (hw0 b (by simp)) (le_of_lt hbpos),
            mul_nonneg (hw0 c (by simp)) (le_of_lt hcpos), hw_sum]
        exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hbpos)
      · have : w b * orient d e b = 0 := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (hw0 b (by simp)) (le_of_lt hbneg),
            mul_nonpos_of_nonneg_of_nonpos (hw0 c (by simp)) (le_of_lt hcneg), hw_sum]
        exact (mul_eq_zero.mp this).resolve_right (ne_of_lt hbneg)
    have wc0 : w c = 0 := by
      rcases same_sign with ⟨hbpos, hcpos⟩ | ⟨hbneg, hcneg⟩
      · exact (mul_eq_zero.mp (show w c * orient d e c = 0 by nlinarith [hw_sum, wb0])).resolve_right
          (ne_of_gt hcpos)
      · exact (mul_eq_zero.mp (show w c * orient d e c = 0 by nlinarith [hw_sum, wb0])).resolve_right
          (ne_of_lt hcneg)
    have hwe : w e = 1 := by
      have hw1' := hw1
      rw [sum3_w b c e w hbe hce hbc] at hw1'
      linarith [hw1', wb0, wc0]
    have hmass' : d = w b • b + w c • c + w e • e := by
      have hsm := sum3_smul b c e w hbe hce hbc
      have hmass2 : d = ∑ y ∈ ({b, c, e} : Finset P), w y • y := hmass.symm
      rw [hmass2, hsm]
    simp [wb0, wc0, hwe, one_smul] at hmass'
    exact hde hmass'
  · intro heconv
    obtain ⟨w, hw0, hw1, hmass⟩ := Finset.mem_convexHull'.mp (by
      have : (({b, c, d} : Finset P) : Set P) = ({b, c, d} : Set P) := by ext; simp
      rwa [← this] at heconv)
    have hode : orient d e d = 0 := by unfold orient; ring
    have hoe : orient d e e = 0 := by unfold orient; ring
    have hsum : ∑ y ∈ ({b, c, d} : Finset P), w y * orient d e y = 0 := by
      have h := congr_arg (orient d e) hmass
      rw [orient_sum_of_weight_one d e _ w hw1] at h
      linarith [hoe, h.symm]
    have hw_sum : w b * orient d e b + w c * orient d e c = 0 := by
      have hsum' := hsum
      rw [sum3_orient d e b c d w hbd hcd hbc, hode, mul_zero, add_zero] at hsum'
      exact hsum'
    have wb0 : w b = 0 := by
      rcases same_sign with ⟨hbpos, hcpos⟩ | ⟨hbneg, hcneg⟩
      · have : w b * orient d e b = 0 := by
          nlinarith [mul_nonneg (hw0 b (by simp)) (le_of_lt hbpos),
            mul_nonneg (hw0 c (by simp)) (le_of_lt hcpos), hw_sum]
        exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hbpos)
      · have : w b * orient d e b = 0 := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (hw0 b (by simp)) (le_of_lt hbneg),
            mul_nonpos_of_nonneg_of_nonpos (hw0 c (by simp)) (le_of_lt hcneg), hw_sum]
        exact (mul_eq_zero.mp this).resolve_right (ne_of_lt hbneg)
    have wc0 : w c = 0 := by
      rcases same_sign with ⟨hbpos, hcpos⟩ | ⟨hbneg, hcneg⟩
      · exact (mul_eq_zero.mp (show w c * orient d e c = 0 by nlinarith [hw_sum, wb0])).resolve_right
          (ne_of_gt hcpos)
      · exact (mul_eq_zero.mp (show w c * orient d e c = 0 by nlinarith [hw_sum, wb0])).resolve_right
          (ne_of_lt hcneg)
    have hwd : w d = 1 := by
      have hw1' := hw1
      rw [sum3_w b c d w hbd hcd hbc] at hw1'
      linarith [hw1', wb0, wc0]
    have hmass' : e = w b • b + w c • c + w d • d := by
      have hsm := sum3_smul b c d w hbd hcd hbc
      have hmass2 : e = ∑ y ∈ ({b, c, d} : Finset P), w y • y := hmass.symm
      rw [hmass2, hsm]
    simp [wb0, wc0, hwd, one_smul] at hmass'
    exact hde.symm hmass'

private lemma s_eq_hull_union_pair (s : Finset P) (a b c d e : P)
    (hH : hullVertices s = {a, b, c})
    (hR : s \ hullVertices s = {d, e}) :
    s = {a, b, c, d, e} := by
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ hullVertices s
    · have : x ∈ ({a, b, c} : Finset P) := by rwa [hH] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    · have hxR : x ∈ s \ hullVertices s := mem_sdiff.mpr ⟨hx, h⟩
      have : x ∈ ({d, e} : Finset P) := by rwa [hR] at hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
  · intro hx
    have hx' : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx
    have memH : ∀ p, p ∈ ({a, b, c} : Finset P) → p ∈ s := by
      intro p hp
      have hpH : p ∈ hullVertices s := by simpa [hH] using hp
      exact (mem_hullVertices.mp hpH).1
    have memR : ∀ p, p ∈ ({d, e} : Finset P) → p ∈ s := by
      intro p hp
      have hpR : p ∈ s \ hullVertices s := by simpa [hR] using hp
      exact (mem_sdiff.mp hpR).1
    rcases hx' with h | h | h | h | h
    · rw [h]; exact memH a (by simp)
    · rw [h]; exact memH b (by simp)
    · rw [h]; exact memH c (by simp)
    · rw [h]; exact memR d (by simp)
    · rw [h]; exact memR e (by simp)

private lemma card4_of_pairwise {u v d e : P}
    (huv : u ≠ v) (hud : u ≠ d) (hue : u ≠ e) (hvd : v ≠ d) (hve : v ≠ e) (hde : d ≠ e) :
    ({u, v, d, e} : Finset P).card = 4 := by
  have h2 : ({d, e} : Finset P).card = 2 := card_pair hde
  have hv_not : v ∉ ({d, e} : Finset P) := by simp [hvd, hve]
  have h3 : ({v, d, e} : Finset P).card = 3 := by
    rw [card_insert_of_not_mem hv_not, h2]
  have hu_not : u ∉ ({v, d, e} : Finset P) := by simp [huv, hud, hue]
  rw [card_insert_of_not_mem hu_not, h3]

/-- Triangle hull + 2 non-hull points ⇒ convex 4-subset via separating line. -/
theorem es_three_eq_five_of_hull_card_eq_three (s : Finset P)
    (hcard : s.card = 5) (hgp : GeneralPosition s)
    (hHcard : (hullVertices s).card = 3) :
    ∃ t : Finset P, t ⊆ s ∧ t.card = 4 ∧
      ConvexIndependent ℝ (fun x : (↑t : Set P) => (x : P)) := by
  have hHeq := hHcard
  rw [card_eq_three] at hHeq
  obtain ⟨a, b, c, hab, hac, hbc, hHset⟩ := hHeq
  have haH : a ∈ hullVertices s := by rw [hHset]; simp
  have hbH : b ∈ hullVertices s := by rw [hHset]; simp
  have hcH : c ∈ hullVertices s := by rw [hHset]; simp
  have haV := mem_hullVertices.mp haH
  have hbV := mem_hullVertices.mp hbH
  have hcV := mem_hullVertices.mp hcH
  have ha := haV.1; have hb := hbV.1; have hc := hcV.1
  let R := s \ hullVertices s
  have hRcard : R.card = 2 := by
    have hdisj : Disjoint (hullVertices s) R := disjoint_sdiff
    have hunion : hullVertices s ∪ R = s := by
      ext x; constructor
      · intro hx
        rcases mem_union.mp hx with h | h
        · exact (mem_hullVertices.mp h).1
        · exact (mem_sdiff.mp h).1
      · intro hx
        by_cases h : x ∈ hullVertices s
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, h⟩)
    have hsum : (hullVertices s ∪ R).card = (hullVertices s).card + R.card :=
      card_union_of_disjoint hdisj
    rw [hunion, hcard, hHcard] at hsum
    omega
  rw [card_eq_two] at hRcard
  obtain ⟨d, e, hde, hRset⟩ := hRcard
  have hdR : d ∈ R := by rw [hRset]; simp
  have heR : e ∈ R := by rw [hRset]; simp
  have hd : d ∈ s := (mem_sdiff.mp hdR).1
  have he : e ∈ s := (mem_sdiff.mp heR).1
  have hdV : ¬IsHullVertex s d := by
    intro h; exact (mem_sdiff.mp hdR).2 (mem_hullVertices.mpr h)
  have heV : ¬IsHullVertex s e := by
    intro h; exact (mem_sdiff.mp heR).2 (mem_hullVertices.mpr h)
  have hda : d ≠ a := fun h => hdV (h ▸ haV)
  have hdb : d ≠ b := fun h => hdV (h ▸ hbV)
  have hdc : d ≠ c := fun h => hdV (h ▸ hcV)
  have hea : e ≠ a := fun h => heV (h ▸ haV)
  have heb : e ≠ b := fun h => heV (h ▸ hbV)
  have hec : e ≠ c := fun h => heV (h ▸ hcV)
  have hs_eq : s = {a, b, c, d, e} := s_eq_hull_union_pair s a b c d e hHset hRset
  have hoa : orient d e a ≠ 0 := hgp hd he ha hde hea hda
  have hob : orient d e b ≠ 0 := hgp hd he hb hde heb hdb
  have hoc : orient d e c ≠ 0 := hgp hd he hc hde hec hdc
  have hod0 : orient d e d = 0 := by unfold orient; ring
  have hoe0 : orient d e e = 0 := by unfold orient; ring
  have hneg_hull : orient d e a < 0 ∨ orient d e b < 0 ∨ orient d e c < 0 := by
    obtain ⟨⟨p, hp, hpneg⟩, _⟩ := both_sides_of_non_hull s d e hd he hde hgp hdV
    have hpmem : p ∈ ({a, b, c, d, e} : Finset P) := by rw [← hs_eq]; exact hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpmem
    rcases hpmem with hpa | hpb | hpc | hpd | hpe
    · subst hpa; exact Or.inl hpneg
    · subst hpb; exact Or.inr (Or.inl hpneg)
    · subst hpc; exact Or.inr (Or.inr hpneg)
    · subst hpd; linarith [hod0, hpneg]
    · subst hpe; linarith [hoe0, hpneg]
  have hpos_hull : 0 < orient d e a ∨ 0 < orient d e b ∨ 0 < orient d e c := by
    obtain ⟨_, ⟨p, hp, hppos⟩⟩ := both_sides_of_non_hull s d e hd he hde hgp hdV
    have hpmem : p ∈ ({a, b, c, d, e} : Finset P) := by rw [← hs_eq]; exact hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpmem
    rcases hpmem with hpa | hpb | hpc | hpd | hpe
    · subst hpa; exact Or.inl hppos
    · subst hpb; exact Or.inr (Or.inl hppos)
    · subst hpc; exact Or.inr (Or.inr hppos)
    · subst hpd; linarith [hod0, hppos]
    · subst hpe; linarith [hoe0, hppos]
  have sa : orient d e a < 0 ∨ 0 < orient d e a := lt_or_gt_of_ne hoa
  have sb : orient d e b < 0 ∨ 0 < orient d e b := lt_or_gt_of_ne hob
  have sc : orient d e c < 0 ∨ 0 < orient d e c := lt_or_gt_of_ne hoc
  have majority :
      (0 < orient d e a * orient d e b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e) ∨
      (0 < orient d e a * orient d e c ∧ a ≠ d ∧ a ≠ e ∧ c ≠ d ∧ c ≠ e) ∨
      (0 < orient d e b * orient d e c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e) := by
    rcases sa with ha_neg | ha_pos
    · rcases sb with hb_neg | hb_pos
      · rcases sc with _hc_neg | _hc_pos
        · exact False.elim (by rcases hpos_hull with h | h | h <;> linarith)
        · exact Or.inl ⟨by nlinarith, Ne.symm hda, Ne.symm hea, Ne.symm hdb, Ne.symm heb⟩
      · rcases sc with hc_neg | hc_pos
        · exact Or.inr (Or.inl ⟨by nlinarith, Ne.symm hda, Ne.symm hea, Ne.symm hdc, Ne.symm hec⟩)
        · exact Or.inr (Or.inr ⟨by nlinarith, Ne.symm hdb, Ne.symm heb, Ne.symm hdc, Ne.symm hec⟩)
    · rcases sb with hb_neg | hb_pos
      · rcases sc with hc_neg | hc_pos
        · exact Or.inr (Or.inr ⟨by nlinarith, Ne.symm hdb, Ne.symm heb, Ne.symm hdc, Ne.symm hec⟩)
        · exact Or.inr (Or.inl ⟨by nlinarith, Ne.symm hda, Ne.symm hea, Ne.symm hdc, Ne.symm hec⟩)
      · rcases sc with _hc_neg | _hc_pos
        · exact Or.inl ⟨by nlinarith, Ne.symm hda, Ne.symm hea, Ne.symm hdb, Ne.symm heb⟩
        · exact False.elim (by rcases hneg_hull with h | h | h <;> linarith)
  rcases majority with hmaj | hmaj | hmaj
  · obtain ⟨hside, had, hae, hbd', hbe'⟩ := hmaj
    have hICP := inConvexPosition4_of_same_side_pair s a b d e haV hbV hd he
      had hae hbd' hbe' hde hab hside
    have h4 := card4_of_pairwise hab had hae hbd' hbe' hde
    obtain ⟨t, ht_sub, ht4, hci⟩ :=
      exists_convexIndependent_of_inConvexPosition4 a b d e h4 hICP
    refine ⟨t, ht_sub.trans ?_, ht4, hci⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨hside, had, hae, hcd', hce'⟩ := hmaj
    have hICP := inConvexPosition4_of_same_side_pair s a c d e haV hcV hd he
      had hae hcd' hce' hde hac hside
    have h4 := card4_of_pairwise hac had hae hcd' hce' hde
    obtain ⟨t, ht_sub, ht4, hci⟩ :=
      exists_convexIndependent_of_inConvexPosition4 a c d e h4 hICP
    refine ⟨t, ht_sub.trans ?_, ht4, hci⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · obtain ⟨hside, hbd', hbe', hcd', hce'⟩ := hmaj
    have hICP := inConvexPosition4_of_same_side_pair s b c d e hbV hcV hd he
      hbd' hbe' hcd' hce' hde hbc hside
    have h4 := card4_of_pairwise hbc hbd' hbe' hcd' hce' hde
    obtain ⟨t, ht_sub, ht4, hci⟩ :=
      exists_convexIndependent_of_inConvexPosition4 b c d e h4 hICP
    refine ⟨t, ht_sub.trans ?_, ht4, hci⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

/-- Full ES(3)=5: any 5-point GP set has a convex-independent 4-subset. -/
theorem es_three_eq_five : EsThreeEqFiveStatement := by
  intro s hcard hgp
  have h3 : 3 ≤ (hullVertices s).card :=
    hullVertices_card_ge_three_of_gp s (by omega : 3 ≤ s.card) hgp
  by_cases hge4 : 4 ≤ (hullVertices s).card
  · exact es_three_eq_five_of_hull_card_ge_four s hcard hgp hge4
  · have hH3 : (hullVertices s).card = 3 := by omega
    exact es_three_eq_five_of_hull_card_eq_three s hcard hgp hH3



/-! ## Sanity -/

example : orient ((0 : ℝ), 0) (1, 0) (0, 1) = 1 := by
  unfold orient; norm_num

example : orient ((0 : ℝ), 0) (1, 0) (2, 0) = 0 := by
  unfold orient; norm_num

end ProofLab.HappyEndingES3
