import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import ProofLab.Ramsey

open SimpleGraph Finset
open ProofLab.Ramsey

namespace ProofLab.RamseyMulticolor

/-!
# Multicolour Ramsey number R(3,3,3) = 17  (formalize-only, OPE-461)

An edge **3-colouring** of the complete graph on `Fin n` is a symmetric function
`f : Fin n → Fin n → Fin 3` (diagonal unused).  A **monochromatic triangle** is a
triple of distinct vertices whose three pairwise colours agree.

## Main results (zero `sorry`)

* `r333_gt_16`: Greenwood–Gleason certificate on 16 vertices, `native_decide`.
* `r333_le_17`: every symmetric 3-edge-colouring of `K₁₇` has a mono triangle
  (pigeonhole deg ≥ 6 + `ramsey33_clique_inside_finset` pullback).
* `r333_eq_17`: both bounds.

Known-classical (Greenwood & Gleason 1955). **No novelty claim.**
-/

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/-! ## Definitions -/

/-- Monochromatic triangle under `f`. -/
def HasMonoTriangle {n k : ℕ} (f : Fin n → Fin n → Fin k) : Prop :=
  ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ f a b = f a c ∧ f a b = f b c

instance {n k : ℕ} (f : Fin n → Fin n → Fin k) : Decidable (HasMonoTriangle f) := by
  unfold HasMonoTriangle
  infer_instance

/-- Symmetry of an edge colouring. -/
def IsSymmetric {n k : ℕ} (f : Fin n → Fin n → Fin k) : Prop :=
  ∀ a b : Fin n, f a b = f b a

/-- Every `Fin 3` is `0`, `1`, or `2`. -/
lemma fin3_eq_zero_one_two (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
  | ⟨n + 3, h⟩ => omega

/-- Simple graph of edges of colour `c`. -/
def colorGraph {n : ℕ} (f : Fin n → Fin n → Fin 3) (c : Fin 3)
    (hsym : IsSymmetric f) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ f u v = c
  symm := by
    intro u v h
    exact ⟨h.1.symm, (hsym u v) ▸ h.2⟩
  loopless := fun u hu => (hu.1 rfl).elim

instance {n : ℕ} (f : Fin n → Fin n → Fin 3) (c : Fin 3) (hsym : IsSymmetric f) :
    DecidableRel (colorGraph f c hsym).Adj := by
  unfold colorGraph
  infer_instance

/-- Lex index of unordered pair `{a,b}` among pairs `i < j` on `Fin n`.
Same convention as the W(2,4)>34 witness string. -/
def edgeIndex {n : ℕ} (a b : Fin n) : ℕ :=
  let i := min a.val b.val
  let j := max a.val b.val
  i * (2 * n - i - 1) / 2 + (j - i - 1)

/-! ## Lower bound R(3,3,3) > 16 -/

/-- Greenwood–Gleason `F₂⁴` colouring of `K₁₆` as 120 digits over `{0,1,2}`,
lex order `i < j`. Scout OPE-458 certificate. -/
def witness16Digits : List ℕ :=
  [0,0,1,0,1,2,1,0,2,1,1,2,2,2,0,1,0,1,0,1,2,2,0,1,1,2,2,0,2,0,2,1,0,1,1,1,0,2,2,0,
   2,2,1,2,1,0,1,1,2,0,0,2,2,2,0,0,1,2,2,2,0,0,2,1,1,1,0,2,2,0,2,2,0,1,1,0,2,0,2,2,
   1,1,0,2,0,2,2,2,1,1,2,0,0,0,1,0,1,2,1,1,0,1,0,1,2,0,2,1,0,1,1,2,1,0,0,0,1,1,0,0]

/-- Colour at certificate index. -/
def certColor (i : ℕ) : Fin 3 :=
  ⟨(witness16Digits.getD i 0) % 3, Nat.mod_lt _ (by decide : 0 < 3)⟩

/-- Greenwood–Gleason colouring of `K₁₆`. Diagonal defaults to `0`. -/
def witness16 (a b : Fin 16) : Fin 3 :=
  if a = b then 0 else certColor (edgeIndex a b)

theorem witness16Digits_length : witness16Digits.length = 120 := by native_decide

/-- **R(3,3,3) > 16**: GG colouring of `K₁₆` has no monochromatic triangle. -/
theorem r333_gt_16 : ¬ HasMonoTriangle (witness16 : Fin 16 → Fin 16 → Fin 3) := by
  native_decide

theorem witness16_symmetric : IsSymmetric witness16 := by
  intro a b
  unfold witness16 edgeIndex
  by_cases h : a = b
  · simp [h]
  · have hmin : min a.val b.val = min b.val a.val := min_comm _ _
    have hmax : max a.val b.val = max b.val a.val := max_comm _ _
    simp [h, Ne.symm h, hmin, hmax]

/-! ## Upper bound helpers -/

theorem hasMonoTriangle_of_colorClique {n : ℕ} (f : Fin n → Fin n → Fin 3)
    (hsym : IsSymmetric f) (c : Fin 3)
    (h : HasClique (colorGraph f c hsym) 3) : HasMonoTriangle f := by
  obtain ⟨s, hs⟩ := h
  rw [isNClique_iff] at hs
  have hcard : 3 ≤ s.card := Nat.le_of_eq hs.2.symm
  rcases extract3 hcard with ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩
  have eab : (colorGraph f c hsym).Adj a b := hs.1 ha hb hab
  have ead : (colorGraph f c hsym).Adj a d := hs.1 ha hd had
  have ebd : (colorGraph f c hsym).Adj b d := hs.1 hb hd hbd
  refine ⟨a, b, d, hab, had, hbd, ?_, ?_⟩
  · exact eab.2.trans ead.2.symm
  · exact eab.2.trans ebd.2.symm

theorem monoTriangle_of_common_color {n : ℕ} (f : Fin n → Fin n → Fin 3)
    {v a b : Fin n} {c : Fin 3}
    (hva : f v a = c) (hvb : f v b = c) (hab : f a b = c)
    (hva_ne : v ≠ a) (hvb_ne : v ≠ b) (hab_ne : a ≠ b) :
    HasMonoTriangle f :=
  ⟨v, a, b, hva_ne, hvb_ne, hab_ne, hva.trans hvb.symm, hva.trans hab.symm⟩

/-- The other two colours given forbidden colour `c`. -/
def otherColor1 (c : Fin 3) : Fin 3 := if c = 0 then 1 else 0
def otherColor2 (c : Fin 3) : Fin 3 := if c = 2 then 1 else 2

/-- If `x ≠ c` and `x ≠ otherColor1 c` then `x = otherColor2 c`. -/
lemma eq_otherColor2_of_ne {x c : Fin 3}
    (hx_ne_c : x ≠ c) (hx_ne_c1 : x ≠ otherColor1 c) :
    x = otherColor2 c := by
  unfold otherColor1 otherColor2 at *
  rcases fin3_eq_zero_one_two c with rfl | rfl | rfl
  · rcases fin3_eq_zero_one_two x with rfl | rfl | rfl <;> simp_all
  · rcases fin3_eq_zero_one_two x with rfl | rfl | rfl <;> simp_all
  · rcases fin3_eq_zero_one_two x with rfl | rfl | rfl <;> simp_all

/-- No edge of colour `c` inside a 6-set ⇒ R(3,3) on the other two colours. -/
theorem monoTriangle_of_two_color_finset {n : ℕ} (f : Fin n → Fin n → Fin 3)
    (hsym : IsSymmetric f) (c : Fin 3)
    (S : Finset (Fin n)) (hS : S.card = 6)
    (hno_c : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b ≠ c) :
    HasMonoTriangle f := by
  classical
  let c1 := otherColor1 c
  let c2 := otherColor2 c
  let G := colorGraph f c1 hsym
  rcases ramsey33_clique_inside_finset G S hS with hred | hblue
  · rcases hred with ⟨t, _, ht⟩
    exact hasMonoTriangle_of_colorClique f hsym c1 ⟨t, ht⟩
  · rcases hblue with ⟨t, ht_sub, ht⟩
    rw [isNClique_iff] at ht
    have hcard : 3 ≤ t.card := Nat.le_of_eq ht.2.symm
    rcases extract3 hcard with ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩
    have haS : a ∈ S := ht_sub ha
    have hbS : b ∈ S := ht_sub hb
    have hdS : d ∈ S := ht_sub hd
    have eab : Gᶜ.Adj a b := ht.1 ha hb hab
    have ead : Gᶜ.Adj a d := ht.1 ha hd had
    have ebd : Gᶜ.Adj b d := ht.1 hb hd hbd
    have fab : f a b = c2 := by
      have hab_ne : a ≠ b := eab.1
      have hnot_c1 : ¬ (a ≠ b ∧ f a b = c1) := eab.2
      have hnot_c1' : f a b ≠ c1 := fun hcol => hnot_c1 ⟨hab_ne, hcol⟩
      have hnot_c : f a b ≠ c := hno_c a haS b hbS hab_ne
      exact eq_otherColor2_of_ne hnot_c hnot_c1'
    have fad : f a d = c2 := by
      have had_ne : a ≠ d := ead.1
      have hnot_c1 : ¬ (a ≠ d ∧ f a d = c1) := ead.2
      have hnot_c1' : f a d ≠ c1 := fun hcol => hnot_c1 ⟨had_ne, hcol⟩
      have hnot_c : f a d ≠ c := hno_c a haS d hdS had_ne
      exact eq_otherColor2_of_ne hnot_c hnot_c1'
    have fbd : f b d = c2 := by
      have hbd_ne : b ≠ d := ebd.1
      have hnot_c1 : ¬ (b ≠ d ∧ f b d = c1) := ebd.2
      have hnot_c1' : f b d ≠ c1 := fun hcol => hnot_c1 ⟨hbd_ne, hcol⟩
      have hnot_c : f b d ≠ c := hno_c b hbS d hdS hbd_ne
      exact eq_otherColor2_of_ne hnot_c hnot_c1'
    refine ⟨a, b, d, hab, had, hbd, fab.trans fad.symm, fab.trans fbd.symm⟩

/-- Deg ≥ 6 in colour `c` at `v` forces a monochromatic triangle. -/
theorem monoTriangle_of_deg_ge_six {n : ℕ} (f : Fin n → Fin n → Fin 3)
    (hsym : IsSymmetric f) (v : Fin n) (c : Fin 3)
    (hdeg : 6 ≤ ((univ : Finset (Fin n)).filter (fun u => u ≠ v ∧ f v u = c)).card) :
    HasMonoTriangle f := by
  classical
  set N : Finset (Fin n) :=
    (univ : Finset (Fin n)).filter (fun u => u ≠ v ∧ f v u = c)
  obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hdeg
  by_cases h_c_edge : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a b = c
  · rcases h_c_edge with ⟨a, haS, b, hbS, hab, habc⟩
    have haN : a ∈ N := hSsub haS
    have hbN : b ∈ N := hSsub hbS
    have haN' := mem_filter.mp haN
    have hbN' := mem_filter.mp hbN
    exact monoTriangle_of_common_color f haN'.2.2 hbN'.2.2 habc
      haN'.2.1.symm hbN'.2.1.symm hab
  · have hno_c : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b ≠ c := by
      intro a ha b hb hab hcol
      exact h_c_edge ⟨a, ha, b, hb, hab, hcol⟩
    exact monoTriangle_of_two_color_finset f hsym c S hScard hno_c

lemma pigeon_three_of_sum_eq_sixteen {a b c : ℕ} (h : a + b + c = 16) :
    6 ≤ a ∨ 6 ≤ b ∨ 6 ≤ c := by omega

/-- Colour-neighbourhood of `v` in colour `c`. -/
def colorNhd {n : ℕ} (f : Fin n → Fin n → Fin 3) (v : Fin n) (c : Fin 3) :
    Finset (Fin n) :=
  univ.filter (fun u => u ≠ v ∧ f v u = c)

lemma colorNhd_disjoint {n : ℕ} (f : Fin n → Fin n → Fin 3) (v : Fin n)
    {c₁ c₂ : Fin 3} (hne : c₁ ≠ c₂) :
    Disjoint (colorNhd f v c₁) (colorNhd f v c₂) := by
  rw [disjoint_left]
  intro u hu1 hu2
  have h1 : f v u = c₁ := (mem_filter.mp hu1).2.2
  have h2 : f v u = c₂ := (mem_filter.mp hu2).2.2
  exact hne (h1.symm.trans h2)

lemma colorNhd_union_eq_erase {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin 3)
    (v : Fin n) :
    colorNhd f v 0 ∪ colorNhd f v 1 ∪ colorNhd f v 2 = univ.erase v := by
  ext u
  by_cases hv : u = v
  · subst u
    simp [colorNhd]
  · constructor
    · intro
      simp [mem_erase, hv]
    · intro
      have _ : u ∈ (univ : Finset (Fin n)) := mem_univ u
      simp only [mem_union, colorNhd, mem_filter, mem_univ, true_and]
      rcases fin3_eq_zero_one_two (f v u) with h0 | h1 | h2
      · exact Or.inl (Or.inl ⟨hv, h0⟩)
      · exact Or.inl (Or.inr ⟨hv, h1⟩)
      · exact Or.inr ⟨hv, h2⟩

lemma colorNhd_card_sum {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin 3)
    (v : Fin n) :
    (colorNhd f v 0).card + (colorNhd f v 1).card + (colorNhd f v 2).card =
      n - 1 := by
  have d01 := colorNhd_disjoint f v (by decide : (0 : Fin 3) ≠ 1)
  have d02 := colorNhd_disjoint f v (by decide : (0 : Fin 3) ≠ 2)
  have d12 := colorNhd_disjoint f v (by decide : (1 : Fin 3) ≠ 2)
  have d0_12 : Disjoint (colorNhd f v 0) (colorNhd f v 1 ∪ colorNhd f v 2) := by
    rw [disjoint_union_right]; exact ⟨d01, d02⟩
  have hunion := colorNhd_union_eq_erase f v
  have hassoc :
      colorNhd f v 0 ∪ colorNhd f v 1 ∪ colorNhd f v 2 =
        colorNhd f v 0 ∪ (colorNhd f v 1 ∪ colorNhd f v 2) := by
    ext x; simp [or_assoc]
  have h1 :
      (colorNhd f v 0 ∪ (colorNhd f v 1 ∪ colorNhd f v 2)).card =
        (colorNhd f v 0).card + (colorNhd f v 1 ∪ colorNhd f v 2).card :=
    card_union_of_disjoint d0_12
  have h2 :
      (colorNhd f v 1 ∪ colorNhd f v 2).card =
        (colorNhd f v 1).card + (colorNhd f v 2).card :=
    card_union_of_disjoint d12
  have h3 :
      (colorNhd f v 0 ∪ colorNhd f v 1 ∪ colorNhd f v 2).card =
        (univ.erase v).card := by rw [hunion]
  have h4 : (univ.erase v : Finset (Fin n)).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
  -- card sums associate as (a+b)+c; rewrite via a+(b+c) to apply the pairwise unions
  have happ :
      (colorNhd f v 0).card + (colorNhd f v 1).card + (colorNhd f v 2).card =
        (colorNhd f v 0).card + ((colorNhd f v 1).card + (colorNhd f v 2).card) := by
    ac_rfl
  rw [happ, ← h2, ← h1, ← hassoc, h3, h4]

/-- **R(3,3,3) ≤ 17**. -/
theorem r333_le_17 (f : Fin 17 → Fin 17 → Fin 3) (hsym : IsSymmetric f) :
    HasMonoTriangle f := by
  classical
  let v : Fin 17 := 0
  have hcard := colorNhd_card_sum f v
  -- n - 1 = 16
  have hcard' :
      (colorNhd f v 0).card + (colorNhd f v 1).card + (colorNhd f v 2).card =
        16 := by
    simpa using hcard
  have hpig :
      6 ≤ (colorNhd f v 0).card ∨
        6 ≤ (colorNhd f v 1).card ∨ 6 ≤ (colorNhd f v 2).card :=
    pigeon_three_of_sum_eq_sixteen hcard'
  rcases hpig with h0 | h1 | h2
  · exact monoTriangle_of_deg_ge_six f hsym v 0 (by simpa [colorNhd] using h0)
  · exact monoTriangle_of_deg_ge_six f hsym v 1 (by simpa [colorNhd] using h1)
  · exact monoTriangle_of_deg_ge_six f hsym v 2 (by simpa [colorNhd] using h2)

/-- **R(3,3,3) = 17** as paired bounds. -/
theorem r333_eq_17 :
    (¬ HasMonoTriangle (witness16 : Fin 16 → Fin 16 → Fin 3)) ∧
      (∀ f : Fin 17 → Fin 17 → Fin 3, IsSymmetric f → HasMonoTriangle f) :=
  ⟨r333_gt_16, r333_le_17⟩

end ProofLab.RamseyMulticolor
