/-
Vosper's inverse Cauchy–Davenport theorem (formalize-only).

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 has `ZMod.min_le_card_add` (direct Cauchy–Davenport;
**do not re-prove; never cite CD as this gap**), Finset pointwise `+`,
`addDysonETransform` / `mulDysonETransform.card` (cardinality invariance),
and `ThreeAPFree` as a **different** predicate (3-AP-free, not `IsAP`).
ZERO Vosper / `IsAP` / inverse-CD / critical-pair theorem under `Mathlib/`
or `Archive/`. Completing the namesake is the gap.

Pin: `catalog/problems/vosper-cauchy-davenport/STATEMENT.md` (OPE-793;
Scout OPE-788 prime; Director OPE-792). Encoding: `Finset (ZMod p)` +
pointwise `+` + new `IsAP`. Zero `sorry`. Do not import `Archive.*`.

This is **not** Cauchy–Davenport (`ZMod.min_le_card_add` already Mathlib).
This is **not** EGZ (`Combinatorics/Additive/ErdosGinzburgZiv.lean`).
This is **not** combinatorial Nullstellensatz
(`ProofLab/CombinatorialNullstellensatz.lean`, PR #71).
This is **not** Mann / Schnirelmann / Erdős–Heilbronn / additive Kneser /
Freiman `3k-4`.
This is **not** `ThreeAPFree` (do not relabel).
This is **not** heron-formula / bipartite-odd-cycle / euclid-euler-perfect /
moore / stirling / KST / pentagonal / sunflower / Kruskal–Katona / Oddtown /
Cayley / Mycielski / Friendship / Havel / Menger / greedy / Brooks /
Dilworth / Eulerian / König / Dirac / EKR.
Leave OPE-403 alone.

v1 is `ℤ/pℤ` only (`p` prime), matching `ZMod.min_le_card_add`.
Level A `isAP_sum_card` recovers CD equality for APs of the same difference
and is **not** labelled Vosper.
Level B namesake `vosper` is **not** landed this heartbeat (e-transform
inverse timebox; unguarded pin is false for a singleton + non-AP partner).
Do not sorry-in the inverse.

Transcribed classical argument (Vosper, J. London Math. Soc. 31 (1956)
200–205; Tao–Vu inverse CD). No novelty claim.
-/
import Mathlib.Combinatorics.SetFamily.CauchyDavenport
import Mathlib.Tactic

set_option linter.unusedVariables false

open Finset
open scoped Pointwise

namespace ProofLab.Vosper

variable {p : ℕ}

/-! ## Encoding: `IsAP` (not `ThreeAPFree`) -/

/-- `s` is a (possibly singleton) arithmetic progression with difference `d`.
Singletons are APs for every `d` (load-bearing). Empty sets are APs.
This is **not** `ThreeAPFree`. -/
def IsAP (s : Finset (ZMod p)) (d : ZMod p) : Prop :=
  ∃ a, s = image (fun k : Fin s.card ↦ a + k.val • d) univ

/-- Consecutive residues `{0, 1, …, n−1}` in `ℤ/pℤ`. Glue, not namesake. -/
def interval (n : ℕ) : Finset (ZMod p) :=
  (range n).image (fun k : ℕ => (k : ZMod p))

/-- Explicit AP `{a, a+d, …, a+(n-1)d}`. -/
def ap (a d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (range n).image (fun k : ℕ => a + k • d)

/-! ## Glue: Fin-image vs range-image -/

lemma image_fin_eq_image_range {α : Type*} [DecidableEq α] (n : ℕ) (f : ℕ → α) :
    (univ : Finset (Fin n)).image (fun k ↦ f k.val) = (range n).image f := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

lemma isAP_iff {s : Finset (ZMod p)} {d : ZMod p} :
    IsAP s d ↔ ∃ a, s = ap a d s.card := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [ap, ← image_fin_eq_image_range]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [ap, ← image_fin_eq_image_range] at ha
    exact ha

/-! ## Singletons are APs (load-bearing) -/

lemma isAP_singleton (a d : ZMod p) : IsAP ({a} : Finset (ZMod p)) d := by
  refine ⟨a, ?_⟩
  have hcard : ({a} : Finset (ZMod p)).card = 1 := card_singleton a
  rw [hcard]
  ext x
  simp only [mem_image, mem_univ, true_and, mem_singleton]
  constructor
  · rintro rfl
    refine ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩
    simp
  · rintro ⟨k, rfl⟩
    have : k.val = 0 := Nat.lt_one_iff.mp k.isLt
    simp [this]

lemma isAP_of_card_eq_one {s : Finset (ZMod p)} {d : ZMod p} (h : s.card = 1) :
    IsAP s d := by
  obtain ⟨a, rfl⟩ := card_eq_one.mp h
  exact isAP_singleton a d

/-- Difference `0` forces a singleton (or empty). -/
lemma card_le_one_of_isAP_zero {s : Finset (ZMod p)} (h : IsAP s (0 : ZMod p)) :
    s.card ≤ 1 := by
  obtain ⟨a, ha⟩ := isAP_iff.mp h
  have : s ⊆ {a} := by
    intro x hx
    rw [ha] at hx
    simp only [ap, mem_image, mem_range, mem_singleton] at hx ⊢
    obtain ⟨k, _, rfl⟩ := hx
    simp
  exact (card_le_card this).trans_eq (card_singleton a)

/-! ## Interval arithmetic in `ℤ/pℤ` -/

lemma injOn_natCast_range [NeZero p] {n : ℕ} (hn : n ≤ p) :
    Set.InjOn (fun k : ℕ ↦ (k : ZMod p)) (range n) := by
  intro a ha b hb h
  simp only [mem_coe, mem_range] at ha hb
  have ha' : a < p := lt_of_lt_of_le ha hn
  have hb' : b < p := lt_of_lt_of_le hb hn
  simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using
    congrArg ZMod.val h

lemma interval_card [NeZero p] {n : ℕ} (hn : n ≤ p) :
    (interval (p := p) n).card = n := by
  rw [interval, card_image_of_injOn (injOn_natCast_range hn), card_range]

lemma interval_eq_univ [NeZero p] : interval (p := p) p = univ :=
  eq_univ_of_card _ (by rw [interval_card le_rfl, ZMod.card])

lemma mem_interval {n : ℕ} {x : ZMod p} :
    x ∈ interval (p := p) n ↔ ∃ k < n, (k : ZMod p) = x := by
  simp [interval, mem_image, mem_range]

/-- Split `k < n+m−1` as `i+j` with `i < n`, `j < m`. Needs `n,m ≥ 1`. -/
lemma exists_add_of_lt {n m k : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hk : k < n + m - 1) : ∃ i j, i < n ∧ j < m ∧ i + j = k := by
  by_cases h : k < n
  · exact ⟨k, 0, h, hm, Nat.add_zero k⟩
  · refine ⟨n - 1, k - (n - 1), Nat.sub_one_lt (ne_of_gt hn), ?_, by omega⟩
    omega

lemma interval_add [NeZero p] {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hn' : n ≤ p) (hm' : m ≤ p) :
    interval (p := p) n + interval (p := p) m =
      interval (p := p) (min p (n + m - 1)) := by
  ext x
  constructor
  · intro hx
    rcases mem_add.mp hx with ⟨y, hy, z, hz, hsum⟩
    rcases mem_interval.mp hy with ⟨i, hi, rfl⟩
    rcases mem_interval.mp hz with ⟨j, hj, rfl⟩
    subst hsum
    by_cases hle : n + m - 1 ≤ p
    · rw [min_eq_right hle, ← Nat.cast_add]
      exact mem_interval.mpr ⟨i + j, by omega, rfl⟩
    · rw [min_eq_left (le_of_not_le hle), interval_eq_univ]
      exact mem_univ _
  · intro hx
    rcases mem_interval.mp hx with ⟨k, hk, rfl⟩
    have hk' : k < n + m - 1 := lt_of_lt_of_le hk (min_le_right _ _)
    obtain ⟨i, j, hi, hj, hij⟩ := exists_add_of_lt hn hm hk'
    have hx' : (k : ZMod p) = (i : ZMod p) + (j : ZMod p) := by
      rw [← hij, Nat.cast_add]
    rw [hx']
    exact add_mem_add (mem_interval.mpr ⟨i, hi, rfl⟩)
      (mem_interval.mpr ⟨j, hj, rfl⟩)

/-! ## Translate / scale an AP -/

lemma ap_eq_add_left (a d : ZMod p) (n : ℕ) :
    ap a d n = {a} + ap 0 d n := by
  ext x
  constructor
  · intro hx
    rcases mem_image.mp hx with ⟨k, hk, rfl⟩
    refine mem_add.mpr ⟨a, mem_singleton_self a, k • d, ?_, by simp⟩
    exact mem_image.mpr ⟨k, hk, by simp⟩
  · intro hx
    rcases mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    simp only [mem_singleton] at hy
    subst y
    rcases mem_image.mp hz with ⟨k, hk, rfl⟩
    exact mem_image.mpr ⟨k, hk, by simp⟩

lemma ap_zero_eq_image_mul (d : ZMod p) (n : ℕ) :
    ap 0 d n = (interval (p := p) n).image fun x ↦ d * x := by
  ext x
  constructor
  · intro hx
    rcases mem_image.mp hx with ⟨k, hk, rfl⟩
    refine mem_image.mpr ⟨(k : ZMod p), mem_interval.mpr ⟨k, mem_range.mp hk, rfl⟩, ?_⟩
    simp [nsmul_eq_mul, mul_comm]
  · intro hx
    rcases mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_interval.mp hy with ⟨k, hk, rfl⟩
    refine mem_image.mpr ⟨k, mem_range.mpr hk, ?_⟩
    simp [nsmul_eq_mul, mul_comm]

lemma card_add_left (a : ZMod p) (s : Finset (ZMod p)) :
    ({a} + s).card = s.card := by
  have h : {a} + s = s.image fun x ↦ a + x := by
    ext z
    constructor
    · intro hz
      rcases mem_add.mp hz with ⟨y, hy, w, hw, rfl⟩
      simp only [mem_singleton] at hy
      subst y
      exact mem_image.mpr ⟨w, hw, rfl⟩
    · intro hz
      rcases mem_image.mp hz with ⟨w, hw, rfl⟩
      exact add_mem_add (mem_singleton_self a) hw
  rw [h]
  exact card_image_of_injective s (add_right_injective a)

lemma card_image_mul_of_ne_zero [Fact p.Prime] {d : ZMod p} (hd : d ≠ 0)
    (s : Finset (ZMod p)) :
    (s.image fun x ↦ d * x).card = s.card :=
  card_image_of_injective s (mul_right_injective₀ hd)

lemma ap_card_of_ne_zero [Fact p.Prime] [NeZero p] {a d : ZMod p} {n : ℕ}
    (hd : d ≠ 0) (hn : n ≤ p) : (ap a d n).card = n := by
  rw [ap_eq_add_left, card_add_left, ap_zero_eq_image_mul,
    card_image_mul_of_ne_zero hd, interval_card hn]

lemma isAP_ap {a d : ZMod p} {n : ℕ} (h : (ap a d n).card = n) :
    IsAP (ap a d n) d :=
  isAP_iff.mpr ⟨a, congrArg (ap a d) h.symm ▸ rfl⟩

lemma singleton_add_add (a b : ZMod p) (s t : Finset (ZMod p)) :
    ({a} + s) + ({b} + t) = {a + b} + (s + t) := by
  ext x
  constructor
  · intro hx
    rcases mem_add.mp hx with ⟨u, hu, v, hv, rfl⟩
    rcases mem_add.mp hu with ⟨y, hy, s', hs', rfl⟩
    rcases mem_add.mp hv with ⟨z, hz, t', ht', rfl⟩
    simp only [mem_singleton] at hy hz
    subst y; subst z
    have : a + s' + (b + t') = a + b + (s' + t') := by
      abel
    rw [this]
    exact add_mem_add (mem_singleton_self _) (add_mem_add hs' ht')
  · intro hx
    rcases mem_add.mp hx with ⟨y, hy, w, hw, rfl⟩
    simp only [mem_singleton] at hy
    subst y
    rcases mem_add.mp hw with ⟨s', hs', t', ht', rfl⟩
    have : a + b + (s' + t') = a + s' + (b + t') := by
      abel
    rw [this]
    exact add_mem_add (add_mem_add (mem_singleton_self a) hs')
      (add_mem_add (mem_singleton_self b) ht')

lemma image_mul_add (d : ZMod p) (s t : Finset (ZMod p)) :
    (s + t).image (fun x ↦ d * x) =
      s.image (fun x ↦ d * x) + t.image (fun x ↦ d * x) := by
  ext x
  constructor
  · intro hx
    rcases mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases mem_add.mp hy with ⟨u, hu, v, hv, rfl⟩
    rw [mul_add]
    exact add_mem_add (mem_image.mpr ⟨u, hu, rfl⟩) (mem_image.mpr ⟨v, hv, rfl⟩)
  · intro hx
    rcases mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases mem_image.mp hy with ⟨u, hu, rfl⟩
    rcases mem_image.mp hz with ⟨v, hv, rfl⟩
    rw [← mul_add]
    exact mem_image.mpr ⟨u + v, add_mem_add hu hv, rfl⟩

lemma ap_zero_add [Fact p.Prime] [NeZero p] {d : ZMod p} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hn' : n ≤ p) (hm' : m ≤ p) :
    ap 0 d n + ap 0 d m = ap 0 d (min p (n + m - 1)) := by
  rw [ap_zero_eq_image_mul, ap_zero_eq_image_mul, ← image_mul_add, interval_add hn hm hn' hm',
    ← ap_zero_eq_image_mul]

lemma ap_add [Fact p.Prime] [NeZero p] {a b d : ZMod p} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hn' : n ≤ p) (hm' : m ≤ p) :
    ap a d n + ap b d m = {a + b} + ap 0 d (min p (n + m - 1)) := by
  rw [ap_eq_add_left a d n, ap_eq_add_left b d m, singleton_add_add,
    ap_zero_add hn hm hn' hm']

lemma card_ap_add [Fact p.Prime] [NeZero p] {a b d : ZMod p} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hn' : n ≤ p) (hm' : m ≤ p) (hd : d ≠ 0) :
    (ap a d n + ap b d m).card = min p (n + m - 1) := by
  rw [ap_add hn hm hn' hm', card_add_left, ap_zero_eq_image_mul,
    card_image_mul_of_ne_zero hd, interval_card (min_le_left _ _)]

lemma card_le_zmod (s : Finset (ZMod p)) [Fintype (ZMod p)] :
    s.card ≤ p :=
  (card_le_univ s).trans_eq (ZMod.card p)

/-! ## Level A — AP-extremal recovers CD equality (not labelled Vosper) -/

/-- If `s` and `t` are arithmetic progressions with the same difference,
then `|s+t| = min(p, |s|+|t|-1)`. Recovers equality in Cauchy–Davenport.
**Not** labelled Vosper. Uses `ZMod.min_le_card_add` only as the ambient
direct theorem (not re-proved). -/
theorem isAP_sum_card [Fact p.Prime] {s t : Finset (ZMod p)} {d : ZMod p}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hsAP : IsAP s d) (htAP : IsAP t d) :
    (s + t).card = min p (s.card + t.card - 1) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out (p := p.Prime))⟩
  have hn : 0 < s.card := hs.card_pos
  have hm : 0 < t.card := ht.card_pos
  have hn' : s.card ≤ p := card_le_zmod s
  have hm' : t.card ≤ p := card_le_zmod t
  obtain ⟨a, ha⟩ := isAP_iff.mp hsAP
  obtain ⟨b, hb⟩ := isAP_iff.mp htAP
  set n := s.card
  set m := t.card
  by_cases hd : d = 0
  · subst hd
    have hs1 : n = 1 :=
      le_antisymm (card_le_one_of_isAP_zero hsAP) (Nat.succ_le_iff.mpr hn)
    have ht1 : m = 1 :=
      le_antisymm (card_le_one_of_isAP_zero htAP) (Nat.succ_le_iff.mpr hm)
    obtain ⟨x, rfl⟩ := card_eq_one.mp (show s.card = 1 from hs1)
    obtain ⟨y, rfl⟩ := card_eq_one.mp (show t.card = 1 from ht1)
    have hsum : ({x} + {y} : Finset (ZMod p)) = {x + y} :=
      singleton_add_singleton x y
    have hmin : min p 1 = 1 :=
      min_eq_right (Nat.Prime.one_le (Fact.out (p := p.Prime)))
    simp [hsum, hs1, ht1, hmin]
  · change (s + t).card = min p (n + m - 1)
    rw [ha, hb]
    exact card_ap_add hn hm hn' hm' hd

/-! ## Level B residual — namesake not landed

The STATEMENT pin

```
theorem vosper ... ∃ d, IsAP s d ∧ IsAP t d
```

is **not** proved here (zero `sorry` / `admit` / custom axiom).

Residual:

1. Unguarded pin is false when `min(|s|,|t|)=1` and the other set is not
   an AP: `|s+t| = |s|+|t|-1` holds for any partner of a singleton, but
   `IsAP` of the partner is not forced. Classical Vosper requires
   `|s|,|t| ≥ 2` and typically `|s+t| ≤ p-2` (the `|s+t|=p-1` family has
   extra exceptional pairs). Singletons remain APs in `IsAP` (load-bearing
   on Level A); they are not a free inverse.
2. Standard e-transform inverse (Dyson / pair e-transforms until an
   interval; `addDysonETransform.card` invariance already Mathlib) was
   not completed this heartbeat. Do not sorry-in `vosper`.
3. Do not expand into Mann / Heilbronn / additive Kneser / Freiman `3k-4`.
-/

end ProofLab.Vosper
