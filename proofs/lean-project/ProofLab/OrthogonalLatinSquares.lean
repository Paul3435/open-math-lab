/-
Named small-order Latin squares — Level A only (order 2 has no
orthogonal pair; order 3 affine pair `L_k(i,j)=i+k*j` for `k=1,2`
is Latin and orthogonal).
**Not labelled Euler / Graeco-Latin.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Fin` / `Function.Injective`
as **infra**. ZERO named `latinSquare` / `LatinSquare` /
`IsLatinSquare` / `orthogonalLatin` / `graecoLatin` / `GraecoLatin`
under `Mathlib/` or `Archive/` or `ProofLab/`. Completing the
Level A named small-order witnesses is the gap this ticket lands.
The Level B namesake `orthogonal_latin_squares` (MOLS exist iff
`n ≠ 2` and `n ≠ 6`) is **out of this ticket** and is **not**
sorry-ed. Euler officers / Bose–Shrikhande–Parker / `n−1` MOLS iff
projective plane / Lo Shu are residual of this id.

Pin: `catalog/problems/orthogonal-latin-squares/STATEMENT.md`
(OPE-1337; Scout OPE-1326 leftover; Director OPE-1336).
Encoding: `IsLatinSquare` / `Orthogonal` / `affineLatin` on
`Fin n → Fin n → Fin n`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `Fin` arithmetic / `Function.Injective` — already
Mathlib. **USE, do not re-prove; do not cite as Latin squares.**
This is **not** `Equiv.Perm` — DIFFERENT already-in row-permutation
glue. Do **not** re-prove; do **not** cite as Latin squares.
This is **not** `Configuration.ProjectivePlane`
(`Combinatorics/Configuration.lean` L329) — DIFFERENT already-in
incidence structure. Do **not** re-prove; do **not** cite as Latin
squares.
This is **not** `HasLines.card_le` (L211) — DIFFERENT already-in
de Bruijn–Erdős. Do **not** re-prove; do **not** cite as Latin
squares.
This is **not** Jordan canonical form
(`ProofLab/JordanCanonicalForm.lean`, consumed #156).
This is **not** Alcuin integer triangles
(`ProofLab/AlcuinIntegerTriangles.lean`, consumed #153).
This is **not** cannonball square-pyramid
(`ProofLab/CannonballSquarePyramid.lean`, consumed #154).
This is **not** Birkhoff–von Neumann
(`ProofLab/BirkhoffVonNeumann.lean`, consumed #123).
This is **not** Gale–Shapley (`ProofLab/GaleShapley.lean`, consumed
#126).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the Latin-square predicate on named small orders: order 2
has no orthogonal pair, and order 3 has the affine pair
`L_k(i,j) = i + k*j` for `k = 1, 2`, **not labelled Euler /
Graeco-Latin**. Row AND column injectivity is load-bearing (so a
row-Latin rectangle is **not** a Latin square). Pair map `(A, B)`
injective on `Fin n × Fin n` is load-bearing.

Level A: order-2 nonexistence / order-3 affine pair. Optional
extra: cyclic table of order 2 is Latin.
**Not** labelled Euler.

Transcribed classical argument (Euler 1782 Graeco-Latin squares;
affine plane of order 3). Compact form: Wikipedia *Graeco-Latin
square* / *Latin square*. Type pin: `IsLatinSquare` / `Orthogonal`
/ `affineLatin`. `ProjectivePlane` is a different already-in
incidence structure. `Equiv.Perm` is row-permutation glue.
No novelty claim. Default no claim.
-/
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open Function

namespace ProofLab.OrthogonalLatinSquares

/-! ## Encoding: Latin squares / orthogonality (not labelled Euler) -/

/-- An `n×n` Latin square: each row and each column is injective
(hence a permutation of `Fin n`). Encoding; **not** labelled Euler.
Load-bearing: row **and** column injectivity (a row-Latin rectangle
is **not** a Latin square). Does **not** re-prove
`Function.Injective`. -/
def IsLatinSquare {n : ℕ} (A : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Injective (A i)) ∧ (∀ j, Injective fun i => A i j)

/-- Two Latin squares of the same order are orthogonal when the
ordered pairs of symbols cover the product (equivalently: the pair
map is injective on the finite square). Encoding; **not** labelled
Euler / Graeco-Latin. Load-bearing: pair map injective on
`Fin n × Fin n`. -/
def Orthogonal {n : ℕ} (A B : Fin n → Fin n → Fin n) : Prop :=
  Injective fun p : Fin n × Fin n => (A p.1 p.2, B p.1 p.2)

/-- Affine filling `L_k(i,j) = i + k * j` on `Fin n`. Encoding;
**not** labelled Euler. Does **not** re-prove `Fin` arithmetic. -/
def affineLatin {n : ℕ} [NeZero n] (k : Fin n) (i j : Fin n) : Fin n :=
  i + k * j

/-! ## Level A: named small orders (not labelled Euler / Graeco-Latin) -/

/-- Cyclic (addition) table of any positive order is Latin.
Glue; **not** labelled Euler. -/
theorem isLatinSquare_affineLatin_one {n : ℕ} [NeZero n] :
    IsLatinSquare (affineLatin (1 : Fin n)) := by
  refine ⟨?row, ?col⟩
  · intro i a b h
    unfold affineLatin at h
    simp only [one_mul] at h
    exact add_left_cancel h
  · intro j a b h
    unfold affineLatin at h
    simp only [one_mul] at h
    exact add_right_cancel h

/-- Affine `L_1(i,j) = i + j` on `Fin 3` is Latin.
Glue; **not** labelled Euler. -/
theorem latin_cyclic_three : IsLatinSquare (affineLatin (1 : Fin 3)) :=
  isLatinSquare_affineLatin_one

/-- Multiplication by `2` is injective on `Fin 3`. Glue; **not**
labelled Euler. Does **not** re-prove `Function.Injective`. -/
theorem mul_two_injective_fin3 :
    Injective fun x : Fin 3 => (2 : Fin 3) * x := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp at h ⊢

/-- Affine `L_2(i,j) = i + 2 * j` on `Fin 3` is Latin.
Glue; **not** labelled Euler. -/
theorem latin_affine_two : IsLatinSquare (affineLatin (2 : Fin 3)) := by
  refine ⟨?row, ?col⟩
  · intro i a b h
    unfold affineLatin at h
    exact mul_two_injective_fin3 (add_left_cancel h)
  · intro j a b h
    unfold affineLatin at h
    exact add_right_cancel h

/-- Affine pair `L_1, L_2` on `Fin 3` is orthogonal.
Glue; **not** labelled Euler / Graeco-Latin.
Load-bearing: pair map injective on `Fin 3 × Fin 3`. -/
theorem orthogonal_affine_one_two :
    Orthogonal (affineLatin (1 : Fin 3)) (affineLatin (2 : Fin 3)) := by
  intro p q h
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  simp [affineLatin] at h
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp at h ⊢

/-- Order 3 admits the affine pair `L_1, L_2`: both Latin, and
orthogonal. Glue; **not** labelled Euler / Graeco-Latin. -/
theorem mols_order_three :
    IsLatinSquare (affineLatin (1 : Fin 3)) ∧
      IsLatinSquare (affineLatin (2 : Fin 3)) ∧
      Orthogonal (affineLatin (1 : Fin 3)) (affineLatin (2 : Fin 3)) :=
  ⟨latin_cyclic_three, latin_affine_two, orthogonal_affine_one_two⟩

/-- On `Fin 2`, the unique other element is `x + 1`. Glue. -/
theorem fin2_eq_add_one_of_ne {x y : Fin 2} (h : x ≠ y) : y = x + 1 := by
  fin_cases x <;> fin_cases y <;> simp_all

/-- Any Latin square of order 2 is the cyclic table of its `(0,0)`
entry (the unique reduced form up to symbol shift). Glue; **not**
labelled Euler. Load-bearing: row and column injectivity. -/
theorem latin_square_fin2_form {A : Fin 2 → Fin 2 → Fin 2}
    (hA : IsLatinSquare A) :
    A 0 1 = A 0 0 + 1 ∧ A 1 0 = A 0 0 + 1 ∧ A 1 1 = A 0 0 := by
  have h01 : A 0 1 = A 0 0 + 1 :=
    fin2_eq_add_one_of_ne ((hA.1 0).ne (by decide : (0 : Fin 2) ≠ 1))
  have h10 : A 1 0 = A 0 0 + 1 :=
    fin2_eq_add_one_of_ne ((hA.2 0).ne (by decide : (0 : Fin 2) ≠ 1))
  have h11 : A 1 1 = A 0 0 := by
    have : A 1 1 = A 1 0 + 1 :=
      fin2_eq_add_one_of_ne ((hA.1 1).ne (by decide : (0 : Fin 2) ≠ 1))
    rw [this, h10, add_assoc]
    simp
  exact ⟨h01, h10, h11⟩

/-- No two Latin squares of order 2 are orthogonal.
Glue; **not** labelled Euler. Load-bearing: pair map would have to
be injective on four cells, but the two diagonals collide. -/
theorem no_mols_order_two :
    ∀ A B : Fin 2 → Fin 2 → Fin 2,
      ¬ (IsLatinSquare A ∧ IsLatinSquare B ∧ Orthogonal A B) := by
  intro A B ⟨hA, hB, hO⟩
  obtain ⟨_, _, hA11⟩ := latin_square_fin2_form hA
  obtain ⟨_, _, hB11⟩ := latin_square_fin2_form hB
  have hval : (A 1 1, B 1 1) = (A 0 0, B 0 0) := by simp [hA11, hB11]
  have hidx : ((1 : Fin 2), (1 : Fin 2)) = (0, 0) := hO hval
  simp at hidx

/-- Optional extra: the cyclic table of order 2 is Latin
(exactly one reduced Latin square of order 2, up to the affine
encoding). Glue; **not** labelled Euler. -/
theorem latin_cyclic_two : IsLatinSquare (affineLatin (1 : Fin 2)) :=
  isLatinSquare_affineLatin_one

/-
Residual (Level B, **out of this ticket**, not sorry-ed):
`orthogonal_latin_squares` — a pair of MOLS of order `n` exists
iff `n ≠ 2` and `n ≠ 6` (Euler officers / Bose–Shrikhande–Parker).
Do **not** sorry the namesake.
Projective planes of every order / `n−1` MOLS / Lo Shu remain
residual of this id; do **not** expand them as extra namesakes.
Do **not** prove `orthogonal_latin_squares` / Euler officers /
Bose–Shrikhande–Parker / `n−1` MOLS iff projective plane /
`ProjectivePlane` as namesake / `Equiv.Perm` as namesake /
`HasLines.card_le` as namesake / Lo Shu / jordan-canonical-form /
`aeval_self_charpoly` as namesake / `exists_isNilpotent_isSemisimple`
as namesake / `IsJordan` as namesake / alcuin-integer-triangles /
integerTriangle / Heron leftover-revivals / cannonball-square-pyramid /
Lucas uniqueness / Watson / Faulhaber / sherman-morrison / Woodbury /
cauchy-binet / circulant-det / schur-product / hadamard-det /
frucht-graph-aut / Cayley-graph / GRR / `Aut(K_n)≅S_n` /
proth-primality / Euler criterion as namesake / Pépin / Pocklington /
platonic-solids / Euler polyhedron / Coxeter H3 / egyptian-fractions /
Erdos-Straus / british-flag / Napoleon / Simson / Viviani / fine-wilf /
graham-pollak / kraft-inequality / lagrange-quadratic-cf / lame-euclid /
farey_adjacent / gale_shapley / birkhoff_von_neumann / hook_length /
singleton_bound / bollobas / schwartz_zippel / Ore Level B / AES Level B /
ostrowski-q Level B / frobenius-real-division Level B /
noether-normalization Level B / krenn-gu / hou-zeng-pfc / sun-135.
Leave OPE-403 alone. Leave OPE-1195 alone.
Do **not** label theorems euler_* / graeco_*.
-/

end ProofLab.OrthogonalLatinSquares
