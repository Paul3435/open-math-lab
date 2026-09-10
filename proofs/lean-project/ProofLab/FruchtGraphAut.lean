/-
Graph automorphism type of named small graphs — Level A only
(`Aut(K₁)` unique / `Aut(P₁)` unique / `pathGraph 3` endpoint-swap
`≠` refl, optional `Aut(K₂)` swap via `Iso.completeGraph`).
**Not labelled Frucht / Cayley / Aut(Kₙ)≅Sₙ.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `SimpleGraph.Iso` / `≃g` /
`pathGraph` / `completeGraph` / `Iso.completeGraph` / `RelIso.refl`
as **infra**. ZERO named Frucht theorem / `frucht` / `Frucht` /
`GraphAut` / `automorphismGroup` under `Mathlib/` or `Archive/` or
`ProofLab/`. Completing the Level A unique Aut on `K₁` / `P₁` plus
a non-identity Aut of `P₃` is the gap this ticket lands. The Level B
namesake `frucht_graph_aut` (every finite group is Aut of some
finite simple graph) is **out of this ticket** and is **not**
sorry-ed. Cayley-graph gadgets / GRR / `Aut(K_n) ≅ S_n` as namesake
are residual of this id.

Pin: `catalog/problems/frucht-graph-aut/STATEMENT.md`
(OPE-1300; Scout OPE-1294 RECOMMENDED PRIME; Director OPE-1299).
Encoding: `GraphAut G := G ≃g G` / Mathlib `pathGraph` /
`completeGraph`. Zero `sorry`. Do not import `Archive.*`.

This is **not** `SimpleGraph.Iso` (`Maps.lean` L215) / `≃g` /
`RelIso.refl` / `Iso.comp` — already Mathlib. **USE, do not
re-prove; do not cite as Frucht.**
This is **not** `Iso.completeGraph` (`Maps.lean` L544) as namesake
— DIFFERENT type-equivalence of complete graphs. **USE glue; do
not re-prove; do not cite as Frucht.**
This is **not** `completeGraph` (`Basic.lean` L144) /
`pathGraph` (`Hasse.lean` L94) / `pathGraph_two_eq_top` L108 —
already Mathlib. **USE, do not re-prove.**
This is **not** `LinearEquiv.automorphismGroup` — DIFFERENT
module Aut. Do **not** cite as graph Aut; do **not** re-prove.
This is **not** Cayley's formula / Prüfer / Kirchhoff
(`ProofLab/CayleyTrees.lean`). Counting trees ≠ Aut groups.
This is **not** Cayley's theorem `Γ ↪ Perm`. Already-in
`Equiv.Perm` glue. Do **not** cite as Frucht.
This is **not** friendship / Moore cages
(`ProofLab/Friendship.lean` / `ProofLab/MooreDegreeGirth.lean`).
This is **not** Sabidussi box-product
(`ProofLab/SabidussiBoxProd.lean`, PR #139) / Hedetniemi.
This is **not** Petersen 1-factor
(`ProofLab/PetersenOneFactor.lean`, PR #135) / Tutte.
This is **not** platonic-solids (`ProofLab/PlatonicSolids.lean`,
PR #147) / Euler polyhedron / Coxeter `H₃`.
This is **not** egyptian-fractions
(`ProofLab/EgyptianFractions.lean`, PR #148) / Erdős–Straus.
This is **not** `proth-primality` (OPE-1294 leftover).
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is the automorphism-type of named small graphs via `≃g`:
unique Aut on `completeGraph (Fin 1)` / `pathGraph 1`, and
`pathGraph 3` admits the endpoint-swap iso (so Aut is at least
a 2-element set), **not labelled Frucht**. `SimpleGraph.Iso` is
load-bearing. `pathGraph` is load-bearing. Endpoint-swap on
`pathGraph 3` is load-bearing.

Level A: `Aut(K₁)` unique. `Aut(P₁)` unique. `pathGraph 3`
endpoint-swap `≠` refl. Optional extra: Aut of `K₂` contains
the swap via `Iso.completeGraph`. **Not** labelled Frucht.

Transcribed classical argument (R. Frucht, *Herstellung von
Graphen mit vorgegebener abstrakter Gruppe*, Compositio Math. 6
(1939) 239–250). Compact form: Wikipedia *Frucht's theorem*.
Type pin: `GraphAut := ≃g` / `pathGraph 3` flip.
`Iso.completeGraph` is a different complete-graph glue.
Cayley trees is a different consumed count. No novelty claim.
Default no claim.
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open SimpleGraph

namespace ProofLab.FruchtGraphAut

/-! ## Encoding: GraphAut := ≃g (not labelled Frucht) -/

/-- Graph automorphisms as Mathlib `SimpleGraph.Iso` / `≃g`.
Uses already-in `Iso`; does **not** re-prove it. Encoding;
**not** labelled Frucht. **Not** `LinearEquiv.automorphismGroup`. -/
abbrev GraphAut {V : Type*} (G : SimpleGraph V) := G ≃g G

/-! ## Level A: unique Aut on K₁ / P₁; P₃ endpoint-swap ≠ refl
(not labelled Frucht) -/

/-- `Aut(K₁)` is unique. Glue; **not** labelled Frucht. Uses
`completeGraph` / `≃g`; does **not** re-prove them. `Fin 1` is
load-bearing. -/
theorem aut_complete_fin_one :
    Subsingleton (GraphAut (completeGraph (Fin 1))) :=
  ⟨fun f g => DFunLike.ext f g fun x => Subsingleton.elim (f x) (g x)⟩

/-- `Aut(P₁)` is unique. Glue; **not** labelled Frucht. Uses
`pathGraph` / `≃g`; does **not** re-prove them. `pathGraph` is
load-bearing. -/
theorem aut_pathGraph_one :
    Subsingleton (GraphAut (pathGraph 1)) :=
  ⟨fun f g => DFunLike.ext f g fun x => Subsingleton.elim (f x) (g x)⟩

/-- Endpoint-swap on `pathGraph 3`: reverse `Fin 3`, which
preserves the two edges `0—1` and `1—2`. Uses Mathlib
`Fin.revPerm` / `pathGraph_adj`; does **not** re-prove
`pathGraph`. Glue; **not** labelled Frucht. -/
def pathGraphThreeFlip : GraphAut (pathGraph 3) where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro a b
    simp only [pathGraph_adj, Fin.revPerm_apply]
    fin_cases a <;> fin_cases b <;> simp

/-- The endpoint-swap is not `RelIso.refl`. So Aut of
`pathGraph 3` is at least a 2-element set. Glue; **not**
labelled Frucht. Endpoint-swap on `pathGraph 3` is
load-bearing. -/
theorem pathGraphThreeFlip_ne_refl :
    pathGraphThreeFlip ≠ RelIso.refl _ := by
  intro h
  have : (pathGraphThreeFlip : Fin 3 → Fin 3) 0 = 0 := by
    rw [h]; rfl
  simp [pathGraphThreeFlip] at this
  exact Fin.pos_iff_ne_zero.mp Fin.last_pos this

/-- Optional extra: Aut of `K₂` contains the transposition of
its two vertices, via `Iso.completeGraph` **USE**. Glue; **not**
labelled Frucht. **Not** `Aut(K_n) ≅ S_n` as namesake. -/
def completeFinTwoSwap : GraphAut (completeGraph (Fin 2)) :=
  Iso.completeGraph (Equiv.swap (0 : Fin 2) 1)

/-- The `K₂` swap is not `RelIso.refl`. Uses `Iso.completeGraph`;
does **not** re-prove it; does **not** cite it as Frucht. -/
theorem completeFinTwoSwap_ne_refl :
    completeFinTwoSwap ≠ RelIso.refl _ := by
  intro h
  have : (completeFinTwoSwap : Fin 2 → Fin 2) 0 = 0 := by
    rw [h]; rfl
  simp [completeFinTwoSwap, Iso.completeGraph] at this

/- Residual of this id (comment, **not** `sorry`):
Level B namesake `frucht_graph_aut` — every finite group is
the automorphism group of some finite undirected simple graph
(Frucht 1939). Out of this ticket. Do **not** prove
`frucht_graph_aut` / Cayley-graph gadgets / GRR /
`Aut(K_n) ≅ S_n` as namesake / `Iso.completeGraph` as namesake /
Cayley trees / Prüfer / Kirchhoff / Cayley's theorem `Γ ↪ Perm` /
friendship / Moore cages / Sabidussi box-product / Hedetniemi /
Petersen 1-factor / Tutte / `proth-primality` / Euler criterion
as namesake / Lucas–Lehmer / Wantzel / Pépin / Pocklington /
platonic-solids / Euler polyhedron / Coxeter `H₃` /
egyptian-fractions / Erdős–Straus /
`LinearEquiv.automorphismGroup` as namesake / `Equiv.Perm` as
namesake. -/

end ProofLab.FruchtGraphAut
