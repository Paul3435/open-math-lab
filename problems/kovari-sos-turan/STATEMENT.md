# Kővári–Sós–Turán — Zarankiewicz integer counting form (formalize-only)

**id:** `kovari-sos-turan`
**ticket:** OPE-740 Formalist (Scout OPE-735 prime; Director OPE-739; support OPE-734; post sunflower #70 + combinatorial Nullstellensatz #71)
**expected:** known-classical (Kővári–Sós–Turán 1954) — **no novelty claim**

## Why not classical / why formalize-only

Settled Zarankiewicz bound: a bipartite graph with parts `α`, `β` and no
`K_{s,t}` (s vertices in `α`, t vertices in `β`) satisfies the integer
double-counting inequality

```text
∑_{b : β} binom(deg b, s) ≤ (t − 1) · binom(|α|, s).
```

Not an open problem. Exact Zarankiewicz numbers `z(|α|,|β|;s,t)` are
**open for most parameters** and are **out of v1** — do not attack
them; do not describe this id as solving Zarankiewicz.

Mathlib v4.10.0 already has the **graph this theorem needs**:

- `SimpleGraph.completeBipartiteGraph` (`Basic.lean`)
- `neighborFinset` / `degree` / `commonNeighbors` (`Finite.lean`)
- `Nat.choose` (`Data/Nat/Choose/Basic.lean`)
- `Combinatorics.Enumerative.DoubleCounting`
- **Turán's theorem** (`SimpleGraph/Turan.lean`,
  `isTuranMaximal_iff_nonempty_iso_turanGraph`) — **different**
  theorem (clique-free / complete multipartite). **Never cite Turán
  as this gap** (OPE-25 negative control).

There is **no** Kővári–Sós–Turán / Zarankiewicz / `K_{s,t}`-extremal
ident anywhere under `Mathlib/` or `Archive/` (word-regexp this run
→ ZERO files). ProofLab has sunflower, Kruskal–Katona, Oddtown, EKR
— **different** theorems (set systems, not bipartite forbidden
subgraphs). This is **not** a re-prime of those ids, **not** a
Turán leftover, **not** Mantel (corollary of upstream Turán).

Do **not** describe an attack as discovering the KST lemma.
Do **not** expand into the real-exponent edge form, Erdős–Stone,
ex(n, C₄) tables, or non-bipartite `K_{s,t}`-free graphs.

## Pinned convention (exact)

**Bipartite pin:** `G : SimpleGraph (α ⊕ β)` with **no internal
edges** (equivalently `G ≤ completeBipartiteGraph α β`). Do **not**
use `Colorable 2` as a substitute without identifying the parts
(König already consumed `Colorable 2` as `ν=τ`).

**Forbidden subgraph pin:** `NoKst G s t` means every `s`-set of
**left** vertices (`α`) has at most `t − 1` common neighbours on the
**right** (`β`). That is exactly “no `K_{s,t}` with the s-side in
`α` and the t-side in `β`.”

**v1 is the integer counting form.** The classical real-exponent
bound `e ≤ (t−1)^{1/s} |β| |α|^{1−1/s} + (s−1)|β|` is a convexity /
Hölder corollary — stretch **out of v1**, not a leftover re-prime.
Exact Zarankiewicz values are **out of v1**.

```text
def IsBipartiteSum {α β : Type*} (G : SimpleGraph (α ⊕ β)) : Prop :=
  (∀ a a' : α, ¬ G.Adj (.inl a) (.inl a')) ∧
  (∀ b b' : β, ¬ G.Adj (.inr b) (.inr b'))

def NoKst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj] (s t : ℕ) : Prop :=
  ∀ S : Finset α, S.card = s →
    (Finset.univ.filter (fun b : β => ∀ a ∈ S, G.Adj (.inl a) (.inr b))).card
      ≤ t - 1

theorem kovari_sos_turan
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph (α ⊕ β)) [DecidableRel G.Adj]
    {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hbi : IsBipartiteSum G) (hno : NoKst G s t) :
    ∑ b : β, Nat.choose (G.degree (.inr b)) s ≤
      (t - 1) * Nat.choose (Fintype.card α) s
```

**`1 ≤ t` is load-bearing** so `t - 1` is the predecessor in `ℕ`.
**`1 ≤ s` is load-bearing** so `Nat.choose _ s` is the interesting
binomial (s = 0 is vacuous).

## Landmines

1. **This is not Turán's theorem.** Turán is already in
   `SimpleGraph/Turan.lean` (K_{r+1}-free → Turán graph). Never cite
   it as this gap (OPE-25 hard stop / negative control).
2. **This is not Mantel.** Mantel is the r = 2 case of Turán
   (triangle-free). Upstream, not a gap.
3. **This is not the Zarankiewicz problem.** Exact z(m,n;s,t) is
   open for most (s,t). Formalizing the classical counting bound is
   not a novelty claim and not a “near-miss” at Zarankiewicz.
4. **This is not sunflower / Kruskal–Katona / Oddtown / EKR.**
   Those are set-system theorems in ProofLab. KST is bipartite
   forbidden subgraphs.
5. **Parts `α` (s-side) and `β` (t-side) do not swap silently.**
   The namesake sums degrees on the **t-side** (`β`) of binomial
   `s`.
6. **`ℕ` subtraction.** Always assume `1 ≤ t` before `t - 1`.
7. **Do not prove the real-exponent edge form / Erdős–Stone /
   non-bipartite K_{s,t}-free in this id.**
8. **Do not re-prime** sunflower-erdos-rado / combinatorial-nullstellensatz
   / kruskal-katona / oddtown / cayley-trees / mycielski-triangle-free
   / havel-hakimi / menger-vertex / greedy / Brooks A/B / Dilworth /
   Eulerian / König / Dirac.
9. **No `Archive.*` import.**
10. **Leave OPE-403 alone.**

## Proof sketch (classical, Kővári–Sós–Turán 1954)

Level A: `s = t = 2` (no K_{2,2} / C₄ between the parts). Counting
form `∑_b binom(deg b, 2) ≤ binom(|α|, 2)`. Optional cheap edge
consequence via Cauchy–Schwarz / handshake (`e²` vs `|α| |β|`),
**not** labelled Kővári–Sós–Turán. Empty / edgeless / complete
bipartite `K_{1,n}` landmines.

Level B: namesake `kovari_sos_turan`. Double count pairs `(S, b)`
with `S ⊆ α`, `|S| = s`, `S` contained in the left-neighbourhood of
`b`. Left side is `∑_b binom(deg b, s)`. Right side is
`∑_{S, |S|=s} |common neighbourhood of S on β| ≤ (t−1) binom(|α|, s)`
by `NoKst`.

Partial: **Level A** `s = t = 2` + empty/edgeless, zero sorry, not
labelled KST. **Level B** namesake counting form. Cap two levels.
No real-exponent form, no Turán, no exact Zarankiewicz.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/KovariSosTuran.lean`
- Reuse Mathlib `SimpleGraph`, `completeBipartiteGraph`,
  `neighborFinset`, `Nat.choose`. Do **not** re-prove Turán /
  Mantel / sunflower / Kruskal–Katona / Oddtown / EKR.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

T. Kővári, V. T. Sós, and P. Turán, *On a problem of K. Zarankiewicz*,
Colloquium Mathematicum 3 (1954) 50–57. Textbook pin: Bollobás,
*Extremal Graph Theory*, Zarankiewicz / KST lemma; Jukna,
*Extremal Combinatorics*, double counting. Type pin: `SimpleGraph (α ⊕ β)`
+ `IsBipartiteSum` + `NoKst`. Turán's theorem, Mantel, sunflower,
and exact Zarankiewicz numbers are **different** statements, not
this claim.
