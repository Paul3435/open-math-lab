# Kruskal–Katona — colex initial segments minimise the shadow (formalize-only)

**id:** `kruskal-katona`
**ticket:** OPE-702 Scout recommended prime (support OPE-701; post cayley-trees #64 + mycielski-triangle-free #65)
**expected:** known-classical (Kruskal 1963 / Katona 1968) — **no novelty claim**

## Why not classical / why formalize-only

Settled shadow-minimisation: among all `r`-uniform families of a given
cardinality, the colexicographic initial segment has the smallest shadow.
Not an open problem. Mathlib v4.10.0 already has the **scaffolding this
theorem was written for**:

- `Finset.shadow` (`∂`) and `Set.Sized` (`Combinatorics/SetFamily/Shadow.lean`)
- `Finset.IsInitSeg` / `Finset.initSeg` (`Combinatorics/Colex.lean`)
- UV-compression `card_shadow_compression_le` (`SetFamily/Compression/UV.lean`,
  comments call this “a key fact in Kruskal-Katona”)
- LYM / Sperner (`SetFamily/LYM.lean` — **different** theorems, already
  upstream; never cite as this gap)

There is **no** Kruskal–Katona theorem anywhere under `Mathlib/` or
`Archive/` (word-regexp this run → ZERO theorem ident; Colex/UV mention
the name only as motivation). Completing the namesake is a new proof
layer on defs that are already waiting — the same “defs waiting”
heuristic that primed `cayley-trees` (`IsTree`) and `mycielski-triangle-free`
(`CliqueFree`). Those two slots are now **consumed**. This is **not**
Sperner, **not** LYM, **not** Dilworth / Mirsky / Greene, **not** EKR.

Do **not** describe an attack as discovering Kruskal–Katona.
Do **not** expand into Hilton–Milner, Oddtown, Eventown, Frankl–Füredi,
or the Lovász fractional form as a second id.

## Pinned convention (exact)

**Uniform pin:** `(𝒜 : Set (Finset (Fin n))).Sized r` (every member has
card `r`). Shadow is Mathlib `Finset.shadow` (down-shadow to card `r-1`).

**Colex pin:** Mathlib `Finset.IsInitSeg 𝒞 r` — `𝒞` is a colex initial
segment of the `r`-subsets. Do **not** reinvent colex. Do **not** use
lex order.

**Namesake (v1):** a colex initial segment of the same cardinality
minimises the shadow.

```text
theorem kruskal_katona {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h𝒞 : IsInitSeg 𝒞 r)
    (hcard : 𝒞.card = 𝒜.card) :
    (shadow 𝒞).card ≤ (shadow 𝒜).card
```

Existence of such a `𝒞` for every `m ≤ n.choose r` is a named lemma,
not a second theorem (every nonempty `IsInitSeg` is some `initSeg s` by
Mathlib `IsInitSeg.exists_initSeg`).

**v1 is the comparison inequality.** Do not require a bundled
`colexInit n r m` API beyond what the proof needs. Lovász’s real-valued
binomial form (`|𝒜| = binom(x,r) ⇒ |∂𝒜| ≥ binom(x,r-1)`) is a **stretch
out of v1**, not a leftover re-prime.

## Landmines

1. **This is not Sperner.** Sperner (`IsAntichain.sperner`) is already in
   `LYM.lean`. Kruskal–Katona is about *shadows of uniform families*,
   not antichain size in the boolean lattice.
2. **This is not LYM.** Local LYM
   (`card_div_choose_le_card_shadow_div_choose`) is already upstream.
   Do not cite it as Kruskal–Katona.
3. **This is not Dilworth / Mirsky / Greene.** Poset width / chain
   partitions are consumed (`dilworth-poset`). Different theorem.
4. **Colex, not lex.** Mathlib `toColex`. Init segments of the *wrong*
   order fail the shadow-minimiser claim.
5. **Uniform `Sized r` is load-bearing.** Mixed-rank families are not
   this theorem.
6. **UV-compression glue is already upstream.**
   `UV.card_shadow_compression_le` may be *used*; do not re-prove it
   and do not call it Kruskal–Katona.
7. **Finite only.** Ground set `Fin n`. Infinite KK / shadows in
   `ℕ` out of scope (Colex.lean even TODOs `initSeg` on `ℕ`).
8. **Do not prove Hilton–Milner / EKR / Oddtown / Eventown in this id.**
9. **Do not re-prime** cayley-trees / mycielski-triangle-free /
   havel-hakimi / menger-vertex / greedy / Brooks A/B / Dilworth /
   Eulerian / König / Dirac.
10. **No `Archive.*` import.**

## Proof sketch (classical, Kruskal 1963 / Katona 1968)

Level A: empty family; singleton `r`-set (shadow has card `r`); `r = 0`
or `r = 1` (shadow of 1-sets is `{∅}` or empty); UV-compression already
does not increase the shadow — glue, not labelled KK.

Level B: namesake `kruskal_katona`. Standard route: UV-compress until
the family is colex-compressed; a fully compressed `r`-uniform family
of size `m` is the colex initial segment of size `m`; compression does
not increase `|∂|`, so that segment minimises the shadow.

Partial: **Level A** small cases + compression glue, zero sorry, not
labelled Kruskal–Katona. **Level B** namesake comparison. Cap two
levels. No Lovász-`ℝ` binomial, no Hilton–Milner, no Oddtown.

## Lean gate (when attacked)

- Target module: `proofs/lean-project/ProofLab/KruskalKatona.lean`
- Reuse Mathlib `shadow`, `IsInitSeg` / `initSeg`, `Set.Sized`,
  `UV.card_shadow_compression_le`. Do **not** re-prove Sperner / LYM /
  Dilworth / EKR.
- Zero `sorry`; `lake env lean` exit 0
- Default **no claim**
- Do not import `Archive.*`

## Canonical source

J. B. Kruskal, *The number of simplices in a complex*, in *Mathematical
Optimization Techniques* (Univ. California Press, 1963) 251–278.
G. O. H. Katona, *A theorem of finite sets*, in *Theory of Graphs*
(Academic Press, 1968) 187–207. Textbook pin: Bollobás, *Combinatorics*,
shadow / colex chapter; or van Lint–Wilson, *A Course in Combinatorics*,
§6. Type pin: Mathlib `Finset.shadow` + `Finset.IsInitSeg`. Sperner,
LYM, Dilworth, EKR, and Hilton–Milner are **different** theorems, not
this claim.
