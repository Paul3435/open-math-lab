# Frucht theorem (every finite group is a graph automorphism group) — formalize-only

**id:** `frucht-graph-aut`
**ticket:** OPE-1294 Scout RECOMMENDED PRIME (parent OPE-1293;
post platonic-solids #147 + egyptian-fractions #148)
**expected:** known-classical (Frucht 1939: every finite group is
the automorphism group of some finite undirected simple graph) —
**no novelty claim**

## Why not classical / why formalize-only

Settled algebraic graph theory: for every finite group `Γ` there
exists a finite simple graph `G` with `Aut(G) ≅ Γ`. Completely
classical (Frucht 1939; later Cayley-graph-plus-gadgets proofs).

Not an open problem. Not a novelty claim.

**Not** Cayley's formula / labelled trees (consumed `cayley-trees`;
counting trees ≠ automorphism groups; do **not** revive Prüfer /
Kirchhoff). **Not** Cayley's theorem that every group embeds in a
symmetric group (`Equiv.Perm` already-in; **USE** `≃` glue, do
**not** re-prove, do **not** cite as Frucht). **Not**
`Iso.completeGraph` as namesake (`Maps.lean` L544: type-equivalences
induce complete-graph isos — **USE**, do **not** cite as Frucht;
`Aut(K_n) ≅ S_n` is residual of *this* id). **Not** friendship
(consumed; Archive `friendship_theorem` already-in). **Not** Moore
cages (consumed). **Not** Sabidussi box-product chromatic number
(consumed #139; `χ(G □ H)` ≠ Aut). **Not** Petersen 1-factor
(consumed #135). **Not** platonic-solids / egyptian-fractions
(consumed #147+#148). **Not** Proth primality (leftover of this
shortlist).

Mathlib v4.10.0 already has the **graph / iso infra this theorem
needs**:

- `SimpleGraph.Iso` / `≃g` (`Maps.lean` L215)
- `Iso.completeGraph` (`Maps.lean` L544) — **not** namesake
- `completeGraph` (`Basic.lean` L144)
- `pathGraph` (`Hasse.lean` L94) / `pathGraph_two_eq_top` L108
- `RelIso.refl` / `Iso.comp` (`Maps.lean` L555)

There is **no** named Frucht theorem, **no** `frucht` /
`Frucht` / `GraphAut` / `automorphismGroup` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/` (this run → ZERO on
those names; manifold Whitney embedding and Turán `≃g` hits
only). Do **not** import `Archive.*`.

OPE-1278 shortlist is **CONSUMED** (#147 platonic-solids Level A
+ #148 egyptian-fractions Level A). This is a **fresh**
catalog-audit id, **not** a Platonic leftover continuation,
**not** an Egyptian leftover, **not** a Cayley-trees leftover,
**not** a prize leftover, **not** a Formalist Level B revival,
**not** a third slot.

Mill NOW: finite graph Aut witnesses after Platonic Schläfli
arithmetic + Egyptian unit-fraction sums. `≃g` + `pathGraph`
are waiting the same way `List.get` waited for Fine–Wilf.
**Not a rubber-stamp of Iso.completeGraph.** **Not a
rubber-stamp of Cayley trees.**

Do **not** describe an attack as discovering Frucht's theorem.
Do **not** expand into Cayley graphs as namesake / Sabidussi
vertex-transitive characterisation / graphical regular
representations as extra namesakes (those are leftover-risk of
*this* id).

## Pinned convention (exact)

**v1 Level A is the automorphism-type of named small graphs
via `≃g`: unique Aut on `completeGraph (Fin 1)` / `pathGraph 1`,
and `pathGraph 3` admits the endpoint-swap iso (so Aut is at
least a 2-element set), not labelled Frucht.** `SimpleGraph.Iso`
is load-bearing. `pathGraph` is load-bearing.

Suggested pin:

```text
-- Level A (not labelled Frucht):
-- Aut(K₁) unique; Aut(P₃) contains the endpoint flip.

abbrev GraphAut {V : Type*} (G : SimpleGraph V) := G ≃g G

theorem aut_complete_fin_one :
    Subsingleton (GraphAut (completeGraph (Fin 1)))

theorem aut_pathGraph_one :
    Subsingleton (GraphAut (pathGraph 1))

def pathGraphThreeFlip : GraphAut (pathGraph 3) := ...
-- reverse Fin 3, preserves the two edges 0—1 and 1—2

theorem pathGraphThreeFlip_ne_refl :
    pathGraphThreeFlip ≠ RelIso.refl _

-- optional extra: Aut(K₂) has card 2 via Iso.completeGraph USE

-- Level B namesake (every finite group; residual OK)
theorem frucht_graph_aut (Γ : Type*) [Group Γ] [Fintype Γ] :
    ∃ V : Type, ∃ G : SimpleGraph V, ∃ _ : Fintype V,
      Nonempty ((GraphAut G) ≃* Γ)
```

Named small graphs are load-bearing.
`≃g` is load-bearing.
Endpoint-swap on `pathGraph 3` is load-bearing.

**Level A may land only** unique Aut on `K₁` / `P₁` plus a
non-identity Aut of `P₃` (optional extra: `K₂` card 2 via
`Iso.completeGraph`), **not** labelled Frucht. Reuse Mathlib
`≃g` / `pathGraph` / `completeGraph` / `Iso.completeGraph` —
**do not re-prove** those.

**Level B** is the namesake: every finite group is Aut of some
finite simple graph. Do not sorry the namesake; honest partial
is allowed (comment residual, not `sorry`). Cayley-graph
gadgets / GRR / `Aut(K_n) ≅ S_n` as namesake are residual.

## Landmines

1. **Do not re-prove** `SimpleGraph.Iso` / `pathGraph` /
   `completeGraph` / `Iso.completeGraph` / `Equiv.Perm`.
   Already Mathlib. Use them.
2. **This is not** `Iso.completeGraph` as namesake.
   Type-equivalence of complete graphs ≠ Frucht. USE glue.
3. **This is not** Cayley's formula / Prüfer / Kirchhoff
   (consumed `cayley-trees`). Counting trees ≠ Aut groups.
4. **This is not** Cayley's theorem `Γ ↪ Perm`. Already-in
   glue. Do not cite as Frucht.
5. **This is not** friendship / Moore / Sabidussi box-product /
   Petersen 1-factor / Hedetniemi.
6. **This is not** `proth-primality` (OPE-1294 leftover).
   Do not prove Proth here.
7. **This is not** platonic-solids / egyptian-fractions
   (consumed #147+#148) / Fine–Wilf / British flag.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Frucht namesake (every finite group)
- Cayley-graph gadget construction / GRR
- `Aut(K_n) ≅ S_n` as namesake
- Prize claims / Millennium / Beal
