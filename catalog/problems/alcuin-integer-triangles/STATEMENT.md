# Alcuin's sequence (integer-sided triangles of perimeter n) — formalize-only

**id:** `alcuin-integer-triangles`
**ticket:** OPE-1310 Scout RECOMMENDED PRIME (parent OPE-1309;
post frucht-graph-aut #150 + proth-primality #151)
**expected:** known-classical (Alcuin of York / OEIS A005044: the
number of non-congruent triangles with positive integer sides and
perimeter `n` is a classical finite count; closed form residual) —
**no novelty claim**

## Why not classical / why formalize-only

Settled enumerative combinatorics: a triple of positive integers
`a ≤ b ≤ c` with `a + b + c = n` and strict triangle inequality
`a + b > c` is an integer-sided triangle of perimeter `n`, up to
congruence. Completely classical (Alcuin of York propositiones;
OEIS A005044).

Not an open problem. Not a novelty claim.

**Not** Heron / integer area (consumed `heron-formula`; area ≠
side-count; do **not** revive Pick / Brahmagupta / Heronian as
namesake). **Not** British flag / Napoleon / Simson / Viviani /
nine-point (consumed #145; Euclidean `dist` ≠ Nat sides; do **not**
revive). **Not** platonic-solids / Euler polyhedron (consumed #147;
regular maps ≠ integer triangles). **Not** egyptian-fractions /
Farey / Stern–Brocot (consumed; rationals ≠ side triples). **Not**
Pythagorean-triple classification (already `PythagoreanTriple.classification`;
right triangles ≠ all integer triangles; USE if needed, do **not**
re-prove, do **not** cite as Alcuin). **Not** Ruzsa triangle
inequality (already-in additive combinatorics; different). **Not**
Frucht graph Aut (consumed #150). **Not** Proth primality
(consumed #151). **Not** cannonball square-pyramid (leftover of
this shortlist).

Mathlib v4.10.0 already has the **Nat / Finset infra this theorem
needs**:

- `Nat` addition / order / `0 < a`
- `Finset.range` / `Finset.filter` / `Finset.card`
- `Nat.choose` / `choose_two_right` (Choose/Basic.lean L88) —
  **not** namesake
- `PythagoreanTriple.classification` — **different** right-triangle
  theorem; do **not** re-prove

There is **no** named Alcuin triangle-count theorem, **no**
`alcuin` / `Alcuin` / `integerTriangle` / `IntegerTriangle` /
`triangleCount` anywhere under `Mathlib/` or `Archive/` or
`ProofLab/` (this run → ZERO on those names; Ruzsa triangle
inequality and Euclidean triangle-sum-to-π hits only). Do **not**
import `Archive.*`.

OPE-1294 shortlist is **CONSUMED** (#150 frucht-graph-aut Level A
+ #151 proth-primality Level A). This is a **fresh**
catalog-audit id, **not** a Frucht leftover continuation,
**not** a Proth leftover, **not** a Heron leftover, **not** a
British-flag leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite Nat triangle-count witnesses after graph Aut +
Proth form. `Nat` / `Finset.filter` are waiting the same way
`Rat` waited for Egyptian fractions. **Not a rubber-stamp of
PythagoreanTriple.classification.** **Not a rubber-stamp of
Heron.**

Do **not** describe an attack as discovering Alcuin's sequence.
Do **not** expand into Heronian area / Pick / Brahmagupta /
isospectral triangles as extra namesakes (those are leftover-risk
of *this* id only if they use area; they are also Heron residuals
— do **not** sorry them).

## Pinned convention (exact)

**v1 Level A is the integer-triangle predicate on named small
perimeters: perimeter `1` has none, perimeter `3` is exactly
`(1,1,1)`, perimeter `5` is exactly `(1,2,2)`, and perimeter `6`
is exactly `(2,2,2)`, not labelled Alcuin.** Positive sides,
`a ≤ b ≤ c`, `a+b+c = n`, and strict `a+b > c` are load-bearing.

Suggested pin:

```text
-- Level A (not labelled Alcuin):
-- named small perimeters.

def IsIntegerTriangle (a b c n : ℕ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = n ∧ a + b > c

theorem alcuin_one :
    ∀ a b c, ¬ IsIntegerTriangle a b c 1

theorem alcuin_three :
    IsIntegerTriangle 1 1 1 3
    ∧ ∀ a b c, IsIntegerTriangle a b c 3 → a = 1 ∧ b = 1 ∧ c = 1

theorem alcuin_five :
    IsIntegerTriangle 1 2 2 5
    ∧ ∀ a b c, IsIntegerTriangle a b c 5 → a = 1 ∧ b = 2 ∧ c = 2

theorem alcuin_six :
    IsIntegerTriangle 2 2 2 6
    ∧ ∀ a b c, IsIntegerTriangle a b c 6 → a = 2 ∧ b = 2 ∧ c = 2

-- optional extra: perimeter 7 is exactly {(1,3,3),(2,2,3)}

-- Level B namesake (closed form; residual OK)
theorem alcuin_integer_triangles (n : ℕ) :
    { (a,b,c) | IsIntegerTriangle a b c n }.encard
      = round (n^2 / 48)   -- pin even/odd convention in a comment;
                           -- do not sorry the closed form
```

Named small perimeters are load-bearing.
`IsIntegerTriangle` arithmetic is load-bearing.
Strict `a+b > c` is load-bearing (so `(1,1,2)` of perimeter 4 is
**not** a triangle).

**Level A may land only** perimeters `1` / `3` / `5` / `6`
(optional extra: perimeter `7` has exactly two triples), **not**
labelled Alcuin. Reuse Mathlib `Nat` / `Finset` — **do not
re-prove** Pythagorean classification / Heron / Euclidean angle
sum.

**Level B** is the namesake closed form (OEIS A005044 /
round-`n²/48` with the even/odd convention). Do not sorry the
namesake; honest partial is allowed (comment residual, not
`sorry`). Heronian area / Pick / Brahmagupta are residual.

## Landmines

1. **Do not re-prove** `Nat` arithmetic / `Finset.filter` /
   `PythagoreanTriple.classification` / Heron.
   Already Mathlib or consumed. Use them if needed.
2. **This is not** Heron / integer area. Side-count ≠ area.
   Do not cite as Alcuin.
3. **This is not** British flag / Napoleon / Simson / Viviani /
   nine-point (consumed #145). Euclidean `dist` ≠ Nat sides.
4. **This is not** platonic-solids / Euler polyhedron
   (consumed #147).
5. **This is not** Pythagorean-triple classification (already-in).
   Right triangles are a proper subclass. Do not cite as Alcuin.
6. **This is not** Ruzsa triangle inequality (already-in additive).
7. **This is not** `cannonball-square-pyramid` (OPE-1310 leftover).
   Do not prove cannonball here.
8. **This is not** frucht-graph-aut / proth-primality
   (consumed #150+#151) / Pépin / Pocklington / Cayley-graph /
   GRR / Aut(Kₙ)≅Sₙ.
9. **Do not** re-prime the consumed mill list.
10. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
    alone.
11. **Do not import `Archive.*`.**
12. Default no claim. No novelty claim.

## Out of v1

- Alcuin namesake (closed form for every `n`)
- Heronian integer-area classification
- Pick's theorem / Brahmagupta
- Prize claims / Millennium / Beal
