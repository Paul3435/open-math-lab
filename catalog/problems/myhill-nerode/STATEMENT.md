# Myhill–Nerode (named small-language witnesses, formalize-only)

**id:** `myhill-nerode`
**ticket:** OPE-1357 Scout RECOMMENDED PRIME (parent OPE-1356;
post langford-pairing #160 + legendre-three-squares #159)
**expected:** known-classical (Myhill 1957 / Nerode 1958:
a language is regular iff it has finitely many Nerode
right-congruence classes) —
**no novelty claim**

## Why not classical / why formalize-only

Settled formal-language theory: words `x, y` are Nerode
equivalent for `L` when `∀ z, xz ∈ L ↔ yz ∈ L`; `L` is
regular iff there are finitely many classes. Completely
classical. The namesake “finite index ⇔ regular” is a
**different**, larger residual — do **not** sorry it.

Not an open problem. Not a novelty claim. Not live cash.

**Not** the pumping lemma (`DFA.pumping_lemma`,
Computability/DFA.lean L152 already-in — **different**
theorem; USE as DFA glue if needed, do **not** re-prove,
do **not** cite as Myhill–Nerode). **Not** NFA→DFA subset
construction (`NFA.toDFA` already-in; USE, do **not**
re-prove). **Not** Kleene's theorem regex ⇔ DFA
(RegularExpressions.lean L18 TODO — residual of *this*
id; do **not** sorry Kleene). **Not** Fine–Wilf (consumed
#144; periods of one word ≠ right-congruence of a
language; do **not** revive Lyndon–Schützenberger /
Thue–Morse). **Not** Kraft (consumed #138; prefix-free
codes ≠ languages; do **not** revive McMillan / Huffman /
Shannon). **Not** Langford pairing (consumed #160; between-
counts ≠ Nerode classes; do **not** revive Skolem
sequences). **Not** Context-free `Language.IsContextFree`
(different Chomsky level). Cardinal `IsRegular` is a
**different** set-theoretic regularity — do **not** cite
as this theorem.

Mathlib v4.10.0 already has the **DFA / Language infra
this theorem needs**:

- `Language` (Computability/Language.lean L31) /
  `Membership` L34 / `0 = ∅` L47 / `1 = {[]}` L51
- `DFA` (Computability/DFA.lean L39) / `eval` L72 /
  `accepts` L100 / `mem_accepts` L102
- `List.append` / `List.foldl`

There is **no** named Myhill–Nerode theorem, **no**
`Myhill` / `Nerode` / `nerode` / `myhillNerode` /
`syntacticMonoid` / `Language.IsRegular` anywhere under
`Mathlib/` or `Archive/` or `ProofLab/` (this run → ZERO
on those names; cardinal `IsRegular` is a different
theorem). Do **not** import `Archive.*`.

OPE-1342 shortlist is **CONSUMED** (#159+#160). This is a
**fresh** catalog-audit prime, **not** a Langford leftover
continuation, **not** a Fine–Wilf leftover, **not** a
three-square leftover, **not** a prize leftover, **not** a
Formalist Level B revival, **not** a third slot.

Mill NOW: finite Nerode witnesses on Mathlib `Language` /
`DFA.accepts`. `DFA` / `Language` are waiting the same
way `List` / `GetElem` waited for Langford. **Not a
rubber-stamp of pumping.** **Not a rubber-stamp of
Fine–Wilf.**

Do **not** describe an attack as discovering Myhill–Nerode.
Do **not** expand into finite-index ⇔ regular as a sorry
(that is leftover-risk of *this* id — do **not** sorry it).
Do **not** label theorems `pumping_*` as the namesake
(already-in). Do **not** sorry Kleene regex ⇔ DFA.

## Pinned convention (exact)

**v1 Level A is named small-language Nerode witnesses:
the empty language has all words equivalent, `{[]}`
distinguishes `[]` from `[0]`, and a 2-state DFA
distinguishes `[]` from `[1]`, not labelled Myhill /
Nerode.** Right-congruence `∀ z, xz ∈ L ↔ yz ∈ L` is
load-bearing.

Suggested pin:

```text
-- Level A (not labelled Myhill / Nerode):
-- named small-language witnesses.

def NerodeEq (L : Language α) (x y : List α) : Prop :=
  ∀ z, (x ++ z ∈ L) ↔ (y ++ z ∈ L)

theorem nerode_empty (x y : List α) :
    NerodeEq (0 : Language α) x y
    -- empty language: no continuation is in L

theorem nerode_one_nil_ne :
    ¬ NerodeEq (1 : Language (Fin 2)) [] [0]
    -- 1 = {[]}; [] ++ [] ∈ 1, [0] ++ [] ∉ 1

-- optional extra: a 2-state last-letter DFA
-- whose accepts distinguishes [] and [1]

-- Level B namesake (finite index iff regular; residual OK)
theorem myhill_nerode :
    -- L regular ↔ finite Nerode index
    -- do not sorry the namesake
```

Named small-language witnesses are load-bearing.
`nerode_empty` / `nerode_one_nil_ne` are load-bearing
(so the theorem is **not** “some DFA exists”).

**Level A may land only** the empty-language equivalence /
`{[]}` distinction / optional 2-state DFA distinction,
**not** labelled Myhill / Nerode. Reuse Mathlib `Language` /
`DFA` / `accepts` — **do not re-prove** pumping / NFA→DFA /
Fine–Wilf periods.

**Level B** is the namesake finite-index characterisation.
Do not sorry the namesake; honest partial is allowed
(comment residual, not `sorry`). Kleene regex ⇔ DFA extras
are residual.

## Landmines

1. **Do not re-prove** `Language` / `DFA` / `eval` /
   `accepts` / `DFA.pumping_lemma` (L152 already-in) /
   `NFA.toDFA`. Already Mathlib. Use them if needed.
2. **This is not** Kleene regex ⇔ DFA
   (RegularExpressions.lean TODO). Residual of this id.
   Do not sorry Kleene.
3. **This is not** Fine–Wilf / Lyndon–Schützenberger
   (consumed #144; periods ≠ Nerode classes).
4. **This is not** Kraft / McMillan / Huffman / Shannon
   (consumed #138; codes ≠ languages).
5. **This is not** `langford-pairing` (consumed #160) /
   Skolem sequences.
6. **This is not** `gray-code` (leftover of this
   shortlist). Do not prove Gray here.
7. **This is not** cardinal `IsRegular` / CFL
   `Language.IsContextFree`.
8. **Do not** re-prime the consumed mill list.
9. **Leave OPE-403 alone.** Leave OPE-1195 leftover status
   alone.
10. **Do not import `Archive.*`.**
11. Default no claim. No novelty claim.

## Out of v1

- Myhill–Nerode namesake (finite index ⇔ regular)
- Kleene regex ⇔ DFA / syntactic monoid
- Prize claims / Millennium / Beal
