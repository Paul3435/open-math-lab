/-
Named small-language Nerode witnesses — Level A only
(empty language all-equivalent / `{[]}` distinguishes `[]`
from `[0]` / optional 2-state last-letter DFA distinguishes
`[]` from `[1]`). **Not labelled Myhill / Nerode.**

status: known-classical, formalize-only, **no novelty claim**.
Mathlib v4.10.0 pin `a719ba5c3115` has `Language` / `DFA` /
`eval` / `accepts` as **infra**. ZERO named Myhill–Nerode /
`Myhill` / `Nerode` / `nerode` / `myhillNerode` /
`syntacticMonoid` / `Language.IsRegular` under `Mathlib/` or
`Archive/` or `ProofLab/` (this run; cardinal `IsRegular` is
a different set-theoretic theorem). Completing the Level A
named small-language witnesses is the gap this ticket lands.
The Level B namesake `myhill_nerode` (finite Nerode index iff
regular) is **out of this ticket** and is **not** sorry-ed.
Kleene regex iff DFA / syntactic monoid extras are residual
of this id. Do **not** label theorems `myhill_*` (namesake)
or `pumping_*` (`DFA.pumping_lemma` already-in).

Pin: `catalog/problems/myhill-nerode/STATEMENT.md`
(OPE-1364; Scout OPE-1357 RECOMMENDED PRIME; Director OPE-1362).
Encoding: `NerodeEq` via Mathlib `Language` / `List.append`.
Zero `sorry`. Do not import `Archive.*`.

This is **not** `Language` / `0` / `1` / `Membership`
(`Computability/Language.lean` L31 / L47 / L51) — already
Mathlib. **USE, do not re-prove; do not cite as Myhill–Nerode.**
This is **not** `DFA` / `eval` / `accepts`
(`Computability/DFA.lean` L39 / L72 / L100) — already Mathlib.
**USE, do not re-prove; do not cite as Myhill–Nerode.**
This is **not** `DFA.pumping_lemma` (DFA.lean L152) — a
**different** already-in pumping theorem. **USE DFA/Language
if needed; do not re-prove; do not cite as Myhill–Nerode.**
This is **not** `NFA.toDFA` — already-in subset construction.
This is **not** Kleene regex iff DFA (`RegularExpressions.lean`
TODO) — residual of this id; do **not** sorry Kleene.
This is **not** Fine–Wilf (`ProofLab/FineWilf.lean`, consumed
#144). Periods of one word ≠ right-congruence of a language.
Do **not** revive Lyndon–Schützenberger.
This is **not** Kraft (`ProofLab/KraftInequality.lean`,
consumed #138). Prefix-free codes ≠ languages. Do **not**
revive McMillan / Huffman / Shannon.
This is **not** Langford pairing
(`ProofLab/LangfordPairing.lean`, consumed #160).
Between-counts ≠ Nerode classes. Do **not** revive Skolem
sequences.
This is **not** Legendre three-square
(`ProofLab/LegendreThreeSquares.lean`, consumed #159).
Do **not** revive Gauss Eureka / three triangular numbers.
This is **not** Gray codes (leftover of this shortlist).
Do **not** prove Gray listings / hypercube Hamiltonian here.
This is **not** cardinal `IsRegular` / `Language.IsContextFree`.
Do not re-prime the consumed mill. Leave OPE-403 alone.
Leave OPE-1195 alone.

v1 is named small-language witnesses: the empty language
has all words equivalent, `{[]}` distinguishes `[]` from
`[0]`, and a 2-state last-letter DFA distinguishes `[]`
from `[1]`, **not labelled Myhill / Nerode**. Right-congruence
`∀ z, xz ∈ L ↔ yz ∈ L` is load-bearing. `nerode_empty` /
`nerode_one_nil_ne` are load-bearing (so Level A is **not**
"some DFA exists").

Level A: empty-language equivalence / `{[]}` distinction /
optional 2-state DFA distinction. **Not** labelled Myhill /
Nerode.

Transcribed classical argument (J. Myhill 1957; A. Nerode
1958 right-congruence). Compact form: Wikipedia
*Myhill–Nerode theorem* (finite-index characterisation is
Level B residual). Type pin: `NerodeEq` / `Language`. Pumping
lemma is a different already-in theorem. Kleene regex iff DFA
is a different residual. Fine–Wilf periods are a different
consumed mill. No novelty claim. Default no claim.
-/
import Mathlib.Computability.DFA
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace ProofLab.MyhillNerode

/-! ## Encoding: Nerode right-congruence (not labelled Myhill / Nerode) -/

/-- Words `x, y` are equivalent for `L` when they have the
same continuations: `∀ z, xz ∈ L ↔ yz ∈ L`. Encoding;
**not** labelled Myhill / Nerode. Load-bearing: right-congruence
via `List.append`. Does **not** re-prove `Language` / `DFA`. -/
def NerodeEq {α : Type*} (L : Language α) (x y : List α) : Prop :=
  ∀ z, (x ++ z ∈ L) ↔ (y ++ z ∈ L)

/-! ## Level A: empty language / `{[]}` distinction / optional 2-state DFA
(not labelled Myhill / Nerode) -/

/-- Empty language: no continuation is in `L`, so every pair
of words is equivalent. Glue; **not** labelled Myhill / Nerode.
Load-bearing (so Level A is **not** "some DFA exists"). -/
theorem nerode_empty {α : Type*} (x y : List α) :
    NerodeEq (0 : Language α) x y := by
  intro z
  simp [Language.not_mem_zero]

/-- `1 = {[]}` distinguishes `[]` from `[0]`: `[] ++ [] ∈ 1`
and `[0] ++ [] ∉ 1`. Glue; **not** labelled Myhill / Nerode.
Load-bearing (so Level A is **not** "some DFA exists"). -/
theorem nerode_one_nil_ne :
    ¬ NerodeEq (1 : Language (Fin 2)) [] [0] := by
  intro h
  have hz := h []
  simp [Language.mem_one] at hz

/-- Optional extra: a 2-state last-letter DFA over `Fin 2`.
Start at `0`; `step` stores the letter; accept `{1}`.
Uses Mathlib `DFA` / `eval` / `accepts`; does **not** re-prove
them. Glue; **not** labelled Myhill / Nerode. -/
def lastLetterDFA : DFA (Fin 2) (Fin 2) where
  step := fun _ a => a
  start := 0
  accept := {1}

/-- `[]` is not accepted (stays at start `0`). Glue;
**not** labelled Myhill / Nerode. Does **not** re-prove
`DFA.eval` / `DFA.accepts`. -/
theorem lastLetterDFA_nil_nmem :
    [] ∉ lastLetterDFA.accepts := by
  rw [DFA.mem_accepts, DFA.eval_nil]
  simp [lastLetterDFA]

/-- `[1]` is accepted (last letter `1`). Glue;
**not** labelled Myhill / Nerode. Does **not** re-prove
`DFA.eval` / `DFA.accepts`. -/
theorem lastLetterDFA_one_mem :
    ([1] : List (Fin 2)) ∈ lastLetterDFA.accepts := by
  rw [DFA.mem_accepts, DFA.eval_singleton]
  simp [lastLetterDFA]

/-- The accepted language distinguishes `[]` from `[1]`
under `NerodeEq` (witness `z = []`). Glue; **not** labelled
Myhill / Nerode. -/
theorem lastLetterDFA_nil_ne :
    ¬ NerodeEq lastLetterDFA.accepts [] [1] := by
  intro h
  have hz := h []
  simp [lastLetterDFA_nil_nmem, lastLetterDFA_one_mem] at hz

/-
Level B namesake OUT of this ticket (do not sorry):
  theorem myhill_nerode :
      -- L regular ↔ finite Nerode index
Kleene regex iff DFA / syntactic monoid extras are residual
of this id — do not expand; do not label theorems `myhill_*`
or `pumping_*`.
-/

end ProofLab.MyhillNerode
