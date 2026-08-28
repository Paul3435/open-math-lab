# RESULTS — ramsey-multicolor-r333 / OPE-461

**status:** formalized (both bounds)  
**novelty:** known-classical only (Greenwood & Gleason 1955) — **no claim**  
**date:** 2026-08-25

## Theorems (Lean, zero sorry)

File: `proofs/lean-project/ProofLab/RamseyMulticolor.lean`

| Theorem | Statement |
|---------|-----------|
| `r333_gt_16` | `¬ HasMonoTriangle witness16` on `Fin 16` |
| `r333_le_17` | every symmetric `f : Fin 17 → Fin 17 → Fin 3` has a mono triangle |
| `r333_eq_17` | both bounds packaged |

## Verification

```text
lake env lean ProofLab/RamseyMulticolor.lean   # EXIT=0
lake build ProofLab                            # green
#print axioms r333_gt_16  → propext, Lean.ofReduceBool, Quot.sound
#print axioms r333_le_17  → propext, Classical.choice, Quot.sound
#print axioms r333_eq_17  → propext, Classical.choice, Lean.ofReduceBool, Quot.sound
rg 'sorry|admit' ProofLab/RamseyMulticolor.lean  # no real sorry
```

## Method

### Lower bound R(3,3,3) > 16
- Scout certificate `catalog/problems/ramsey-multicolor-r333/witness16_certificate.txt` (120 digits, lex `i<j`).
- Encoded as `witness16Digits : List ℕ` + `edgeIndex`.
- `native_decide` on one fixed colouring (triple enumeration over `Fin 16`), **not** `3^120` colourings.
- Offline Python pre-check: 0 monochromatic triangles; every vertex degree (5,5,5).

### Upper bound R(3,3,3) ≤ 17
- Pigeonhole at any vertex of `K_17`: among 16 incident edges some colour has deg ≥ 6.
- On a 6-subset of that colour-neighbourhood:
  - either a same-colour edge closes a mono triangle with the apex, or
  - no edge of that colour ⇒ remaining 2-colouring; pull back `ramsey33_clique_inside_finset` from closed `ProofLab/Ramsey.lean`.
- **Note on Director brief parity layer:** on `K_17` the complementary “all colour-degrees ≤ 5” case is impossible by `5+5+5=15<16`, so handshake parity is not required. The GG colouring on 16 vertices is 5-regular per colour (degree sum 80 even) — parity does not obstruct the lower bound either.

## STATEMENT pin
`problems/ramsey-multicolor-r333/STATEMENT.md` — `f : Fin n → Fin n → Fin k` symmetric; mono triangle = equal pairwise colours; cert order lex `i<j`.

## Residual risks
- Upper bound requires `IsSymmetric f` (correct for undirected edges); diagonal default unused.
- `native_decide` lower bound depends on kernel reduction (`Lean.ofReduceBool`) — standard lab pattern (cf. VdW / Ramsey).
- No Mathlib upstream contribution PR claimed; formalize-only inside ProofLab.
- Adversarial review recommended before treating as portfolio-closed.

## Non-goals
- No novelty / no external claim packet.
- Did not modify closed `Ramsey.lean` / `VanDerWaerden.lean`.
