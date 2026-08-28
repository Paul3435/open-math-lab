# Attack log — van-der-waerden-w24

| Date | Role | Method | Outcome |
|------|------|--------|---------|
| 2026-08-25 | Attack Lead (OPE-455) | STATEMENT pin; offline pruned backtrack for Fin-34 free colouring; Lean `HasMono4` + `native_decide` on fixed witness; upper bound timeboxed | **PARTIAL**: `vdw24_gt_34` zero-sorry (`W(2,4)>34`); `W(2,4)≤35` **not** proved. `lake env lean` + `lake build ProofLab` green. No novelty / no claim. Artifacts under `attacks/van-der-waerden-w24-20260825-ope455/`. |
