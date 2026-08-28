# LOG — OPE-455 van-der-waerden-w24

| Time (local) | Step | Result |
|--------------|------|--------|
| 2026-08-25 | Wake issue_assigned OPE-455; checkout already claimed | start |
| 2026-08-25 | Pin STATEMENT.md conventions (W(2,4), Fin encoding, 4-AP) | done |
| 2026-08-25 | Offline pruned backtrack for length-34 mono-4-AP-free colouring | found `0010001110100100011101001000111011` |
| 2026-08-25 | Lean `HasMono4` + `witness34` + `vdw24_gt_34` by `native_decide` | lake env lean EXIT=0 |
| 2026-08-25 | `lake build ProofLab` | green |
| 2026-08-25 | `#print axioms` audit | only propext / choice / ofReduceBool / Quot.sound |
| 2026-08-25 | Upper bound W(2,4)≤35 | **timebox stop** — partial ladder close |
| 2026-08-25 | RESULTS/STATUS + PR | handoff |
