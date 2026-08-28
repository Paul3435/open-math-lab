# LOG — OPE-447

- Started from OPE-445 green base (`glaisherExpand_nodup`, one-way Finset maps).
- Proved bind-collapse-expand on shifted odd kernels by strong induction on multiplicity.
- Rebuilt B-multisets via `dedup.bind replicate count`.
- Linked collapse counts to bit indices (`kernelExponents`, Colex `toFinset_bitIndices_twoPowSum`).
- Closed expand∘collapse on Nodup A-legal via bit membership characterization.
- Lifted to partitions + `Finset.card_bij'` → `schur_partition`.
- `lake build ProofLab` green; zero sorry.
