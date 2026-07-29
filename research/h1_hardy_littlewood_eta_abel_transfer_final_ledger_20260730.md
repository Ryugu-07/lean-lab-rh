# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Final Ledger

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Classification: `FULL_SUCCESS / ETA_TO_THETA_ABEL_TRANSFER_FORMALIZED`

## Public chain

- preregistration `e770d76f85ab9d363b50c606fc195a2401b93390`: run `30477686788`,
  job `90663405809`, passed in `1m33s`;
- frozen implementation `f03c6a8f5d35945d34407d0627b7a5f4f629cb9e`: run `30479693865`,
  job `90670228283`, passed in `2m17s`;
- immutable evidence `6b151d4cbecd963ea4be9d208c9dff3d20ac47ac`: run `30480041592`,
  job `90671423054`, passed in `2m22s`.

The five-file frozen proof and registration diff remains empty.

## Result

Lean verifies the exact shifted reciprocal-log Abel transform. A uniform eta remainder
`Ceta*N^(-sigma)` with `sigma>0` implies convergence of the ordered Theta partial sums and the
explicit uniform remainder `(2/log 2)*Ceta*N^(-sigma)`. The theorem preserves the same common
constant over arbitrary parameter families.

The historical omission finding is structural: Hardy--Littlewood Lemma 4 has no independent
oscillatory producer beyond Lemma 3.

## Remaining route

The fixed transfer node is closed. The first open successor is the actual uniform Lemma 3 eta
remainder without an extra `abs(s)` loss. Primitive identification, both source moments, the
count parameter budget, an unconditional linear critical-zero count, H1, and RH remain open.

The global RH Goal remains active.
