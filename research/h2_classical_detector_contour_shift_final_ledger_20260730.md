# H2 Classical Detector Contour-Shift Final Ledger

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Classification: `FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`

## Public chain

- preregistration `c82a77039e939d904038de1c39625bef50ea9dd3`: run `30482171994`,
  job `90678758000`, passed in `2m12s`;
- frozen implementation `b87e9164395b14723f61d8451e3ed1b0cd0ae1c8`: run `30484701769`,
  job `90687338466`, passed in `2m39s`;
- immutable evidence `1cc20bca2455d9eb9ca27a0e42fbaf86b340b4e8`: run `30485116278`,
  job `90688732121`, passed in `1m36s`.

The five-file frozen proof and registration diff remains empty.

## Result

Lean verifies the actual classical detector contour shift for every nontrivial zeta zero
`rho` with `1/2<Re(rho)` and every `Y>0`. The Gamma pole at `w=0` is removable without a
simple-zero assumption; the translated zeta pole at `w=1-rho` contributes the exact source
residue. Both horizontal edges vanish, both vertical lines are integrable, and the finite
rectangle passes to the infinite shifted-line and smoothed-series identities.

For `M>=1`, the exact coefficient-gap head/tail identity also compiles. The aggregate theorem
is `classicalDetectorContourShift_endpoint`.

## Remaining route

The fixed contour-shift node is closed. The first open H2 successor is the actual quantitative
dyadic Type-I/Type-II block and tail estimate used to derive a zero-density dichotomy. No
zero-density exponent, sparse-exception exclusion, H2, or RH has been proved.

The global RH Goal remains active.
