# H2 Classical Detector Dyadic Dichotomy Final Ledger

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-DYADIC-DICHOTOMY-01`

Classification: `FULL_SUCCESS / SOURCE_DYADIC_DICHOTOMY_FORMALIZED`

## Public chain

- preregistration `af32194ba854e6df168f9ec09f1bd8581bbef772`: run `30489281045`,
  job `90702801282`, passed in `2m0s`;
- frozen implementation `207953d7cff153eddc017a7d2e2612a786a0c050`: run `30491308421`,
  job `90709585747`, passed in `2m18s`;
- immutable evidence `c509cf6f475fa19e86d4734fb39b4b4f740255ef`: run `30491565903`,
  job `90710420038`, passed in `1m37s`.

The five-file frozen proof and registration diff remains empty.

Public final-ledger gate: commit `ae35eae20c5f5dcdd2c266e3af4f4fc9dddaa20c`,
Lean Action run `30491754062`, build job `90711045096`, passed in `2m7s`.

## Result

Lean verifies the actual finite Maynard--Pratt detector alternative at
`Y=sqrt T`, `M=floor(2*T^(1/100))`, and
`K=ceil(sqrt(T)*(log T)^2/2)`. The exact smoothed series splits into the source head, actual
binary-logarithmic blocks, and actual far tail. Explicit estimates make the head, far tail,
and retained translated-zeta residue simultaneously small, while the possible block count is
at most `3*log T`.

For every actual nontrivial zero in the source height range with real part greater than
`1/2`, Lean eventually proves that the actual shifted Mellin integral is at least `1/3` or
one actual dyadic block is large on the `1/log T` scale. The aggregate theorem is
`classicalDetectorDyadicDichotomy_endpoint`.

## Remaining route

The finite dyadic-dichotomy node is closed. The first open H2 successors are rarity estimates
for the actual Type-I dyadic blocks and actual Type-II shifted Mellin integrals, followed by the
source zero-density count. No density exponent, zero-free region, sparse-exception exclusion,
H2, or RH has been proved.

The global RH Goal remains active.
