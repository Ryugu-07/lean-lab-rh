# H7 Connes Weighted Ground-State Comparison Immutable Evidence

Date: 2026-07-30

Campaign:
`PROOF-ATTEMPT-20260730-H7-CONNES-WEIGHTED-GROUNDSTATE-COMPARISON-01`

Classification:
`MEANINGFUL_PARTIAL / EXACT_CONSUMER_AND_OBSTRUCTION / ACTUAL_SOURCE_RATE_OPEN`

## Frozen implementation

- commit: `f55c334050cf135997308a287701ed5239978a86`;
- Lean Action run: `30517091377`;
- build job: `90789265240`;
- result: passed in `2m14s`;
- local full build before publication: `8811/8811`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/ConnesGroundStateWeightedComparison.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
attempts/h7_connes_weighted_groundstate_comparison_20260730.md
research/h7_connes_weighted_groundstate_comparison_prereg_20260730.md
research/h7_connes_weighted_groundstate_comparison_result_20260730.md
research/hard_gap_dag.md
research/literature_source_registry.csv
```

## Certified positive result

Lean proves:

- the exact positive-strip squared weight mass `(exp(2*A*R)-1)/A`;
- the exact `A=0` mass `2*R`;
- oriented normalized `L2Error <= 2*projectiveDefect`;
- the implication from `lambda^(2*A)*ratio -> 0` for every `0<A<1/2` to the full weighted
  comparison for every `0<=A<1/2`;
- transfer from an independently proved packet-transform limit to the true-ground transform.

The positive result is a consumer.  It does not instantiate the actual Connes ground state,
packet, Rayleigh excess, or gap.

## Certified negative result

For `lambda_n=exp(n)` and the compiled two-dimensional collapsing-gap family with both gap and
absolute Rayleigh excess equal to `exp(-n)`, Lean proves:

```text
lambda_n^(2*A) * absoluteExcess_n -> 0   for every A<1/2,
absoluteExcess_n / gap_n = 1,
projectiveDefect_n = 1.
```

Therefore support-weighted small absolute Rayleigh excess cannot replace the actual
excess-to-gap ratio.

Five exact campaign TargetChecks compile. Eleven selected axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`. Three forbidden scans and `git diff --check` are empty.

## Source boundary

Connes--Consani 2023 supplies numerical graph agreement and reports a growing cluster of
minuscule Weil eigenvalues, but proves no packet Rayleigh bound, first Weil spectral gap, or
ratio rate.  The actual source comparison, packet-to-`Xi` Lean reconstruction, simple-even
ground-state theorem, H7, and RH remain open.
