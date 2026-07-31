# H12 Levinson--Montgomery Global Count Step 7 Result

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Status: `STEPS_1_7_COMPILED / LOCAL_AUDIT_GREEN / IMPLEMENTATION_CI_REQUIRED /
CAMPAIGN_ACTIVE`

## Exact result

Two new no-sorry modules compile the first seven preregistered steps:

- `LeanLab/Riemann/LevinsonMontgomeryNegativeHeightGeometry.lean`;
- `LeanLab/Riemann/LevinsonMontgomeryFiniteArgumentPrinciple.lean`.

The negative integer-height predicate now excludes every actual zeta zero in the open source
segment by a punctured positive-right principal-part contradiction. It consequently excludes
actual derivative zeros and yields the source negative top geometry or the already compiled
dense-count branch.

For a finite analytic divisor, Lean proves an exact rectangle argument principle with analytic
multiplicity. The actual zeta and zeta-derivative instantiations identify divisor values with
`burnolZetaZeroMultiplicity` and `riemannZetaDerivZeroMultiplicity`.

The final compiled endpoint of this checkpoint is
`levinsonMontgomery_globalCountDifference_actual`. Given a common zero-free bottom and actual
negative top geometry, it constructs `0<r<1/2` and proves that the difference of the two actual
rectangle logarithmic-derivative integrals equals `2*pi*I` times the change in the global
multiplicity-bearing Speiser count difference between the two heights.

## Omission candidate

The open-left convention can be recovered without directly integrating critical-line
indentation arcs in this finite argument-principle step. Compact divisor support is finite, so
Lean selects a common adaptive side `r<1/2` lying to the right of every support point whose real
part is strictly below `1/2`. A proved filter equality then preserves every open-left zero while
excluding every critical-line zero.

This is a genuine alternative bookkeeping mechanism for the finite count identity. It does not
show that source indentations are unnecessary elsewhere, and it does not prove the logarithmic
count bound.

## Failed attack and repair

The first finite-factorization attempt tried to use one domain both for compact divisor
extraction and for the connected open factorization identity. Mathlib supplies these at
different logical levels. The repair is
`AnalyticOnNhd.extract_zeros_eqOn_openSubset`: extract the finite divisor on a larger compact
`K`, factor on a connected open `V`, and explicitly prove `V subset K` and contour containment.

This domain distinction is now part of the reusable argument-principle API.

## First open theorem

The first unavailable preregistered theorem remains `LevinsonMontgomeryLogCountBound`.
Expanding the rectangle equality and taking imaginary parts leaves four vertical-side terms:
the real parts of the `zeta'/zeta` and `zeta''/zeta'` integrals on `Re(s)=0` and on the adaptive
line `Re(s)=r`.

The compiled top argument variations provide `O(log(t+2))`; the fixed bottom contributes only a
height-independent term. No existing project theorem currently controls or cancels those
vertical real integrals. The next attack is to formalize a zero-free vertical
logarithmic-modulus endpoint identity and determine whether available zeta and derivative
modulus bounds imply `O(log T)` uniformly in the adaptive `r`.

The subsequent all-real-cutoff transfer also remains open.

## Audit

- standalone new modules: compiled;
- `TargetChecks`, `Targets`, `AxiomsAudit`, and aggregate `LeanLab.lean` under
  `-DwarningAsError=true`: pass;
- selected axioms: only `propext`, `Classical.choice`, and `Quot.sound`;
- campaign placeholder and forbidden-declaration scan: empty;
- full local build: `8818/8818`, inherited warnings only.

## Classification

- `result=LEVINSON_MONTGOMERY_GLOBAL_COUNT_IDENTITY_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `negative_height_zero_exclusion_delta=1`;
- `finite_argument_principle_delta=1`;
- `open_left_adaptive_cutoff_delta=1`;
- `global_count_identity_delta=1`;
- `levinson_montgomery_log_count_bound_delta=0`;
- `levinson_montgomery_count_dichotomy_delta=0`;
- `speiser_equivalence_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

The full campaign endpoint
`LevinsonMontgomeryLogCountBound and LevinsonMontgomeryCountDichotomy` remains open. The
persistent RH Goal remains active.
