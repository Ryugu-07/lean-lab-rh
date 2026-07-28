# Route Selection after H9 Conrey Actual-Seven Flat Interval

Date: 2026-07-29

Status: `RERANK_COMPLETE / H12_LEFT_HALF_PLANE_WINDING_SELECTED`

## Closed parent

Campaign `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01` is publicly closed at
`FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS`. Its final-ledger commit
`5dab6664c49e5e03effe9ac309256eaf91e5a171` passed Lean Action run `30401325481`, build job
`90416579015`, in `1m31s`; closure receipt
`fa3e22d4a8cf9dcd082eec3ef2d2d6b788b0d5ca` passed run `30401538278`, job
`90417268794`, in `1m36s`.

The campaign proves a genuine flat interval for the Legendre character modulo seven, but
`7 mod 8 = 7`; the source-permitted `q mod 8 = 3` branch remains open. Fresh cross-family
selection is therefore required.

## Cross-family comparison

| family | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H9 Conrey character sums | Prove or refute the flat-prefix branch for every squarefree `q>3` with `q mod 8 = 3`. | The new modulo-seven theorem shows that the omitted flat mechanism is real. The source family additionally forces `chi_q(2)=-1`, but no congruence, class-number, or monotonicity theorem is presently known that upgrades this distinction to a universal exclusion. Existing finite scans are navigation only. | Retain as a high-value arithmetic reserve; do not continue by recency alone. |
| H12 Speiser/Levinson--Montgomery | Formalize the source step that strict left-half-plane containment of `zeta'/zeta` forces zero change of argument. | The preceding admissible-contour campaign proved that mere nonvanishing does not control winding. The 1974 proof uses the stronger left-half-plane fact in exactly one printed inference before the argument-principle count. This positive theorem has not been formalized. | **Select.** |
| H7 spectral/Weil | Prove the true ground-state/prolate comparison or construct the infinite arithmetic operator. | The finite source blocks and Rayleigh consumer compile, but the remaining comparison is explicitly open in the modern source and requires a new infinite spectral input. | Retain open. |
| H10 function fields/trace | Construct a regularized number-field trace object or transfer the geometric mechanism. | The successful finite-field Hodge and spectral consumers compile; the number-field object is not supplied by the historical proof. | Retain open. |
| H1/H2/H11 analytic distribution | Supply a long mollified mean value, an actual exceptional-zero detector, or a sparse-exception amplifier. | These are high-value frontiers, but their next statements still require global estimates not produced by the current repository. | Retain open. |

H12 is selected because it has a literal source sentence whose hypothesis was sharpened by the
last H12 falsification. The endpoint is not the whole global count theorem: it isolates the
topological inference that the source actually uses and then connects it to an actual
`zeta'/zeta` horizontal segment. This is a materially new re-entry rather than another contour
existence or bounded-bottom lemma.

## Source lock

The fixed source is Norman Levinson and Hugh L. Montgomery,
*Zeros of the derivatives of the Riemann zeta-function*, Acta Mathematica 133 (1974), 49--65,
Theorem 1 and Section 2:

<https://doi.org/10.1007/BF02392141>

On page 52 the source places `zeta'/zeta` in the strict left half-plane on the closed indented
contour and concludes that its change of argument is zero. The same page then converts this
zero-winding statement, through the argument principle, into equality of the two zero counts.

The repository already compiles:

- the actual left and critical boundary signs above height ten;
- multiplicity-safe local critical-zero indentations;
- common zero-free horizontal slices;
- a nonvanishing closed exponential path with logarithmic-derivative integral `2*pi*I`.

The missing positive counterpart is that strict left-half-plane containment provides a single
principal logarithm branch, so the logarithmic-derivative integral telescopes and vanishes on a
closed path.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`.
- `node`: `H12-LM-LEFT-HALF-PLANE-WINDING-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: prove the generic endpoint-log formula for a differentiable path in the
  strict left half-plane, its closed-path zero-winding corollary, and the corresponding actual
  horizontal endpoint formula for `zeta'/zeta` on a strict-negative common zero-free slice.
- `meaningful_partial`: the generic closed-path theorem compiles and the first exact
  actual-ratio derivative obstruction is recorded.
- `negative_control`: retain the compiled nonvanishing winding-one exponential model; the new
  theorem must fail if strict left-half-plane containment is weakened to nonvanishing.
- `strict_boundary`: no negative horizontal slice, indented global contour, argument-principle
  count, Jensen top bound, Levinson--Montgomery count output, Speiser equivalence, derivative-zero
  exclusion, or RH may be inferred.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
