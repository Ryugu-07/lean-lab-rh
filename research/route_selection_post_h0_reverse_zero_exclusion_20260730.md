# Route Selection after H0 Reverse Zero Exclusion

Date: 2026-07-30

Status: `SELECTED_CAMPAIGN_LOCAL_SUCCESS / ARGUMENT_VARIATION_NEXT_OPEN`

## Closed parent

Campaign `LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01` is public-green
through closure-ledger commit `897d27006fccaf9f6c74517f9b08289dc97cb909`, Lean Action
run `30524823723`, build job `90813231404`, in `2m8s`.

It closes only the conditional analytic implication from every positive-epsilon Chebyshev
error estimate to `Mathlib.RiemannHypothesis`. The error estimate itself, H0, and RH remain
open.

## Selection rule

Historical coverage is omission search. The comparison prioritizes a human proof inference
that:

1. was compressed, discarded, or carried by a stronger premise than the final consumer needs;
2. is close to a genuine RH-relevant theorem rather than a detached analogue;
3. has a falsifiable fixed endpoint;
4. can expose a cross-route producer even if the endpoint fails.

Original conjectures, falsification, and direct RH attacks remain open throughout.

## Cross-family comparison

| family or subroute | first live historical edge | omission reading | decision |
| --- | --- | --- | --- |
| H12 Levinson--Montgomery/Speiser | Reconstruct the sentence on page 52 that Jensen's theorem gives `O(log T)` argument variation for actual `zeta` and `zeta'` across the top horizontal side. | The source compresses analyticity, a real-part symmetrization, center lower bounds, fixed-disc polynomial growth, Jensen zero counting, and the crossing-to-argument passage into one sentence. Mathlib now contains Jensen's inequality, while the project already contains the actual divisor, indentation, boundary, and count consumers. | **Select.** |
| H1 Selberg/Levinson--Conrey | Prove the global mollified moment and actual auxiliary-function count. | Historically central, but recent source audits reduce the first producer to broad off-diagonal mean values with no newly exposed smaller inference. | Retain open. |
| H2 zero density | Prove the fixed short-Mobius twisted fourth moment or Type-I rarity. | The complete Type-II consumer is compiled and the remaining producer survived three shortcut audits. Immediate return would repeat the same deep moment obstruction. | Retain open. |
| H7/H8 spectral and RKHS | Construct the actual arithmetic operator, true ground-state rate, or concrete `F(W)` space. | High omission value, but the missing objects are still coupled global constructions rather than one newly separable source inference. | Retain open. |
| H10 function fields | Build a general-curve one-point pole filtration and Riemann--Roch dimension producer. | The rational-function-field realization compiles, but current Mathlib has no Riemann--Roch infrastructure for the required smooth projective curve. | Retain open and continue source/library reconnaissance. |
| H11 pair correlation | Instantiate the moving-window diagonal with the actual PCC remainder and complete the Fejer/Fujii calculation. | The logical diagonal is closed, but the source-facing asymptotic remains a broad analytic package. | Retain open. |

H12 is not selected because Jensen's inequality is available in isolation. It is selected
because the unformalized source sentence is the first exact global analytic producer after a
large compiled collection of local Levinson--Montgomery components. A failed actual
instantiation will locate the obstruction in fixed-strip zeta growth, derivative normalization,
or conversion from real-part crossings to argument variation.

## Primary-source lock

Norman Levinson and Hugh L. Montgomery,
*Zeros of the derivatives of the Riemann zeta-function*, Acta Mathematica 133 (1974),
49--65:

- stable PDF:
  `https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf`;
- DOI: `https://doi.org/10.1007/BF02392141`.

On page 52, after proving the vertical and indented critical-line signs, the source states that
a standard use of Jensen's theorem gives

```text
change in arg zeta(sigma+iT) = O(log T),
change in arg zeta'(sigma+iT) = O(log T)
```

as `sigma` runs from `1` to `0`. This is then combined with the other contour sides to obtain
the count comparison `N_1^-(T)=N^-(T)+O(log T)`.

## Fixed next campaign

- `campaign`:
  `LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`;
- `node`: `H12-LM-JENSEN-TOP-REAL-ZERO-COUNT-01`;
- `mode`: `LITERATURE / OMISSION-AUDIT / PROOF-ATTEMPT`;
- `full_endpoint`: for the actual zeta and actual zeta derivative, construct the source
  real-part analytic symmetrizations, prove uniform polynomial sphere bounds and nonvanishing
  center lower bounds on one fixed Jensen disc, and derive an `O(log T)` bound for their
  multiplicity-bearing divisor counts in a smaller disc containing `[0,1]`;
- `source_corollary`: every real-part crossing on the top segment lies among those divisor
  zeros, so the actual crossing count is `O(log T)`;
- `next_composition`: convert the crossing count into the logarithmic-derivative argument
  variation and compose it with the separately open indented argument-principle count;
- `negative_controls`: a global finite-order exponential-square estimate gives only a
  quadratic Jensen numerator; the unrotated dominant term of `zeta'` has an oscillating real
  part, so a phase-normalized derivative symmetrization is required;
- `strict_boundary`: this campaign does not assume or prove RH, does not prove the full
  Levinson--Montgomery count theorem unless the argument-principle layer also compiles, and
  does not treat an abstract Jensen inequality as the actual zeta endpoint;
- `production_gate`: no `LeanLab/` or theorem-registration edit before this docs-only
  preregistration passes public Lean Action CI.

The persistent RH Goal remains active.

## Campaign outcome

The selected omission was reconstructible for the actual zeta objects. The complete local
Jensen producer now compiles: fixed-disc analyticity, polynomial bounds for zeta and its
derivative, quantitative center separation, logarithmic multiplicity-bearing divisor counts,
and real-crossing inclusion.

The source sentence still compresses one distinct topological-analytic edge not supplied by
Jensen alone: turn the ordered real-part crossings into the continuous change of argument used
by the horizontal contour. This is the first H12 successor to compare against non-adjacent
historical candidates; it is not automatically selected merely because it is adjacent.
