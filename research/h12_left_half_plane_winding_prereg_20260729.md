# H12 Levinson--Montgomery Left-Half-Plane Winding Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`

Node: `H12-LM-LEFT-HALF-PLANE-WINDING-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary source and exact inference

The fixed source is Norman Levinson and Hugh L. Montgomery,
*Zeros of the derivatives of the Riemann zeta-function*, Acta Mathematica 133 (1974), 49--65,
Theorem 1 and Section 2:

<https://doi.org/10.1007/BF02392141>

On page 52 the source proves strict negativity of the real part of `zeta'/zeta` on the left
vertical boundary and on a suitably indented critical boundary. If the same strict negativity
holds on a cofinal horizontal boundary, the image of the complete closed contour lies in the
strict left half-plane. The source then concludes that the change in argument of `zeta'/zeta`
is zero and invokes the argument principle to equate the zeta and zeta-derivative counts.

Campaign `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01` proved that common
nonvanishing alone is not enough: an everywhere-nonzero closed exponential path has
logarithmic-derivative integral `2*pi*I`. The present campaign attacks the exact stronger
source inference. It does not preregister the entire argument-principle count or Jensen top
estimate.

## Material re-entry difference

The predecessor campaign constructed zero-free horizontal slices and bounded a fixed unsigned
bottom contribution. It stopped after falsifying the proposal that nonvanishing itself controls
winding.

This campaign supplies the positive theorem separated by that falsification:

```text
strict left-half-plane image
  -> one principal logarithm branch for the negated path
  -> endpoint difference for the logarithmic-derivative integral
  -> zero integral on a closed path.
```

No new finite-height search, numerical bottom, or asymptotic constant is involved.

## M0 definition alignment

1. The source ratio `zeta'(s)/zeta(s)` is
   `deriv riemannZeta s / riemannZeta s`.
2. A strict-negative horizontal slice includes both endpoints
   `s=sigma+t*I`, `0<=sigma<=1/2`, and asserts nonvanishing of both `zeta` and `zeta'`.
3. Strict negativity means the real part of the actual ratio is negative. It is stronger than
   `SpeiserCommonZeroFreeHorizontal`.
4. The negated ratio then has positive real part and lies in Mathlib's principal-log slit plane.
   No arbitrary logarithm branch or choice axiom is introduced.
5. The path logarithmic derivative is the real-parameter derivative divided by the path value.
   For the actual horizontal ratio it equals
   `logDeriv (deriv riemannZeta) - logDeriv riemannZeta`.
6. A closed-path zero-winding theorem is a boundary identity only. It does not count interior
   zeros without a separately proved argument principle.
7. Critical-line zeta zeros require the already compiled local semicircle indentations in a
   later global assembly. They are not silently crossed by the horizontal theorem.

## Proposed Lean spine

The generic analytic core is:

```lean
theorem intervalIntegral_deriv_div_eq_log_sub_of_re_neg
    {g g' : Real -> Complex} {a b : Real}
    (hderiv : forall x, x ∈ Set.uIcc a b -> HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) volume a b)
    (hneg : forall x, x ∈ Set.uIcc a b -> (g x).re < 0) :
    (∫ x in a..b, g' x / g x) =
      Complex.log (-g b) - Complex.log (-g a)

theorem intervalIntegral_deriv_div_eq_zero_of_re_neg_of_eq
    {g g' : Real -> Complex} {a b : Real}
    (hderiv : forall x, x ∈ Set.uIcc a b -> HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) volume a b)
    (hneg : forall x, x ∈ Set.uIcc a b -> (g x).re < 0)
    (hclosed : g b = g a) :
    (∫ x in a..b, g' x / g x) = 0
```

The actual source-facing objects are:

```lean
def speiserZetaDerivRatio (s : Complex) : Complex :=
  deriv riemannZeta s / riemannZeta s

def SpeiserStrictNegativeHorizontal (t : Real) : Prop :=
  0 < t ∧
    forall sigma, sigma ∈ Set.Icc (0 : Real) (1 / 2) ->
      riemannZeta (sigma + t * Complex.I) ≠ 0 ∧
      deriv riemannZeta (sigma + t * Complex.I) ≠ 0 ∧
      (speiserZetaDerivRatio (sigma + t * Complex.I)).re < 0
```

The fixed actual endpoint is an exact horizontal formula:

```lean
theorem intervalIntegral_speiserZetaDerivRatio_horizontal
    {t : Real} (ht : SpeiserStrictNegativeHorizontal t) :
    (∫ sigma : Real in (0 : Real)..(1 / 2),
      (logDeriv (deriv riemannZeta) (sigma + t * Complex.I) -
        logDeriv riemannZeta (sigma + t * Complex.I))) =
      Complex.log (-speiserZetaDerivRatio (1 / 2 + t * Complex.I)) -
        Complex.log (-speiserZetaDerivRatio (t * Complex.I))
```

Names may change only to satisfy local naming conventions; the statement strength and actual
function may not be weakened.

## Success and meaningful-partial criteria

`FULL_SUCCESS` requires:

1. the generic endpoint-log formula;
2. the generic closed-path zero-winding corollary;
3. the actual `zeta'/zeta` ratio and strict-negative horizontal definition;
4. the exact derivative identity connecting the ratio path to the difference of the two actual
   logarithmic derivatives;
5. the actual horizontal endpoint-log formula;
6. exact TargetChecks, selected standard-only axiom prints, forbidden scans, warning-as-error
   compilation, `git diff --check`, and a full build.

`MEANINGFUL_PARTIAL` requires items 1--2 and an exact record of the first failed actual-ratio
derivative or integrability statement. A theorem that merely assumes the endpoint formula is not
a meaningful partial.

## Falsification and negative controls

The attack is falsified or must be narrowed if:

- strict left-half-plane containment does not imply membership of the negated path in the
  principal-log slit plane;
- the fundamental theorem of calculus cannot be applied under the registered derivative and
  interval-integrability hypotheses;
- the actual horizontal derivative is not the source difference
  `logDeriv zeta' - logDeriv zeta`;
- endpoint inclusion or totalized division makes the actual statement vacuous.

The inherited theorem `integral_logDeriv_speiserNonzeroWindingModel` is the mandatory negative
control. It proves that the conclusion cannot be generalized from strict left-half-plane paths
to arbitrary nonvanishing closed paths.

## Known obstacles and nearest compiled facts

- `SpeiserAdmissibleContour.lean` supplies common actual zero-free horizontal slices,
  integrability of both logarithmic derivatives, and the winding-one nonvanishing model.
- `LevinsonMontgomeryBoundarySigns.lean` supplies actual strict signs on the vertical sides.
- `LevinsonMontgomeryCriticalIndentation.lean` supplies multiplicity-safe local strict signs on
  critical-zero semicircles.
- Mathlib supplies the principal complex logarithm derivative on `Complex.slitPlane` and the
  interval-integral fundamental theorem.
- The remaining global assembly must enumerate and orient finitely many indentation arcs and
  prove the argument principle for the actual zeta-derivative divisor. This campaign does not
  assume either result.

## Assumption and implication frontier

Before and after preregistration:

- no strict-negative actual horizontal height is known;
- no global indented contour or exact count identity is known;
- `LevinsonMontgomeryLogCountBound` and `LevinsonMontgomeryCountDichotomy` remain open;
- Speiser's unconditional equivalence, derivative-zero exclusion, H12, and RH remain open.

Full success closes one source topological inference and gives an actual horizontal edge formula.
It is historical-route infrastructure with `rh_frontier_delta=0`.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1; no serving token budget is exposed.
- `compaction_state`: resumed from a generated summary after the H9 closure; canonical
  governance, HANDOFF, Targets, current attempts, hard-gap DAG, H9/H12/H7/H10 frontiers, and both
  fixed primary sources were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit and push this docs-only preregistration first. Public Lean Action CI must pass before
editing any `LeanLab/` proof source, target registry, exact check, or axiom-audit file.
