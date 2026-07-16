# H6 de Bruijn-Newman Entire Heat Equation Pre-Registration

Campaign: `CAMPAIGN-20260717-H6-HEAT-EQUATION-01`

Mode: `LITERATURE`

Status: `PREREGISTERED`

## Exact source endpoint

Use the already compiled source-normalized definitions

`H_t(z) = integral_(0,infinity) exp(t*u^2) * Phi(u) * cos(z*u) du`

from `LeanLab/Riemann/DeBruijnNewman.lean`. The indivisible endpoint is the following joint
analytic statement for every real `t` and complex `z`:

1. `z -> H_t(z)` is complex differentiable on all of `C`;
2. `t -> H_t(z)` is real differentiable, with derivative obtained by inserting `u^2`;
3. the second complex derivative in `z` is obtained by inserting `-u^2`;
4. consequently `partial_t H_t(z) = -partial_z^2 H_t(z)`.

The quantifier over `t` may not be weakened to `t >= 0`, and the endpoint may not be obtained by
introducing a new abstract heat family unrelated to the compiled source integral.

## Proposed Lean surface

Exact helper names may be adjusted to local style, but the final statements and quantifiers may
not be weakened:

```lean
theorem differentiable_deBruijnNewmanH (t : Real) :
    Differentiable Complex (deBruijnNewmanH t)

theorem hasDerivAt_deBruijnNewmanH_time (t : Real) (z : Complex) :
    HasDerivAt (fun tau : Real => deBruijnNewmanH tau z)
      (integral fun u in Set.Ioi 0 =>
        (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : Real) : Complex) *
          Complex.cos (z * (u : Complex)))) t

theorem deriv_deriv_deBruijnNewmanH (t : Real) (z : Complex) :
    deriv (deriv (deBruijnNewmanH t)) z =
      -(integral fun u in Set.Ioi 0 =>
        (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : Real) : Complex) *
          Complex.cos (z * (u : Complex))))

theorem deBruijnNewmanH_backward_heat_equation (t : Real) (z : Complex) :
    deriv (fun tau : Real => deBruijnNewmanH tau z) t =
      -deriv (deriv (deBruijnNewmanH t)) z
```

The restricted-integral syntax may change to match mathlib elaboration. The derivative values,
the minus sign, and the full real/complex quantifiers may not.

## Success and falsification

Success requires:

1. a reusable domination theorem proving integrability after arbitrary fixed quadratic and linear
   exponential weights and at least the `u^2` moment needed by both derivatives;
2. differentiation under the integral in real time and twice in the complex spatial variable;
3. the exact entire-family and backward-heat-equation endpoints above;
4. exact TargetChecks, transitive standard-only axiom audit, forbidden scans, full local build,
   and public CI.

The campaign records `DEPENDENCY_GAP_IDENTIFIED` if arbitrary-real-time domination reduces to a
precise absent integration theorem, or if mathlib's parameter-integral API cannot establish
complex differentiation without a new general theorem. Proving only continuity, only a bounded
time interval, only real `z`, or only a formal pointwise integrand identity does not close the
campaign.

## Source and DAG position

- Primary modern source: D. H. J. Polymath,
  [arXiv:1904.12438](https://arxiv.org/abs/1904.12438), which defines the displayed integral for
  every real `t`, calls `H_t` entire, and uses its heat-flow evolution.
- Independent normalization source: Rodgers and Tao,
  [arXiv:1801.05914](https://arxiv.org/abs/1801.05914).
- `node_id`: `H6-H`
- `relation_to_RH`: source analytic infrastructure below the all-real-zero and `Lambda <= 0`
  endpoint; no zero-location theorem follows from the PDE alone.
- `assumption_frontier_before`: H6-B is public and compiled, so the exact source `H_t` is connected
  to project xi at `t=0`; no differentiability or heat-equation theorem is available for `t != 0`.
- `hard_gap_before`: H6-E/G8 (`Lambda <= 0`), W2/G7, M2/G3, and RH are open.
- `expected_hard_gap_delta`: 0
- `expected_route_infrastructure_delta`: 1 only if all four endpoint clauses compile.

## Route selection and known obstacle

The selection compared H6-H against H6-X, direct H6-E/H6-Q, H1-B, H2-B, H10 census work,
W2/G7, and M2/G3.

- H6-X needs an entire heat family and exact derivative control before its genus/order hypotheses
  can be stated honestly.
- Direct H6-E and H6-Q have higher endpoint value but currently lack the compiled analytic and
  all-real-zero framework needed even to express their source argument faithfully.
- H1-B and H2-B are finite-count infrastructure with less immediate leverage.
- H10 remains the next required census card, but its curve/product/Frobenius mechanism has little
  overlap with the present Lean analytic stack and is not displaced or rejected by this choice.
- W2/G7 and M2/G3 remain open, but the prior tested mechanisms supply no materially new attack
  angle for this selection loop.

The fixed technical obstacle is domination of

`u^k * exp(c*u^2 + d*u) * Phi(u)`

on `(0,infinity)` for arbitrary fixed real `c,d` and `k <= 2`, uniformly on neighborhoods of the
time and spatial parameters. The intended attack is to split the double exponential
`exp(-pi*n^2*exp(4*u))` into a summable index factor and a super-exponentially decaying `u` factor,
then apply mathlib's dominated parameter-integral theorem. Do not split this chain into separate
campaigns.
