# H2 Half-Isolated Bow Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H2-HALF-ISOLATED-BOW-01`

Module: `LeanLab/Riemann/HalfIsolatedBowAudit.lean`

## Source crosswalk

| source object | Lean object | alignment | boundary |
| --- | --- | --- | --- |
| A `Y`-half-isolated zero `rho0` | `halfIsolatedIn zeros nearRadius similarWidth leftGap rho0` | Exact local logical form | The logarithmic source scales are explicit real parameters. |
| Nearby zero condition | `rho in zeros` and `dist rho rho0 <= nearRadius` | Exact metric cutoff | The finite model does not assert zeta multiplicity or analytic discreteness. |
| Similar real part and no smaller ordinate | `abs (rho.re-rho0.re) <= similarWidth` and `rho0.im <= rho.im` | Exact first branch | No strictness is added. |
| Sufficiently far to the left | `rho.re <= rho0.re-leftGap` | Exact second branch | `leftGap` is independent of `similarWidth` until a witness theorem assumes an ordering. |
| Functional-equation reflection in the upper half-plane | `criticalLineReflect rho = 1-star(rho)` | Exact critical-line reflection | This is only divisor geometry, not a proof that a finite set is a zeta divisor. |
| Finite fixed vertical lines | `rho.re=rho0.re` or `rho.re<=rho0.re-leftGap` | Source-shaped local consequence | The theorem assumes the local discrete gap rather than formalizing Hypothesis F globally. |
| Bottom of a rightmost vertical cluster | `hbottom` in `halfIsolatedIn_of_rightmost_bottom_and_verticalGap` | Exact extremal input | The theorem is finite/local geometry and does not produce a zeta cluster. |
| Bow obstruction | `finiteBow step rise` | Minimal three-point model | It tests the source disjunction and reflection symmetry only, not source-valid zero statistics. |

## Compiled conclusions

`halfIsolatedIn_of_rightmost_bottom_and_verticalGap` proves that discrete vertical separation plus
a bottom point supplies the full source disjunction for every nearby point.

`finiteBow_concreteCounterexample` gives a finite set invariant under `rho |-> 1-star(rho)`, with
a right off-line point and a nearby lower blocker. The blocker's real displacement is strictly
between the similar-width and left-gap thresholds, so it defeats both source branches. Every
right-side off-line point in the set therefore fails `halfIsolatedIn`.

`halfIsolatedBowAudit_endpoint` packages the positive finite-line theorem, the parameterized bow,
and a concrete nonvacuous witness.

## Claim boundary

- The module proves no statement about `riemannZeta`, its divisor, or a Dirichlet polynomial.
- The finite bow is not evidence that actual zeta bows exist.
- The countermodel rules out only a symmetry-only promotion to half-isolated detection.
- Maynard--Pratt's analytic short detector, its density estimate, actual bow exclusion, and RH
  remain open in the project.
