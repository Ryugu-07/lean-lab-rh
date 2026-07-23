# H1 Theta-Infinity Consumer Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`

Module: `LeanLab/Riemann/ThetaInfinityMollifier.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / FULL_BUILD_REQUIRED`

## Primary source boundary

The alignment source is Bettin--Gonek, arXiv:1604.02740, especially Theorem 1 and equations
`(1.1)`, `(2.1)`--`(2.5)`. Farmer 1993 supplies the historical `theta=infinity` conjecture;
Radziwill 2012 and Conrey et al. 2025 place the long- and short-mollifier mechanisms.

This module reconstructs the source objects, the integer-to-real cutoff interpolation, and the
final exponent/zero-free consumers. It does not reconstruct the Mellin inversion and contour
argument in `(2.2)`--`(2.5)` and does not prove Farmer's conjecture.

## Object alignment

| source object | Lean object | alignment |
| --- | --- | --- |
| `log(x/n)/log x` | `farmerLogTaper x n` | Literal real logarithmic taper. For `x>1,n>=1`, `farmerLogTaper_eq_one_sub` proves the affine form `1-log n/log x`. |
| `M_x(s) log x = sum_(n<=x) mu(n)n^(-s)log(x/n)` | `farmerMollifier x s` | Sum over `Finset.Icc 1 floor(x)` with complex Mobius coefficients and complex `cpow`; extended by zero for `x<=1`, agreeing with the source extension at `x=1`. |
| `1/2+it` | `farmerCriticalLinePoint t` | Literal critical-line coordinate in `Complex`. |
| `I_x(T1,T2)` | `farmerMollifiedMoment x T1 T2` | Oriented interval integral of `Complex.normSq (M_x*zeta)`; the comparison theorem assumes `T1<=T2`, matching the source use. |
| `I_N(0,T) <<_epsilon T^(1+epsilon)` uniformly for `2<=N<=T^theta` | `FarmerLongMollifierBound theta` | Explicit constants `C,T0`, positive `C`, `T0>=2`, and simultaneous natural-cutoff quantifiers. |
| arbitrary positive `theta` | `FarmerThetaInfinityConjecture` | Exact all-positive-`theta` wrapper around the uniform source bound. It is a definition of an open proposition, not a theorem. |
| `T^(2 beta theta) <<_epsilon T^(1+epsilon+theta)` | `BettinGonekPowerObstruction theta beta` | Every positive epsilon has a positive constant and an eventual-at-top real-power bound. |

## Integer-to-real cutoff edge

For `N<=x<=N+1`, define

```text
u = (1/log x - 1/log(N+1)) / (1/log N - 1/log(N+1)).
```

Lean proves `0<=u<=1`. The taper and fixed-cutoff polynomial satisfy

```text
M_x = u*M_N + (1-u)*M_(N+1).
```

At `x=N+1`, the newly admitted coefficient has taper `log 1/log(N+1)=0`; this closes the endpoint
without changing the polynomial. `complex_normSq_convex` then proves the pointwise bound after
multiplication by zeta. Continuity away from zeta's pole at `1` gives interval integrability, and
`farmerMollifiedMoment_interpolate` lifts the bound to `I_x(T1,T2)`.

This verifies the quantifier passage from integer `N` in Theorem 1 to real `y` under the integral
in the source proof. It reveals no counterexample or missing endpoint hypothesis.

## Exponent consumer

For fixed `theta>0`, `beta_le_of_bettinGonekPowerObstruction` chooses half the positive exponent
gap as epsilon. If `beta>1/2+1/(2*theta)`, division by the positive denominator power would bound a
strictly positive power of `T` by a constant, contradicting its limit to infinity.

The compiled consequences are:

- every nontrivial zero carrying the obstruction has real part at most
  `1/2+1/(2*theta)`;
- the same hypothesis excludes all zeta zeros strictly to the right of that boundary;
- if every nontrivial zero carries the obstruction for every positive `theta`, functional-equation
  reflection `rho -> 1-rho` forces exact real part `1/2`, hence Mathlib's `RiemannHypothesis`;
- `1/2+1/(4*theta)` is strictly off line but below the fixed-`theta` boundary, so one fixed theta
  is correctly classified as quasi-RH rather than RH.

## Conditional-source boundary

`BettinGonekMomentToPowerBridge theta` names the exact unformalized published analytic implication
from `FarmerLongMollifierBound theta` to the power obstruction for each nontrivial zero.
`farmerThetaInfinityConjecture_implies_riemannHypothesis` displays both the open Farmer conjecture
and this bridge as explicit premises. Neither premise is proved, and neither theorem may be used
as an unconditional input.

The next analytic edge contains Mellin inversion for `M_x`, holomorphy and decay of `G_t`, the
contour shift across a selected zero, the residue lower bound, Cauchy--Schwarz, the critical-line
zeta second-moment lower bound, and uniform constant bookkeeping.

## Mechanical status

- Production module: 482 lines and 12 selected axiom prints at the current endpoint.
- Exact TargetChecks: 12 new statement witnesses compile.
- Axiom audit: every selected declaration depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Production forbidden scan: empty in `ThetaInfinityMollifier.lean`.
- Direct compiles: production module, Targets, TargetChecks, and AxiomsAudit pass.
- Full build: `8,751` jobs passed.
- Frozen implementation: commit `ed9fb11e3293e80a86561f30eb05073bfbf0b7ab` passed public Lean
  Action run `29967710426`, build job `89082709000`, in `2m3s`.
- RH frontier delta: zero. Source-consumer delta: two. Route-map correction: one.
