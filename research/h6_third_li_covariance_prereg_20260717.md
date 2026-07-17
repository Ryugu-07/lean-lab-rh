# H6 Third-Li Covariance Discovery Preregistration

Date: 2026-07-17

Campaign: `DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`

Mode: `DISCOVERY`

Status: `LOCAL_FORMALIZATION_COMPLETE_PUBLIC_IMPLEMENTATION_CI_PENDING`

## Exact source extension

Keep the public definitions `deBruijnNewmanHeatXi`, moments `A_t,B_t,C_t`, and standard
`deBruijnNewmanHeatLiOne/Two`. Add

`D_t = integral_(0,infinity) u^3 * exp(t*u^2) * Phi(u) * sinh(u) du`

and the standard third Li differential expression

`heatLiThree(t) = 3*L_t(1) + 3*L_t'(1) + (1/2)*L_t''(1)`,

where `L_t=logDeriv(heatXi_t)`.

## Fixed mathematical endpoint

The campaign succeeds only if Lean proves all of the following without a new hypothesis:

1. `D_t` is integrable for every real `t`, and the third spatial derivative at `s=1` is exactly
   `64*D_t`;
2. for every real `t`,
   `B_t*C_t <= A_t*D_t`;
3. for every real `t`, `heatLiThree(t)` equals
   `6*b_t + 12*(c_t-b_t^2) + 4*d_t - 12*b_t*c_t + 8*b_t^3`, cast to `Complex`, where
   `b_t=B_t/A_t`, `c_t=C_t/A_t`, and `d_t=D_t/A_t`;
4. `heatLiThree(0) = liCoefficientCandidate 2`, with the existing project convention in which
   candidate index `2` is the standard third Li coefficient;
5. `0 < (liCoefficientCandidate 2).re` and `(liCoefficientCandidate 2).im=0`;
6. the sign proof explicitly uses the compiled time-zero bridge and
   `liCoefficientCandidate_zero_re_lt_one`, not a floating-point estimate.

Definitions and theorem names may be adjusted to local style; none of these mathematical clauses
may be weakened or omitted.

## Proposed Lean surface

```lean
def deBruijnNewmanHeatLiMomentD (t : Real) : Real :=
  integral fun u => u^3 * exp (t*u^2) * deBruijnNewmanPhi u * sinh u

def deBruijnNewmanHeatLiThree (t : Real) : Complex :=
  3 * logDeriv (deBruijnNewmanHeatXi t) 1 +
    3 * deriv (logDeriv (deBruijnNewmanHeatXi t)) 1 +
    (1 / 2) * iteratedDeriv 2 (logDeriv (deBruijnNewmanHeatXi t)) 1

theorem deBruijnNewmanHeatLiMomentB_mul_C_le_A_mul_D (t : Real) :
  deBruijnNewmanHeatLiMomentB t * deBruijnNewmanHeatLiMomentC t <=
    deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentD t

theorem deBruijnNewmanHeatLiThree_zero_eq_candidate_two :
  deBruijnNewmanHeatLiThree 0 = liCoefficientCandidate 2

theorem liCoefficientCandidate_two_re_pos :
  0 < (liCoefficientCandidate 2).re
```

The final integral definition will retain the existing `Set.Ioi 0` restricted-measure notation.

## Covariance certificate

Use the positive weight

`W_t(u)=exp(t*u^2)*Phi(u)*cosh(u)`,

and coordinates `X(u)=u*tanh(u)`, `Y(u)=u^2`. Then `A=int W`, `B=int W*X`,
`C=int W*Y`, and `D=int W*X*Y`.

The preferred one-integral certificate sets `m=C/A` and `r=sqrt(m)`. Since `X` and `Y` are
monotone on the positive half-line and `Y(r)=m`,

`W(u)*(X(u)-X(r))*(Y(u)-m) >= 0`.

After justified expansion and integration, the `X(r)` terms cancel because `m*A=C`, leaving
`D-(C/A)*B>=0`. This must be converted to `B*C<=A*D` using the compiled proof `A>0`.
A product-measure/Fubini Chebyshev proof is an allowed fallback, but every integrability exchange
must be explicit.

## DAG and strength

- `node_id`: H6-X3, a finite necessary-condition child below H6-X/L1 and H6-E/G8.
- `relation_to_RH`: `liCoefficientCandidate 2 > 0` is an unconditional necessary condition for RH
  and is strictly weaker than the all-index criterion. It neither implies RH nor reduces G8.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH are open.
- `expected_hard_gap_delta`: 0.
- `expected_route_infrastructure_delta`: 1 only if the covariance mechanism, exact third formula,
  and actual Li-index sign all compile.
- `novelty_label`: `NOVELTY_UNCHECKED`; no first-formalization or priority claim is permitted.

## Boundary and falsification tests

- Recheck all factors `8,16,32,64` in `F,F',F'',F'''` under
  `z=-i*(2*s-1)`.
- Derive the coefficient `1/2` in the third standard Li expression from the project definition,
  rather than treating the new expression as definitionally identical to candidate index `2`.
- Test the covariance proof at one-atom and two-atom positive measures and at `C=0`.
- Confirm that monotonicity is used only on `u>0` and that `sqrt(C/A)` lies in its closure.
- Confirm all `D` and covariance integrands are Bochner integrable before expansion.
- The compiled positive-cosh counterexample must fail the small-mean condition rather than one of
  the claimed universal covariance inequalities.
- A mismatch with `liCoefficientCandidate 2`, a failed exact derivative factor, or an exact
  counterexample to `B*C<=A*D` falsifies the registered route.

## Closest primary literature

- X.-J. Li, J. Number Theory 65 (1997), 325-333, DOI `10.1006/jnth.1997.2137`.
- E. Bombieri and J. C. Lagarias, J. Number Theory 77 (1999), 274-287.
- D. H. J. Polymath, arXiv:1904.12438.
- M. W. Coffey, J. Comput. Appl. Math. 166 (2004), 525-534, DOI
  `10.1016/j.cam.2003.09.003`.
- K. Maslanka, arXiv:math/0402168.

The bounded search found derivative positivity and numerical Li evaluations, but not the exact
registered weighted-covariance proof. This is an originality rationale only.

## Success and stop conditions

- `success`: all six endpoint clauses compile; exact Targets and TargetChecks, selected axiom
  prints, forbidden scans, definition alignment, standalone compile, full build, and public CI
  pass.
- `falsification`: any fixed factor, covariance inequality, Li-index bridge, or final sign is
  false and the failure is recorded as an `OBS` node.
- `obstruction`: a precise missing monotone-integral, third-differentiation, or standard-Li bridge
  statement remains after attempting both the preferred and fallback proofs.
- `local_stop`: close at the actual candidate-two sign theorem or at a precise falsification or
  obstruction. Do not replace the endpoint by a fourth-moment definition, an abstract covariance
  helper, or another finite coefficient.

No Lean proof source has been edited in this campaign before this preregistration.

## Gate update

Preregistration commit `6c1c8c0defb2186ef20701ae9e33ca6be95c4daa` passed public Lean Action CI
run `29544246770`, build job `87772850526`, in `1m45s`, before any Lean proof-source edit.

All six fixed endpoint clauses now compile in `DeBruijnNewmanThirdLi.lean`, bundled as
`deBruijnNewmanHeat_thirdLi_covariance_endpoint`. Exact Targets/TargetChecks, selected
standard-only axiom prints, empty forbidden scans, `git diff --check`, and the 8,695-job full
build pass locally. Classification is `DISCOVERY_FORMALIZED_LOCAL`, `hard_gap_delta=0`, and
`route_infrastructure_delta=1`; implementation public CI and immutable evidence closure remain.
