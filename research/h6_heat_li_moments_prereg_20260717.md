# H6 Heat-Li Moment Discovery Preregistration

Date: 2026-07-17

Campaign: `DISCOVERY-20260717-H6-HEAT-LI-MOMENTS-01`

Mode: `DISCOVERY`

Status: `PREREGISTERED_PUBLIC_CI_PENDING`

## Exact source definitions

For real `t` and complex `s`, define the source-normalized heat-Xi coordinate

`heatXi_t(s) = 8 * H_t(-i*(2*s-1))`.

Define the first two Li-type quantities with the same project convention used by the existing
zero- and one-index coefficient spine:

`heatLiOne(t) = logDeriv(heatXi_t)(1)`,

`heatLiTwo(t) = 2*logDeriv(heatXi_t)(1) + (logDeriv(heatXi_t))'(1)`.

Define real source moments on `(0,infinity)`:

- `A_t = integral exp(t*u^2)*Phi(u)*cosh(u) du`;
- `B_t = integral u*exp(t*u^2)*Phi(u)*sinh(u) du`;
- `C_t = integral u^2*exp(t*u^2)*Phi(u)*cosh(u) du`.

## Fixed mathematical endpoint

For every real `t`, prove all of the following without extra hypotheses:

1. `heatXi_t(1) != 0`;
2. `heatLiOne(t) = 2*B_t/A_t` and is a positive real number;
3. `heatLiTwo(t) = 4*(A_t*B_t + A_t*C_t - B_t^2)/A_t^2`;
4. `B_t^2 <= A_t*C_t`, with a kernel-checked weighted Cauchy-Schwarz certificate;
5. `heatLiTwo(t)` is a positive real number.

## Proposed Lean surface

```lean
def deBruijnNewmanHeatXi (t : ℝ) (s : ℂ) : ℂ :=
  8 * deBruijnNewmanH t (-Complex.I * (2 * s - 1))

def deBruijnNewmanHeatLiOne (t : ℝ) : ℂ :=
  logDeriv (deBruijnNewmanHeatXi t) 1

def deBruijnNewmanHeatLiTwo (t : ℝ) : ℂ :=
  2 * logDeriv (deBruijnNewmanHeatXi t) 1 +
    deriv (logDeriv (deBruijnNewmanHeatXi t)) 1

theorem deBruijnNewmanHeatMoment_one_sq_le_zero_mul_two (t : ℝ) :
  deBruijnNewmanHeatMomentOne t ^ 2 <=
    deBruijnNewmanHeatMomentZero t * deBruijnNewmanHeatMomentTwo t

theorem deBruijnNewmanHeatLi_first_two_re_pos (t : ℝ) :
  0 < (deBruijnNewmanHeatLiOne t).re ∧
    0 < (deBruijnNewmanHeatLiTwo t).re
```

Exact names may change only to match established project naming; the mathematical clauses may not
be weakened.

## DAG and strength

- `node_id`: H6-X below H6-E/G8 and the all-index Li criterion L2.
- `relation_to_RH`: finite necessary conditions only. The conjunction for two coefficients is
  strictly weaker than RH and is not recorded as a hard-gap reduction.
- `all_index_warning`: extending the positivity conclusion to every Li index at `t=0` is
  RH-equivalent by the compiled Li criterion. No finite result may be extrapolated.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH remain open.
- `expected_hard_gap_delta`: 0.
- `expected_route_infrastructure_delta`: 1 only if the exact positive-moment mechanism compiles.

## Known obstacles and adversarial tests

- **Generic heat-family countermodel:** `H6ReverseHeatLiAudit.lean` has a reflection-symmetric heat
  polynomial with negative second Li value. Therefore the heat PDE, symmetry, and later real zeros
  are insufficient; the positive theta-transform representation is indispensable.
- **Normalization:** verify `F(1)=8*A`, `F'(1)=16*B`, and `F''(1)=32*C`; a missed factor or heat sign
  invalidates the endpoint.
- **Strictness:** nonnegativity of Cauchy-Schwarz is insufficient by itself. Strict positivity must
  come from `A_t>0` and `B_t>0` on a positive-measure subset.
- **Integrability:** prove the square-integrability needed by Holder/Cauchy-Schwarz from the public
  all-time double-exponential majorant; no formal integral manipulation is accepted.
- **Division:** every quotient rewrite must carry the proved `A_t != 0` witness.
- **Complex/real alignment:** both Li quantities must be shown equal to explicit real casts before
  their real-part signs are used.

## Closest known results

The source heat family and its normalization are from D. H. J. Polymath, arXiv:1904.12438. The
all-index context is Li's criterion and the Bombieri-Lagarias zero criterion, already specialized
in the project at `t=0`. A bounded primary-source search found no exact theorem matching this
all-real-time first-two source-moment endpoint. This is only an originality rationale for the
attempt, not a novelty claim.

## Success, falsification, and stop conditions

- `success`: every fixed clause compiles, exact TargetChecks and selected axiom prints pass, the
  definition and moment normalization audit passes, forbidden scans and full build pass, and the
  implementation commit passes public CI.
- `falsification`: Lean proves a fixed moment formula has a different factor/sign, the weighted
  Cauchy-Schwarz inequality cannot hold for the exact positive source weight, or a concrete source
  time violates one of the registered signs.
- `obstruction`: the endpoint reduces to a precise missing measure/integrability theorem that
  cannot be derived from the compiled majorants without introducing an unproved hypothesis.
- `local_stop`: success, falsification, or a precise obstruction returns the persistent RH Goal to
  `ROUTE_SELECTION`. No result here closes H6-E or the global Goal.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.
