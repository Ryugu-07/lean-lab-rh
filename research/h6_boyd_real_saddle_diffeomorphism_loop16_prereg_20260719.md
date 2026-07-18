# H6 Boyd Real Saddle Diffeomorphism Loop 16 Preregistration

Date: 2026-07-19

Campaign: `FORMALIZATION-20260719-H6-BOYD-REAL-SADDLE-DIFFEO-01`

Mode: `LITERATURE`

Status: `IMPLEMENTATION_PUBLIC; CLOSURE_EVIDENCE_PENDING`

## Exact target

For real `u`, define the real restriction of the Loop 15 phase and its normalized removable
factor by

```text
phaseR(u) = exp(u)-u-1,
factorR(0) = 1,
factorR(u) = 2*phaseR(u)/u^2  when u != 0,
wR(u) = u*sqrt(factorR(u)).
```

Prove the exact bridge to the existing complex coordinate and the full real-axis geometry:

```text
wC((u:C)) = (wR(u):C),
0 < factorR(u),
wR(u)^2/2 = phaseR(u),
0 < deriv(wR,u),
wR is strictly increasing,
wR(u) -> -infinity as u -> -infinity,
wR(u) -> +infinity as u -> +infinity.
```

Construct the resulting order isomorphism `wR : R ~=o R`, its inverse `uR`, and prove

```text
uR(wR(u)) = u,
wR(uR(w)) = w,
deriv(uR,w) = 1 / deriv(wR,uR(w)) > 0.
```

For `x>0`, define the exact Gaussian-coordinate integrand

```text
gaussianJacobian(x,w) = deriv(uR,w) * exp(-x*w^2/2).
```

Prove its integrability and the exact global change of variables

```text
integral_R gaussianJacobian(x,w) dw
  = integral_R exp(-x*(exp(u)-u-1)) du,

GammaStar(x)
  = sqrt(x/(2*pi)) * integral_R gaussianJacobian(x,w) dw.
```

Finally record the first complex continuation obstruction supplied by the source saddle geometry.
For

```text
saddle(n) = n*(2*pi*i),  n in Z,
```

prove for every `n != 0` that the Loop 15 coordinate is analytic at `saddle(n)`, has derivative
zero there, and satisfies

```text
wC(saddle(n))^2 = -2*saddle(n) = -4*pi*i*n.
```

In particular, `n=1` and `n=-1` are the two adjacent source saddles. This locates their critical
images; it does not construct a global complex inverse branch or a resurgence contour.

## Proposed Lean declarations

```lean
def deBruijnNewmanPolymathBoydRealSaddlePhase (u : R) : R :=
  Real.exp u - u - 1

def deBruijnNewmanPolymathBoydRealSaddleFactor (u : R) : R :=
  if u = 0 then 1 else
    2 * deBruijnNewmanPolymathBoydRealSaddlePhase u / u ^ 2

def deBruijnNewmanPolymathBoydRealSaddleCoordinate (u : R) : R :=
  u * Real.sqrt (deBruijnNewmanPolymathBoydRealSaddleFactor u)

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ofReal (u : R) :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate (u : C) =
      (deBruijnNewmanPolymathBoydRealSaddleCoordinate u : C)

theorem deBruijnNewmanPolymathBoydRealSaddleFactor_pos (u : R) :
    0 < deBruijnNewmanPolymathBoydRealSaddleFactor u

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq (u : R) :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate u ^ 2 / 2 =
      deBruijnNewmanPolymathBoydRealSaddlePhase u

theorem deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_pos (u : R) :
    0 < deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_strictMono :
    StrictMono deBruijnNewmanPolymathBoydRealSaddleCoordinate

theorem tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atBot :
    Tendsto deBruijnNewmanPolymathBoydRealSaddleCoordinate atBot atBot

theorem tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atTop :
    Tendsto deBruijnNewmanPolymathBoydRealSaddleCoordinate atTop atTop

noncomputable def deBruijnNewmanPolymathBoydRealSaddleOrderIso : R ~=o R :=
  -- the strictly increasing surjection above

noncomputable def deBruijnNewmanPolymathBoydRealSaddleInverse : R -> R :=
  deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm

theorem hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse (w : R) :
    HasDerivAt deBruijnNewmanPolymathBoydRealSaddleInverse
      (deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate
        (deBruijnNewmanPolymathBoydRealSaddleInverse w))^-1 w

def deBruijnNewmanPolymathBoydGaussianSaddleIntegrand (x w : R) : R :=
  deriv deBruijnNewmanPolymathBoydRealSaddleInverse w * Real.exp (-x*w^2/2)

theorem deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_integrable
    {x : R} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x)

theorem integral_deBruijnNewmanPolymathBoydGaussianSaddleIntegrand (x : R) :
    integral (deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x) =
      integral (deBruijnNewmanPolymathBoydLogSaddleIntegrand x)

theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydGaussianSaddleIntegral
    {x : R} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : C) =
      ((Real.sqrt (x/(2*Real.pi)) *
        integral (deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x) : R) : C)

def deBruijnNewmanPolymathBoydComplexSaddlePoint (n : Z) : C :=
  (n : C) * (2 * (Real.pi : C) * Complex.I)

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_critical
    {n : Z} (hn : n != 0) :
    AnalyticAt C deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) /\
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) = 0 /\
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ^ 2 =
      -2 * deBruijnNewmanPolymathBoydComplexSaddlePoint n
```

Exact names may be split when that produces clearer statement witnesses. The mathematical content,
global quantifiers, inverse derivative, integral identity, and nonzero-integer saddle statement are
fixed.

## Literature and source alignment

- W. G. C. Boyd, *Gamma function asymptotics by an extension of the method of steepest descents*,
  Proc. R. Soc. Lond. A 447 (1994), 609--630, DOI `10.1098/rspa.1994.0158`, applies the
  Berry--Howls saddle framework to Euler's Gamma integral. Its logarithmic variable has phase
  `exp(u)-u-1` and saddle points at `2*pi*i*n`.
- G. Nemes, arXiv `1310.0166`, reconstructs Boyd's Gamma resurgence representation and starts from
  the exact scaled integral obtained by `t=exp(u)`. The paper confirms that equation `(15)` is a
  subsequent resurgence identity, not a premise of the real-axis Gaussian normalization.
- Loop 14 already compiles the exact full-real phase integral. Loop 15 compiles the normalized
  principal square-root coordinate and only its origin-local complex inverse. Loop 16 is the
  source-faithful real-axis global continuation and identifies where the first nonreal critical
  points enter.

## Audited mathlib APIs

- `Real.add_one_lt_exp` and `Real.quadratic_le_exp_of_nonneg` give phase positivity and the
  positive-ray growth needed for surjectivity.
- `HasDerivAt.real_of_complex` transports the Loop 15 derivative through the removable point.
- `strictMono_of_deriv_pos`, `Continuous.surjective`, and
  `StrictMono.orderIsoOfSurjective` package the global real coordinate.
- `OrderIso.toHomeomorph` supplies continuity of the inverse.
- `HasDerivAt.of_local_left_inverse` computes the inverse derivative from the already constructed
  global inverse.
- `integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn` and
  `integral_image_eq_integral_deriv_smul_of_monotoneOn` provide the exact whole-line Jacobian.
- `Complex.exp_int_mul_two_pi_mul_I`, `Complex.differentiableOn_sqrt`, and
  `Complex.mem_slitPlane_iff` cover the nonzero integer saddle points.

## Position in the RH graph

- `node_id`: `H6-Q1`
- `relation_to_RH`: this is the real steepest-descent normalization immediately upstream of the
  contour/Cauchy decomposition needed for Boyd--Nemes equation `(15)`, which feeds the effective
  `R2` bound in the Polymath Table 1 final-region certificate.
- `assumption_frontier_before`: Loop 14 gives the exact full-real phase integral; Loop 15 gives the
  normalized local complex inverse at zero. Both are public K0.
- `hard_gap_before`: no global real inverse/Jacobian is compiled; the first nonreal critical images,
  global complex branch continuation, adjacent-saddle contour decomposition, equation `(15)`,
  effective `R2`, and the unconditional Table 1 certificates remain open.

## Success and falsification

- `success_criterion`: the real/complex bridge, positive factor, everywhere-positive derivative,
  strict monotonicity, both infinite-end limits, global order isomorphism, inverse derivative,
  transformed integrability, exact Gaussian-Jacobian integral, scaled-Gamma endpoint, and all
  nonzero-integer complex critical-saddle statements compile. Exact Targets/TargetChecks,
  standard-only axiom prints, forbidden scans, full build, and public implementation/evidence CI
  must pass.
- `falsification_criterion`: the real coordinate differs from the principal complex restriction,
  its derivative is not positive somewhere, either end limit fails, the whole-line Jacobian needs
  an unproved integrability premise, or the nonzero integer saddle factor lies on the square-root
  slit and invalidates the claimed analyticity.
- `proper_prefix_rule`: retain a global real order isomorphism only if compiled, but classify the
  campaign as partial unless the inverse derivative and Gaussian integral identity also compile.
  Complex saddle localization may be recorded as a separate obstruction result if it fails after
  the complete real Jacobian spine.
- `anti_substitution_rule`: do not assume a global complex inverse, global complex injectivity,
  Boyd--Nemes equation `(15)`, a resurgence contour identity, an effective `R2` estimate, or an
  unspecified analytic continuation.

## Next decision

- `next_if_success`: preregister the Cauchy coefficient representation for the real inverse
  Jacobian and determine how its first critical images generate the two adjacent-saddle terms.
- `next_if_blocked`: record the exact failed layer: real/complex branch alignment, zero derivative
  transport, end growth, inverse derivative, Jacobian integrability, or saddle slit-plane
  membership. Attack only that exposed obligation with a materially new mechanism.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.

No Loop 16 proof source may be edited before this preregistration passes public Lean Action CI.

## Implementation outcome

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydRealSaddleDiffeomorphism.lean`
- `result`: every fixed real-axis, inverse-derivative, Gaussian-Jacobian, scaled-Gamma, and
  nonzero-integer complex critical-saddle declaration in the exact target compiles.
- `closed_subobligations`: the principal coordinate's complete real restriction is an
  orientation-preserving order isomorphism; its inverse has the certified reciprocal derivative;
  the Loop 14 integral has the exact Gaussian-Jacobian form; and the critical images of all source
  saddles `2*pi*i*n`, `n != 0`, are located.
- `remaining_hard_gap`: no global complex inverse branch, Cauchy coefficient representation,
  adjacent-saddle resurgence decomposition, Boyd--Nemes equation `(15)`, or effective `R2` estimate
  has been proved.
- `rh_frontier_delta`: 0
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `obstruction_map_delta`: 1
- `local_audit`: exact source and aggregate imports, two Targets, TargetChecks, sixteen selected
  standard-only axiom prints, empty forbidden scans, `git diff --check`, and the 8,721-job full
  build pass. The selected declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `public_preregistration`: commit `e21951ecbbf91bfaa7f654027de4e671a45ab525` passed public Lean
  Action CI run `29663980567`, build job `88131219843`, in `1m33s` before proof-source editing.
- `public_implementation`: commit `59d58270504f26555d6f8771e8a101bda4a115c5` passed public Lean
  Action CI run `29664724249`, build job `88133120232`, in `2m24s`.
- `next_exact_gate`: derive a Cauchy coefficient representation for the real inverse Jacobian near
  zero, with its radius controlled by the `n=+/-1` critical images, and determine how those images
  generate the two adjacent-saddle terms without assuming equation `(15)`.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
