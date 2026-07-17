# H6 Heat-Li Time Monotonicity Preregistration

Date: 2026-07-17

Campaign: `PROOF-ATTEMPT-20260717-H6-HEAT-LI-TIME-MONOTONICITY-01`

Mode: `PROOF-ATTEMPT`, with mandatory `FALSIFICATION` gate

Status: `PREREGISTERED_PUBLIC_CI_SUCCESS`

## Exact mathematical target

For `n : Nat`, define

```text
lambda_n(t) = Re(deBruijnNewmanHeatLiCoefficient t n).
```

Prove the indivisible conjunction

```text
(for every n, lambda_n(t) tends to 0 as t tends to -infinity)
and
(for every n, lambda_n is monotone nondecreasing on t<=0),
```

then derive `Mathlib.RiemannHypothesis` from the compiled all-index heat-Li criterion.

## Proposed Lean endpoint

Module: `LeanLab/Riemann/DeBruijnNewmanHeatLiMonotonicity.lean`

```lean
def DeBruijnNewmanHeatLiAtBotZero : Prop :=
  forall n : Nat,
    Tendsto (fun t : Real => (deBruijnNewmanHeatLiCoefficient t n).re)
      atBot (nhds 0)

def DeBruijnNewmanHeatLiMonotoneToZero : Prop :=
  forall n : Nat,
    MonotoneOn
      (fun t : Real => (deBruijnNewmanHeatLiCoefficient t n).re)
      (Set.Iic 0)

theorem deBruijnNewmanHeatLi_atBot_zero_and_monotone :
    DeBruijnNewmanHeatLiAtBotZero and
      DeBruijnNewmanHeatLiMonotoneToZero

theorem riemannHypothesis_of_heatLi_atBot_zero_and_monotone :
    Mathlib.RiemannHypothesis
```

Equivalent filter spelling and namespaces are allowed. The all-index quantifier, `atBot` limit,
full half-line `Iic 0`, and unconditional RH endpoint may not be weakened.

## Strength and DAG position

- DAG position: a direct unconditional edge into H6-E/G8 through the compiled all-index heat-Li
  criterion
- relation to RH: the conjunction implies RH; the converse is not known, so it may be strictly
  stronger
- `hard_gap_before`: no unconditional all-index sign mechanism at time zero
- success `hard_gap_delta`: closes H6-E/G8 and RH
- failure `hard_gap_delta`: 0, with a new exact obstruction if Lean certifies a counterexample
- no clause may be used as a premise before it is proved

## Mandatory falsification gate

Before proof-source implementation:

1. Derive the formal power-series identity
   `log F_t(1/(1-z)) = log F_t(1) + sum_(m>=1) lambda_(m-1)(t)*z^m/m`
   numerically from independently evaluated theta moments.
2. Search indices `0<=n<=31` and times `-16<=t<=0`, including a dense grid near zero and
   logarithmically separated negative times.
3. Evaluate the time derivative by the exact quotient-series identity
   `partial_t log F = (partial_t F)/F`, not by subtracting two nearly equal Li values.
4. Repeat every negative or near-zero sign at 80, 120, and 180 decimal digits, increase the theta
   and quadrature cutoffs, and round the time to a simple rational.
5. Test positive finite cosh mixtures separately. Their failure cannot refute the actual-theta
   conjecture, but it audits whether any proposed proof accidentally uses only generic positivity.
6. Check the first coefficient against the compiled covariance sign `B*C<=A*D`.

Numerical support is never a theorem. A robust negative derivative or decreasing rational-time
pair selects an exact Lean falsification target.

## Fixed proof architecture if the gate survives

1. Prove the `atBot` limit by rescaling `u=v/sqrt(-t)` and controlling the full theta kernel near
   zero plus its super-exponential tail.
2. Differentiate every Li coefficient in heat time using
   `partial_t F=(1/4)*partial_s^2 F` and the all-index logarithmic generating series.
3. Seek a single all-index coefficient representation whose time derivative is an integral of a
   nonnegative actual-theta expression. Finite-index verification alone cannot close the target.
4. Prove all time-zero signs from the limit and monotonicity, invoke
   `deBruijnNewmanAllZerosReal_iff_forall_heatLiCoefficient_re_nonneg 0`, and finish through the
   compiled RH equivalence.

If no all-index representation emerges, do not replace the endpoint by another finite coefficient.

## Known obstacles and adversarial cases

- Generic reverse-heat Li transfer is false by the compiled quadratic countermodel.
- Generic positive cosh mixtures can have a negative third Li coefficient.
- The first coefficient covariance does not imply higher-index derivative signs.
- High-order formal power series can suffer severe cancellation and require independent precision
  checks.
- The negative-infinite-time limit requires a uniform all-index argument, not a fixed-`n`
  dominated-convergence lemma reported as campaign success.
- A proof of only monotonicity or only the limit is insufficient.

## Success and failure criteria

Success requires the exact conjunction and unconditional RH theorem to compile, followed by exact
TargetChecks, selected transitive axiom prints, forbidden scans, standalone and full builds, and
public CI.

The conjecture is falsified only when Lean proves an exact actual-theta violation of monotonicity
or the `atBot` limit. A numerical violation is target-selection evidence. If the numerical gate
survives but two materially different all-index proof mechanisms fail at a precise dependency,
close as `NO_PROGRESS` with that dependency; do not weaken to finite-index positivity.

## Stop boundary

Stop after one of:

- the full RH endpoint is publicly audited;
- an exact actual-theta counterexample is publicly audited;
- the numerical gate survives and two all-index proof mechanisms reach the same recorded analytic
  obstacle.

Every local stop returns the persistent Goal to value-ranked route selection.

## Public preregistration evidence

- Commit: `645b4570dfe25bd5bcdcda63168d64a34ba90e24`.
- Lean Action CI run: `29569013156`.
- Build job: `87848139812`, success in `1m28s`.
