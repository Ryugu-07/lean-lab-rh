# H1 Bettin--Gonek Moment-to-Power Bridge Result

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Node: `H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Status: `LOCAL_FULL_MOMENT_TO_POWER_SUCCESS / IMPLEMENTATION_PUBLIC_CI_REQUIRED`

## Compiled endpoint

The new 1,174-line module
`LeanLab/Riemann/BettinGonekMomentToPowerBridge.lean` proves:

```lean
theorem bettinGonekMomentToPowerBridge_of_pos
    {theta : ℝ} (htheta : 0 < theta) :
    BettinGonekMomentToPowerBridge theta

theorem farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek
    (hmoment : FarmerThetaInfinityConjecture) :
    RiemannHypothesis
```

The second theorem supplies the first theorem directly to the existing reflection and exponent
consumer. No abstract bridge premise remains in the conditional implication.

## Proof chain

1. `criticalStripRealAxisZeroFree` proves `riemannZeta (1/2) != 0`.
2. Continuity and nonvanishing give strictly positive zeta squared mass on `[0,1]`.
3. An explicit positive lower bound controls the selected residue scale uniformly on `[0,1]`.
4. Translation invariance of the real integral makes the inverse-Mellin bound independent of
   the height translation.
5. The literal mollifier equals one on the real-cutoff interval `(1,2]`; subsequent unit
   intervals reduce to neighboring integer mollifiers through the compiled interpolation.
6. Equations `(2.4)` and `(2.5)`, squaring, and finite Cauchy yield an integer mollifier
   norm-square sum.
7. Multiplication by the critical-line zeta squared norm and integration over `[0,1]` identify
   the exact integer Farmer moments.
8. Interval monotonicity embeds those moments into `[0,T]`, where
   `FarmerLongMollifierBound theta` applies.
9. With `X=floor(T^theta)`, floor comparison and logarithmic absorption give the exact
   `BettinGonekPowerObstruction theta rho.re`.
10. The existing all-positive-theta exponent consumer and zero reflection imply Mathlib's
    `RiemannHypothesis`.

## Omission result

The preregistered fixed-low-height attack succeeds. Bettin--Gonek Theorem 1 does not require a
full asymptotic formula for the critical-line zeta second moment in this formal reconstruction.
A fixed compact interval with positive zeta squared mass supplies the needed lower factor. This
is a proof simplification and historical omission finding, not a new unconditional
number-theory theorem.

## Source and definition alignment

- The mollifier is the project's literal real-cutoff `farmerMollifier`.
- The moment premise is the registered integer-cutoff `FarmerLongMollifierBound`.
- The residue and convolution inputs are the compiled source equations `(2.1)`--`(2.5)`.
- The final exponent is exactly `1 + epsilon + theta`; no cutoff, logarithm, or square factor
  changes the source obstruction.
- No target-equivalent premise, abstract explicit-formula premise, or numerical zeta witness is
  introduced.

## Mechanical audit

- direct production compile with `-DwarningAsError=true`: pass;
- `LeanLab.Riemann.Targets`: pass;
- `LeanLab.Riemann.TargetChecks`: pass;
- `LeanLab.Riemann.AxiomsAudit`: pass;
- selected transitive axioms: `propext`, `Classical.choice`, `Quot.sound`;
- `sorry`, `admit`, `native_decide`: absent;
- custom `axiom`, `opaque`, `unsafe`: absent;
- resource-limit relaxations: absent;
- full build: `8763/8763`;
- preregistration commit `3df6ed836c550671a0e552a09bbba314fcab5c1c`: public Lean Action
  run `30188267224`, build job `89756704490`, passed in `1m31s`.

## Claim boundary

`FarmerThetaInfinityConjecture` remains an open arbitrary-length mollified moment conjecture.
The result proves the known conditional Bettin--Gonek implication from that conjecture to RH;
it is not an unconditional proof of RH.

- `source_analytic_bridge_delta=1`
- `known_theorem_formalization_delta=1`
- `historical_route_coverage_delta=1`
- `hard_gap_delta=0` for RH
- `rh_frontier_delta=0`

The next gate is a frozen implementation commit and public Lean Action CI, followed by
docs-only immutable-evidence and final-ledger commits.
