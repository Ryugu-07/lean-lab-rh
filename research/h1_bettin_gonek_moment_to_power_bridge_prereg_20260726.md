# H1 Bettin--Gonek Moment-to-Power Bridge Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Selected node: `H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Mode: `LITERATURE / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `31362f4044e99651d7567f91dc4fd8a701974f38`.
- `parent_public_ci`: Lean Action run `30187802034`, build job `89755512303`, passed in
  `1m29s`.
- `route_selection`:
  `research/route_selection_post_h7_dictionary_explicit_formula_20260726.md`.
- `global_goal`: active. RH is the target.
- `production_gate`: docs-only preregistration must pass public Lean Action CI before production
  proof edits.

## Locked primary source

Sandro Bettin and Steven M. Gonek, *The theta=infinity conjecture implies the Riemann
hypothesis*, Mathematika 63 (2017), 29--33, arXiv:1604.02740, Theorem 1 and equations
`(2.1)`--`(2.5)`.

For `theta>0`, the source proves that a uniform bound

```text
I_N(0,T) <<_epsilon T^(1+epsilon)
```

for every integer `2<=N<=T^theta` excludes zeta zeros in
`Re(s)>1/2+1/(2*theta)`. Taking every positive `theta` gives RH.

## Compiled project state

The project already proves, for the literal source objects:

1. integer-to-real cutoff interpolation for the Farmer mollifier and its moment;
2. equation `(2.1)`, including the actual Mobius sum and Mellin transform;
3. standalone decay and inverse Mellin support/boundedness for `G_t`;
4. the actual Mellin convolution and upper estimate `(2.4)`;
5. the exact contour shift and selected-zero residue `(2.5)`;
6. the exponent consumer converting every power obstruction into the source zero-free
   half-plane and converting all positive `theta` obstructions into RH.

The definition `BettinGonekMomentToPowerBridge` currently names the missing theorem and is not an
available premise.

## Fixed Lean endpoints

Create `LeanLab/Riemann/BettinGonekMomentToPowerBridge.lean` only after public preregistration CI.

The mandatory primary theorem is equivalent to:

```lean
theorem bettinGonekMomentToPowerBridge_of_pos
    {theta : Real} (htheta : 0 < theta) :
    BettinGonekMomentToPowerBridge theta
```

The mandatory source corollary is equivalent to:

```lean
theorem farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek
    (hmoment : FarmerThetaInfinityConjecture) :
    RiemannHypothesis
```

Equivalent reassociation is allowed, but the final theorem must consume the actual
`FarmerLongMollifierBound`, actual `IsNontrivialZero`, and actual compiled `(2.4)` and `(2.5)`
objects. An abstract inequality carrying the desired power bound as a premise is not acceptable.

## Registered attack

### A. Fixed-low-height positive mass

For each selected zero `rho`, prove uniform constants on `t in [0,1]`:

- a positive lower bound for `bettinGonekResidueScale rho t`;
- independence, or a uniform upper bound, for `bettinGonekInverseMellinBound rho t`;
- positivity of
  `integral_0^1 normSq (riemannZeta (1/2+i*t)) dt`.

Use the residue and convolution bounds to control the source real-cutoff integral from below.
Partition the real cutoff interval `[1,X]` into unit intervals. On intervals starting at
`n>=2`, use the already compiled exact interpolation between integer cutoffs `n` and `n+1`;
handle `[1,2]` from the literal finite sum. Apply finite Cauchy--Schwarz to obtain an integer
sum of squared mollifiers.

Multiply by the zeta squared norm and integrate only over `[0,1]`. Monotonicity embeds every
integer moment into `[0,T]`, where `FarmerLongMollifierBound` applies. Choose
`X=floor(T^theta)`, prove `X` is comparable to `T^theta`, absorb `log(X)^2` into an arbitrarily
small positive power of `T`, and derive the registered eventual power obstruction.

### B. Source second-moment fallback

If the fixed compact interval cannot be connected to the actual integer moment API without a
target-equivalent assumption, reconstruct the source's standard critical-line second-moment
lower bound and use its displayed weighted estimate. Record the exact first unavailable theorem
before stopping.

## Decision criteria

- `FULL_MOMENT_TO_POWER_SUCCESS`: both mandatory endpoints compile, together with a proven Target,
  exact TargetChecks, selected transitive axiom audit, empty forbidden scans, full build, and the
  public evidence sequence.
- `FIXED_INTERVAL_ASSEMBLY_BLOCKED`: the local positive mass compiles, but one named
  real-cutoff partition, integer-moment domination, or power-asymptotic theorem remains
  unavailable. Record its complete Lean signature.
- `SOURCE_SECOND_MOMENT_BLOCKED`: fallback B reaches one exact source theorem not derivable from
  current zeta APIs. Record it without introducing it as a premise.
- `NORMALIZATION_MISMATCH`: a factor of `x`, `log x`, the selected residue power, or the real
  cutoff interpolation changes the source exponent. Compile the mismatch where possible and
  stop the source claim.
- `PREMISE_CREEP`: reject any proof that assumes `BettinGonekMomentToPowerBridge`, the desired
  power obstruction, or an equivalent aggregate inequality.
- `local_stop`: full public closure or one exact analytic blocker after both registered attacks.
  Local stop returns to `ROUTE_SELECTION`; the global RH Goal remains active.

## Known obstacles

- The residue lower bound must be uniform in `t` on the chosen compact interval.
- The inverse Mellin upper constant is written as a translated real integral; translation
  invariance must be proved rather than inferred informally.
- `farmerMollifier` changes finite support at integer cutoffs. The endpoint-zero taper and
  compiled interpolation must justify the unit-interval partition.
- The moment hypothesis controls integer cutoffs only. Every endpoint introduced by the
  partition must remain at most `floor(T^theta)`.
- Floor comparison, real powers, logarithmic absorption, and eventual quantifiers must preserve
  the exact exponent `1+epsilon+theta`.
- Positivity on a fixed interval must be kernel-checked from continuity and a nonzero value, not
  imported as a numerical zeta evaluation.

## Assumption and claim audit

- `assumption_frontier_before`: equations `(2.1)`--`(2.5)` compile, but the actual
  `FarmerLongMollifierBound -> BettinGonekPowerObstruction` theorem is absent.
- `assumption_frontier_after_on_success`: the bridge is unconditional; Farmer's long-mollifier
  conjecture remains the sole open premise in the source RH implication.
- `rh_strength`: `FarmerThetaInfinityConjecture` implies RH after success. The conjecture is not
  proved and remains unavailable in unconditional work.
- `expected_delta`: `source_analytic_bridge_delta=1`, `known_theorem_formalization_delta=1`,
  `hard_gap_delta=0` for RH, `rh_frontier_delta=0`.
- `originality_boundary`: fixed-low-height positive mass is a proof simplification for the
  source `[0,T]` theorem, not a priority or new-number-theory claim.

## Mechanical and publication gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct module compilation, exact TargetChecks, selected `#print axioms`,
empty forbidden scans, `git diff --check`, full `lake build`, frozen implementation CI,
immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Local outcome

Status: `FULL_MOMENT_TO_POWER_SUCCESS_LOCAL / IMPLEMENTATION_PUBLIC_CI_REQUIRED`.

Attack A succeeded without changing the preregistered endpoint. The 1,174-line production
module `LeanLab/Riemann/BettinGonekMomentToPowerBridge.lean` proves:

```text
0 < theta -> BettinGonekMomentToPowerBridge theta
FarmerThetaInfinityConjecture -> RiemannHypothesis
```

The exact exported theorem names are `bettinGonekMomentToPowerBridge_of_pos` and
`farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek`. The proof establishes the
fixed positive zeta mass on `[0,1]`, the compact residue lower bound, translation invariance of
the inverse-Mellin majorant, the unit-interval real-cutoff reduction to integer mollifiers,
finite Cauchy, moment monotonicity, and the floor/rpow/logarithm asymptotics. The stronger source
second-moment fallback was not needed.

Direct warning-as-error compilation, exact Targets and TargetChecks, selected axiom prints,
three forbidden scans, `git diff --check`, and the full `8763/8763` build pass locally. Selected
transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

This is a formalization of the known conditional Bettin--Gonek bridge. It does not prove
Farmer's arbitrary-length moment conjecture and does not prove RH unconditionally.
