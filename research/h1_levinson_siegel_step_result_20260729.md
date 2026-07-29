# H1 Levinson--Siegel Step Geometry Result

Date: 2026-07-29

Campaign: `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01`

Node: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`

Classification: `FULL_SUCCESS / STRUCTURAL_OMISSION_GEOMETRY_FORMALIZED`

## Compiled result

The 319-line module `LeanLab/Riemann/LevinsonSiegelStep.lean` defines

```text
L_R(y) = 1 / (1 + exp(R*(2*y-1)))
Q_R(y) = (L_R(y)-L_R(1)) / (L_R(0)-L_R(1))
```

and the three-case Siegel step. Lean proves:

1. `L_R(1-y)=1-L_R(y)`;
2. `L_R(0)-L_R(1)=(exp R-1)/(exp R+1)`, positive for `R>0`;
3. `Q_R(0)=1`, `Q_R(1)=0`, and `Q_R(y)+Q_R(1-y)=1`;
4. the exact derivative of `L_R` and `Q_R`;
5. `Q_R(1/2)=1/2`;
6. `Q_R` converges pointwise to the Siegel step as `R` tends to positive infinity;
7. `R/2 <= |Q_R'(1/2)|` for `R>0`;
8. every differentiable decreasing transition has an interior derivative magnitude at least
   its secant magnitude;
9. an epsilon-step transition on a window of radius `delta` exceeds every derivative bound
   below `(1-2*epsilon)/(2*delta)`.

The aggregate declaration is:

```text
levinsonSiegelStep_endpoint
```

Target `H1.levinson-siegel.step-geometry` is registered as proven.

## Proof audit

- The reflection theorem uses the exact exponential reciprocal identity.
- Endpoint normalization is justified by an explicit positive denominator, not a totalized
  division convention.
- The derivative proof uses Mathlib's exponential chain rule and inverse derivative theorem.
- The pointwise limit treats `y<1/2`, `y=1/2`, and `y>1/2` separately; no uniform limit is
  asserted.
- The general steepness result is an exact application of the real mean-value theorem.
- The production forbidden and resource scans are empty.
- The new module and registration files compile with `-DwarningAsError=true`.
- Eight exact TargetChecks compile.
- Seven selected axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`.
- Full build passes `8792/8792`.

## Historical reading

The result formally separates mollifier length from auxiliary-function complexity. Within the
source endpoint and reflection class, short length does not prevent a smooth family from
approaching Siegel's step. The price is increasing transition steepness.

This supports the structural lesson of the 2025 short-mollifier paper without identifying the
explicit logistic family with its hypergeometric optimizer. The useful omission probe is now
sharper:

```text
Can source polynomial approximants and mollified mean-value estimates remain quantitatively
uniform while the admissible derivative combination approaches the step?
```

That is a different question from optimizing a fixed numerical zero proportion.

## Strict boundary

This result does not:

- prove uniform convergence to the discontinuous step;
- identify the logistic profile with the source optimizer;
- prove that the profile is a polynomial differential combination;
- give a polynomial degree or approximation-rate theorem;
- prove a mollified zeta mean-value asymptotic uniform in growing complexity;
- reconstruct Conrey's argument-principle and Littlewood counting bridge;
- improve a critical-line zero proportion;
- exclude a sparse off-line zero orbit;
- prove H1 or RH.

Accordingly:

- `historical_route_coverage_delta=1`;
- `structural_obstacle_map_delta=1`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Successor question

The next H1 work should compare two source-faithful producers:

1. quantitative polynomial approximation to the source optimizer or Siegel step with explicit
   derivative/degree growth;
2. a mollified second-moment theorem whose error terms are uniform in that growing complexity.

The actual zeta auxiliary count in Conrey 1989 equations `(32)`--`(39)` remains the downstream
consumer. The campaign must close locally after public evidence and return to fresh
cross-family ranking rather than continuing H1 by inertia.

## Public implementation evidence

Frozen implementation commit `fb5d03e268849dbac7c7d51375d245eba944a92b` passed public Lean
Action run `30410129919`, build job `90444149672`, in `2m6s`.

The frozen proof and registration set is:

- `LeanLab/Riemann/LevinsonSiegelStep.lean`;
- `LeanLab/Riemann/Targets.lean`;
- `LeanLab/Riemann/TargetChecks.lean`;
- `LeanLab/Riemann/AxiomsAudit.lean`;
- `LeanLab.lean`.

The immutable-evidence and final-ledger commits must leave this set unchanged from the frozen
implementation.

Immutable-evidence commit `a7d1e38bba631fb7deb9b9a9adbd19a9198dd9fc` passed public Lean
Action run `30410358415`, build job `90444833678`, in `2m1s`. The frozen-set diff from
`fb5d03e268849dbac7c7d51375d245eba944a92b` is empty.

## Final ledger

Close exactly:

```text
H1.levinson-siegel.step-geometry
```

as `FULL_SUCCESS / STRUCTURAL_OMISSION_GEOMETRY_FORMALIZED`.

Keep open:

1. identification and independent formalization of the source hypergeometric optimizer;
2. source-faithful polynomial approximation with explicit derivative and degree growth;
3. mollified zeta mean-value estimates uniform in that growing complexity;
4. Conrey's actual auxiliary-function argument variation and right-zero count;
5. Littlewood-lemma conversion to critical-line zero proportions;
6. exclusion of finite or density-zero off-line zero orbits;
7. H1 and RH.

The key durable conclusion is that short mollifier length is not a geometric obstruction
inside the source endpoint/reflection class. The newly isolated obstruction is quantitative
uniformity as the derivative combination becomes step-like.

After the final-ledger public CI, publish one closure receipt and return the active RH Goal to
fresh cross-family historical omission selection.
