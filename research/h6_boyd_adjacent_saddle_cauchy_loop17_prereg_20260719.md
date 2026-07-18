# H6 Boyd Adjacent-Saddle Cauchy Branch Loop 17 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-ADJACENT-SADDLE-01`

Mode: `PROOF-ATTEMPT`

Status: `PARTIAL / OBSTRUCTION_RECORDED`

## Exact target

Let `phase(u)=exp(u)-u-1`, let `w(u)` be the normalized principal coordinate compiled in Loop 15,
and let

```text
s_n = 2*pi*i*n,
c_n = w(s_n).
```

Loop 16 proves that `w'(s_n)=0` and `c_n^2=-4*pi*i*n` for every nonzero integer `n`. The two
adjacent saddles are `s_1` and `s_-1`.

The full Loop 17 target is to construct an analytic continuation `U` of the origin-local inverse
on the open disk

```text
D = { z : C | norm z < 2*sqrt(pi) },
```

prove that it agrees with the compiled local inverse near zero, satisfies

```text
phase(U(z)) = z^2/2  for z in D,
```

and prove the two radial landing statements

```text
U(t*c_1)  -> s_1  as real t -> 1 from below,
U(t*c_-1) -> s_-1 as real t -> 1 from below.
```

For every `0<r<2*sqrt(pi)`, prove that the inverse Jacobian `deriv U` is represented on
`ball 0 r` by its Cauchy power series. Finally prove that no analytic inverse branch which agrees
with the origin branch and lands at either adjacent saddle can extend to any centered disk of
radius strictly larger than `2*sqrt(pi)`. Thus the two adjacent critical images give the exact
centered continuation barrier for this branch.

This target determines the analytic coefficient domain upstream of Boyd's adjacent-saddle
decomposition. It does not assume or claim Boyd--Nemes equation `(15)`.

## Proposed Lean declarations

Exact implementation names may be split, but the quantifiers and mathematical content are fixed.

```lean
def deBruijnNewmanPolymathBoydComplexSaddleImage (n : Z) : C :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydComplexSaddlePoint n)

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_sq
    {n : Z} (hn : n != 0) :
    norm (deBruijnNewmanPolymathBoydComplexSaddleImage n) ^ 2 =
      4 * Real.pi * abs (n : R)

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one :
    norm (deBruijnNewmanPolymathBoydComplexSaddleImage 1) =
      2 * Real.sqrt Real.pi

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_neg_one :
    norm (deBruijnNewmanPolymathBoydComplexSaddleImage (-1)) =
      2 * Real.sqrt Real.pi

theorem not_differentiableAt_leftInverse_at_boydComplexSaddle
    {n : Z} (hn : n != 0) (U : C -> C)
    (hleft : forall eventually u near
      deBruijnNewmanPolymathBoydComplexSaddlePoint n,
      U (deBruijnNewmanPolymathBoydComplexSaddleCoordinate u) = u) :
    not DifferentiableAt C U
      (deBruijnNewmanPolymathBoydComplexSaddleImage n)

theorem boydOriginInverseBranch_radius_le_adjacent
    {U : C -> C} {R : R} {n : Z}
    (hn : n = 1 or n = -1)
    (hR : 0 < R)
    (hU : AnalyticOnNhd C U (Metric.ball 0 R))
    (hlocal : U = eventually near 0
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse)
    (hlands : U (deBruijnNewmanPolymathBoydComplexSaddleImage n) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint n) :
    R <= 2 * Real.sqrt Real.pi

noncomputable def deBruijnNewmanPolymathBoydOriginInverseBranch : C -> C :=
  -- actual continuation of the Loop 15 inverse to the first critical disk

theorem deBruijnNewmanPolymathBoydOriginInverseBranch_analyticOnNhd :
    AnalyticOnNhd C deBruijnNewmanPolymathBoydOriginInverseBranch
      (Metric.ball 0 (2 * Real.sqrt Real.pi))

theorem deBruijnNewmanPolymathBoydOriginInverseBranch_eventuallyEq_localInverse :
    deBruijnNewmanPolymathBoydOriginInverseBranch = eventually near 0
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse

theorem deBruijnNewmanPolymathBoydOriginInverseBranch_phase
    {z : C} (hz : z in Metric.ball 0 (2 * Real.sqrt Real.pi)) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
      (deBruijnNewmanPolymathBoydOriginInverseBranch z) = z ^ 2 / 2

theorem tendsto_deBruijnNewmanPolymathBoydOriginInverseBranch_adjacent
    {n : Z} (hn : n = 1 or n = -1) :
    Tendsto
      (fun t : R => deBruijnNewmanPolymathBoydOriginInverseBranch
        ((t : C) * deBruijnNewmanPolymathBoydComplexSaddleImage n))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (deBruijnNewmanPolymathBoydComplexSaddlePoint n))

theorem deBruijnNewmanPolymathBoydOriginInverseJacobian_hasCauchyPowerSeriesOnBall
    {r : NNReal} (hr0 : 0 < r)
    (hr : (r : R) < 2 * Real.sqrt Real.pi) :
    HasFPowerSeriesOnBall
      (deriv deBruijnNewmanPolymathBoydOriginInverseBranch)
      (cauchyPowerSeries
        (deriv deBruijnNewmanPolymathBoydOriginInverseBranch) 0 r)
      0 r
```

The displayed pseudocode uses words such as `eventually` only to fix the intended filter-level
statement. The production declarations will use the corresponding Lean `EventuallyEq` syntax.

## Success and falsification

- `success_criterion`: construct the actual analytic branch on the full open disk of radius
  `2*sqrt(pi)`, prove agreement with the Loop 15 inverse, the phase equation, both one-sided radial
  landing statements, Cauchy power-series representations for the inverse Jacobian on every
  smaller disk, and the no-larger-disk obstruction. Exact Targets/TargetChecks, standard-only
  axiom prints, forbidden scans, full build, and public implementation/evidence CI must pass.
- `falsification_criterion`: the principal Loop 15 branch reaches a singularity of smaller norm;
  either radial path exits the principal-coordinate continuation domain before its adjacent
  saddle; the branch lands at a different preimage; or a compiled analytic continuation exists
  through an adjacent critical image while preserving the inverse identity.
- `proper_prefix_rule`: if the actual branch construction is blocked, retain results only if Lean
  compiles all of the following: exact adjacent-image norms, impossibility of a differentiable
  local left inverse at every nonzero saddle, a generic analytic-origin-branch phase identity by
  the identity theorem, and the radius upper bound conditional only on explicit branch landing.
  Record the first missing global continuation or landing statement as an `OBS` node. Isolated
  Taylor coefficients, abstract Cauchy APIs, or a theorem assuming equation `(15)` do not qualify.
- `anti_substitution_rule`: do not postulate the branch, its landing, global injectivity, monodromy,
  a contour deformation, Boyd--Nemes equation `(15)`, an effective `R_2` estimate, or an unnamed
  analytic-continuation hypothesis.

## Prior state and source alignment

- `node_id`: `H6-Q1`.
- `relation_to_RH`: bridge to the Boyd `R_2` representation used by the Polymath Proposition 6.1
  final-region certificate.
- `assumption_frontier_before`: Loop 15 gives the origin-local analytic inverse. Loop 16 gives the
  global real inverse/Jacobian and compiler-locates every nonzero complex critical saddle and its
  image square. All are public K0.
- `hard_gap_before`: no complex inverse branch on a specified disk, no exact Cauchy coefficient
  domain, no adjacent-saddle landing theorem, no resurgence contour, and no equation `(15)`.
- `known_obstacles`: the principal square-root coordinate is not globally analytic on all of `C`;
  a disk-wide inverse needs continuation independent of that total representative. Mathlib has
  local analytic inversion, Cauchy power series, and identity theorems, but no packaged monodromy
  theorem or Lambert-W branch suited to this phase.
- `nearest_primary_source`: W. G. C. Boyd, *Gamma function asymptotics by an extension of the
  method of steepest descents*, Proc. R. Soc. Lond. A 447 (1994), 609--630, DOI
  `10.1098/rspa.1994.0158`, especially equations `(2.14)` and `(4.2)` as cited by Nemes; and
  G. Nemes, arXiv `1310.0166`, equation `(15)`.
- `nearest_project_attempt`: Loop 16's real diffeomorphism and nonzero-integer critical-image
  theorem.
- `new_attack_angle`: replace an unspecified “global Cauchy decomposition” by a fixed centered
  continuation disk, explicit radial landing tests, and a compiler-checkable obstruction theorem
  identifying exactly which landing fact is needed to make the adjacent images control the
  inverse series.

## Audited APIs

- `AnalyticAt.analyticAt_localInverse` supplies the existing origin branch.
- `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` can extend the local phase identity across
  a connected disk once a disk-wide analytic branch is constructed.
- `differentiableOnNhd_cball.cauchyPowerSeries` and related theorems in
  `Mathlib.Analysis.Complex.CauchyIntegral` produce the exact Cauchy series on smaller disks.
- Chain-rule derivatives turn `w'(s_n)=0` into the no-differentiable-left-inverse obstruction.
- `norm_pow`, the Loop 16 square identity, and positivity of `pi` determine the exact adjacent
  image norm `2*sqrt(pi)`.

## Next decision

- `next_if_success`: use the two boundary branch germs and their Cauchy discontinuities to derive
  the adjacent-saddle Stieltjes contributions in Boyd--Nemes equation `(15)` at `N=2`.
- `next_if_blocked`: record the exact missing continuation layer, expected to be construction of
  the disk-wide branch or proof that its radial limits are `s_1` and `s_-1`; route selection then
  chooses between proving that layer by path lifting/monodromy or pivoting to a direct Stieltjes
  representation of `GammaStar`.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.

No Loop 17 Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 17 outcome

- `result`: `PARTIAL / OBSTRUCTION_RECORDED`.
- `proper_prefix`: passed exactly as preregistered, with additional classification of every phase
  critical point and exclusion of all nonzero critical points over the open phase disk of radius
  `2*pi`.
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydAdjacentSaddleCauchy.lean`.
- `compiled_declarations`:
  `norm_deBruijnNewmanPolymathBoydComplexSaddleImage_sq`,
  `norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one`,
  `norm_deBruijnNewmanPolymathBoydComplexSaddleImage_neg_one`,
  `deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero`,
  `deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff`,
  `two_pi_le_norm_deBruijnNewmanPolymathBoydComplexSaddlePhase_of_critical`,
  `deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi`,
  `not_differentiableAt_leftInverse_at_boydComplexSaddle`,
  `deBruijnNewmanPolymathBoydOriginInverseBranch_phaseOn_ball`,
  `deBruijnNewmanPolymathBoydOriginInverseJacobian_hasCauchyPowerSeriesOnBall`, and
  `deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent`.
- `assumption_frontier_after`: K0 now includes the exact norm formula for all integer critical
  images, the complete phase-critical-point classification, absence of hidden nonzero critical
  points above values of norm below `2*pi`, the generic disk phase identity, Cauchy expansions of
  any analytic branch Jacobian on smaller disks, and the exact adjacent radius bound conditional
  only on explicit landing. No branch, covering map, or landing premise was introduced as an
  axiom or definition.
- `full_target_missing`: no actual disk-wide `U` and no radial landing theorem were constructed.
  The radius theorem therefore remains conditional on the explicit endpoint equality.
- `obstruction`: `OBS-H6-BOYD-COVERING-CERTIFICATE-01`. Critical-value exclusion alone does not
  establish a global inverse for the transcendental phase. The missing theorem must certify the
  origin saddle component as a phase-specific covering/path-lifting domain, rule out asymptotic
  singularities over the target disk, and identify its two adjacent boundary contours and radial
  limits at `2*pi*i` and `-2*pi*i`.
- `source_refinement`: Boyd's open 1995 primary exposition states its steepest-descent Conditions
  2.1 in terms of a unique descent path and a domain bounded by adjacent contours; its Gamma
  specialization identifies only the `+1` and `-1` saddles as adjacent. This is precisely the
  geometric certificate absent from the current Lean graph. Nemes equation `(15)` remains a
  downstream consequence candidate, not a premise.
- `source_links`: Boyd 1995 primary PDF,
  `https://intlpress.com/site/pub/files/_fulltext/journals/maa/1995/0002/0004/MAA-1995-0002-0004-a007.pdf`;
  Nemes source text `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`.
- `mechanical_audit`: the production module, `Targets.lean`, and exact `TargetChecks.lean`
  witnesses compile. Seven selected `#print axioms` entries contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `classification`: obstruction plus route infrastructure; no RH progress claim.
- `deltas`: `rh_frontier_delta=0`, `hard_gap_delta=0`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`.
- `next_route_decision`: do not continue by merely enumerating more critical points. Route
  selection should compare a direct proof of Boyd Conditions 2.1/path lifting against a direct
  Stieltjes representation of `GammaStar`; any return to this branch must preregister the exact
  geometric certificate it removes.
- `public_preregistration`: commit `43ffadd881b96aca92ab3f4684612833f9aa15cc` passed public Lean
  Action CI run `29665357300`, build job `88134769245`, in `1m57s` before proof-source editing.
- `compaction_state`: this loop inherited a compaction summary, re-read canonical governance and
  all required frontier files, then inherited a subsequent summary and repeated the canonical
  audit before closure.
- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no V4.1 numerical quota; serving token budget not exposed.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
