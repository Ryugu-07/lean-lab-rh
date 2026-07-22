# H6 Boyd Boundary Trace Two-Scale Loop 29 Preregistration

Date: 2026-07-22

Campaign: `PROOF-ATTEMPT-20260722-H6-BOYD-BOUNDARY-TRACE-TWO-SCALE-01`

Mode: `PROOF-ATTEMPT`

Status: `PUBLICLY_CLOSED / FINAL_LEDGER_CI_PENDING`

## Opening

RH is the goal. Loop 29 directly attacks
`OBS-H6-BOYD-R2-BOUNDARY-TRACE-UNIFORM-INTEGRABILITY-01`, the exact residual left by Loop 28 in
the inner-boundary clause of the Boyd--Nemes equation `(15)` route. The complete target is still
the canonical trace discrepancy limit. The first fixed attack is a two-scale decomposition that
must eliminate every compact annulus away from the singular boundary coordinate and leave only
the near-zero cancellation and shifted tails. Every retained claim is decided by Lean.

## Baseline and route selection

- `parent_commit`: `f2b221fe68151ce1f69635350297ba325c57b0e4`.
- `baseline_public_ci`: Lean Action run `29888544096`, build job `88824171715`, passed in `1m30s`
  for the Loop 28 final ledger.
- `selected_node`: `OBS-H6-BOYD-R2-BOUNDARY-TRACE-UNIFORM-INTEGRABILITY-01`, a child of
  `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01` and immediately upstream of
  `H6.debruijn-newman.boyd-r2-equation-15`.
- `value_ranking`: the open trace discrepancy has three analytic regimes: cancellation near
  `y=0`, compact annuli away from zero, and shifted tails as the canonical height grows. The
  near-zero regime needs a uniform removable-boundary analysis for the paired scaled-Gamma
  weights; the tails need complex second-order Stirling control not present in K0. On a fixed
  compact annulus, all singularities and Cauchy poles are uniformly separated and the existing
  half-plane holomorphy plus Loop 28 boundary continuity can close the entire middle regime.
  Retain this edge only if the result is an exact decomposition and limit equivalence, not an
  isolated continuity lemma.
- `comparison_with_outer_edges`: the two Loop 27 outer-edge limits still require unbounded
  closed-half-plane decay. The compact-annulus trace edge is the highest-value presently
  attackable child because it removes one complete regime from the already canonical inner-trace
  discrepancy without importing that unavailable decay.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Source audit and noncircularity

- Nemes, arXiv `1310.0166`, Section 2, equation `(15)`, remains the primary source for the two
  Boyd rays. The audited local source is
  `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`, SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Loop 27 fixes the exact reflection jump and Boyd projection. Loop 28 fixes the canonical offset
  discrepancy and proves pointwise convergence at every nonzero boundary coordinate.
- The two-scale partition is a formal analytic reduction, not a literature novelty claim. Its
  role is to identify exactly which portions of the source contour limit follow from local
  holomorphy and which still require new boundary estimates.
- Nemes's sector bound for `R_N`, equation `(15)`, either outer-edge limit, and any specialized
  Plemelj or Binet formula remain inadmissible premises because they would be circular or are not
  in K0.

## Exact mathematical target

For every `z` with `Re z > 0`, prove

```text
BoundaryTraceDiscrepancy(z,n) -> 0.
```

The attack is fixed through the following decomposition. Define the exact boundary-axis kernel

```text
A_z(y) = i * ((i*y) * BoundaryJump(i*y) / (i*y-z))
```

and the error kernel

```text
E_z(epsilon,y) = ShiftedBoundaryPairIntegrand(z,epsilon,y) - A_z(y).
```

For fixed `0 < delta <= A`, split its interval integral at
`-T < -A < -delta < delta < A < T` into:

```text
near(epsilon,delta)       = integral[-delta,delta] E_z(epsilon,y) dy,
middle(epsilon,delta,A)   = integral[-A,-delta] E_z(epsilon,y) dy
                            + integral[delta,A] E_z(epsilon,y) dy,
tails(epsilon,A,T)        = integral[-T,-A] E_z(epsilon,y) dy
                            + integral[A,T] E_z(epsilon,y) dy.
```

All three terms carry the same exact factor `-(2*pi*i*z)^(-1)` as the finite projection. Prove:

1. the truncated boundary-jump projection is exactly the correspondingly normalized interval
   integral of `A_z`;
2. `E_z(epsilon,.)` tends uniformly to zero on
   `[-A,-delta] union [delta,A]` as `epsilon -> 0`;
3. the fixed middle residual tends to zero, both for a real offset and along the canonical
   sequence `epsilon_n=Re(z)/(n+2)`;
4. once `T_n >= A`, the canonical discrepancy is exactly `near_n + middle_n + tails_n`;
5. consequently, the full discrepancy tends to zero if and only if `near_n + tails_n` tends to
   zero.

After this chain compiles, continue within the campaign by attempting either a uniform
near-zero cancellation estimate or a shifted-tail estimate. Neither residual may be promoted to
a premise.

## Proposed Lean surface

Names may be adjusted for type correctness, but the kernel, compact set, normalization, and final
equivalence are fixed.

```lean
def deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand
    (z : Complex) (y : Real) : Complex :=
  Complex.I *
    (((y : Complex) * Complex.I) *
      deBruijnNewmanPolymathScaledGammaBoundaryJump
        ((y : Complex) * Complex.I) /
      ((y : Complex) * Complex.I - z))

def deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand
    (z : Complex) (epsilon y : Real) : Complex :=
  deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y -
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y

def deBruijnNewmanPolymathBoydBoundaryMiddleSet
    (delta A : Real) : Set Real :=
  Set.Icc (-A) (-delta) union Set.Icc delta A

theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_middle
    {z : Complex} (hz : 0 < z.re) {delta A : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= A) :
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (nhds 0)
      (deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A)

theorem deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto
    {z : Complex} (hz : 0 < z.re) {delta A : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= A) :
    Filter.Tendsto
      (fun epsilon =>
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z epsilon delta A)
      (nhds 0) (nhds 0)

theorem deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_threeScale
    {z : Complex} (hz : 0 < z.re) {n : Nat} {delta A : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= A)
    (hAT : A <= deBruijnNewmanPolymathBoydBoundaryHeight z n) :
    deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n =
      deBruijnNewmanPolymathBoydBoundaryNearResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A +
        deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n)

theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_near_add_tail
    {z : Complex} (hz : 0 < z.re) {delta A : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= A) :
    Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (nhds 0) <->
      Filter.Tendsto
        (fun n =>
          deBruijnNewmanPolymathBoydBoundaryNearResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
            deBruijnNewmanPolymathBoydBoundaryTailResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
              (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (nhds 0)
```

The production module must expose an aggregate certificate containing the exact axis
normalization, compact-annulus uniform convergence, middle-integral convergence, exact
three-scale decomposition, and final iff. If the near-zero and tail residuals are also controlled,
include the unconditional discrepancy limit and close the Loop 28 inner trace.

## Success, falsification, and meaningful partial

- `success_criterion`: compile the canonical trace discrepancy limit for every `Re z > 0`, and
  therefore discharge the inner-boundary clause of the Loop 27 limit certificate without a new
  premise.
- `minimum_hard_gap_reduction`: compile the complete aggregate chain specified above, ending in
  the exact iff that removes every fixed compact annulus and leaves only the named near-zero plus
  tail residual. Uniform convergence without integral convergence, or integral convergence
  without the canonical discrepancy decomposition and iff, is insufficient.
- `falsification_criterion`: Lean proves a different axis orientation, normalization, partition
  sign, or that a proposed uniform statement fails because the compact set still contains a pole.
  Record the corrected theorem and do not alter the Loop 27/28 definitions to force agreement.
- `local_stop`: stop when the full discrepancy limit compiles, a falsification compiles, or the
  minimum exact two-scale reduction compiles and the first remaining near-zero or tail estimate is
  stated precisely as an obstruction. Local stop never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes exact Boyd jump integrability, the finite offset-line
  representation, pointwise convergence at every nonzero boundary coordinate, and the canonical
  discrepancy iff from Loop 28.
- `still_open_before`: no growing-interval uniform-integrability estimate, near-zero paired bound,
  shifted-tail bound, outer-edge decay, equation `(15)`, effective `R2`, Table 1, H6-E/G8, or RH
  is proved.
- `anti_substitution`: do not assume equation `(15)`, the discrepancy limit, either outer-edge
  limit, a Binet/Plemelj formula, second-order complex Stirling decay, a uniform near-zero bound,
  a shifted-tail majorant, or interchange of limits and integrals. The compact-annulus proof must
  use only compiled local continuity, compactness, and finite-interval integration.
- `conjecture_status`: no model-original conjecture is admitted as a premise. The final near and
  tail residuals remain open obligations unless independently proved by Lean.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTraceTwoScale.lean`.
- Any retained spine must be imported and registered in `LeanLab/Riemann/Targets.lean`, receive
  name resolution and exact statement witnesses in `LeanLab/Riemann/TargetChecks.lean`, and have
  selected `#print axioms` entries in `LeanLab/Riemann/AxiomsAudit.lean`.
- At loop end update `attempts/h6_polymath_table_row_certificates.md`,
  `research/hard_gap_dag.md`, this preregistration outcome, `HANDOFF.md`, and the external active
  ledger.
- No proof placeholder, custom axiom, opaque or unsafe declaration, native evaluator shortcut, or
  resource-limit relaxation is permitted.
- Run standalone diagnostics, exact witnesses, selected axiom audits, all forbidden scans,
  `git diff --check`, the full project build, and public implementation/evidence CI.
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 29
  Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: one compaction during Loop 29 route and API research. After recovery,
  current governance and V4.1, HANDOFF, relevant Targets/TargetChecks, the current H6 attempt,
  hard-gap DAG, full Loop 28 preregistration/outcome, the Loop 28 production module, the external
  ledger, and git status were re-read before this selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.

## Local outcome

- `result`: `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`.
- `minimum_hard_gap_reduction`: achieved. The aggregate theorem
  `deBruijnNewmanPolymathBoydBoundaryTraceTwoScaleCertificate` compiles and contains the exact
  axis normalization, compact-annulus uniform convergence, real and canonical middle-integral
  convergence, exact near/middle/tail partition, and final iff removing the middle regime.
- `near_zero_attack`: Lean additionally proves
  `deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized`. The two explicit
  `1/(12*w)` singular terms combine into the regular rational correction
  `epsilon/(6*(w-z)*(q-z))`; the remaining local quantities are the scaled-Gamma expressions
  `w*GammaStar(w)` and `q/GammaStar(-q)`.
- `full_success`: not achieved. No near-zero uniform estimate, shifted-tail estimate, complete
  discrepancy limit, inner trace, outer-edge limit, or Boyd--Nemes equation `(15)` is assumed or
  proved.
- `refined_obstructions`:
  `OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01` requires uniform boundary estimates
  for `w*GammaStar(w)` and `w/GammaStar(w)` in shrinking right-half-disks;
  `OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01` requires a tail majorant uniform as the offset
  tends to zero and the canonical height tends to infinity.
- `local_mechanical_audit`: the 884-line production module, exact Target, seven exact
  TargetChecks, eight selected axiom prints, standalone and integration compiles, empty forbidden
  scans, `git diff --check`, and the full 8,734-job build pass. Every selected declaration depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- `public_preregistration`: commit `436594434b0611d92978a3e7201f8f5f477ecf4c`, Lean Action run
  `29889067030`, build job `88825688680`, passed in `1m49s` before proof-source editing.
- `public_implementation`: commit `6f34d60701ac696d99b694132d231dc2ab931b62`, Lean Action run
  `29890689402`, build job `88830378785`, passed in `2m16s`.
- `public_closure`: evidence commit `ea0c2cec523adbc394af69e3a93674517c765aa4`, Lean Action run
  `29890883349`, build job `88830937245`, passed in `2m23s`.
- `compaction_state`: two compaction recoveries during Loop 29; the canonical frontier and new
  production source were re-read after each before proof or publication work resumed.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active.
