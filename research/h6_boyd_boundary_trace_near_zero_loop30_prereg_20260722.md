# H6 Boyd Boundary Trace Near-Zero Loop 30 Preregistration

Date: 2026-07-22

Campaign: `PROOF-ATTEMPT-20260722-H6-BOYD-BOUNDARY-TRACE-NEAR-ZERO-01`

Mode: `PROOF-ATTEMPT`

Status: `LOCALLY_VERIFIED / MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`

## Opening

RH is the goal. Loop 30 directly attacks
`OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01`, one of the two exact children left by
Loop 29. The complete target remains the canonical Boyd boundary-trace discrepancy limit. The
fixed first attack proves that the near-zero residual vanishes by removing the actual Gamma pole
through the Gamma recurrence and the principal square-root factor in the project's Stirling main
term. If this succeeds, the complete inner trace becomes equivalent to the single shifted-tail
limit. Every retained claim is decided by Lean.

## Baseline and route selection

- `parent_commit`: `eeb6ee4d0a9f04148b36590c8bdd1ed63e4c1c2c`.
- `baseline_public_ci`: Lean Action run `29891040964`, build job `88831388930`, passed in `1m28s`
  for the Loop 29 final ledger.
- `selected_node`: `OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01`, immediately upstream
  of the canonical inner trace and hence of the third Loop 27 dispersion-limit clause.
- `value_ranking`: Loop 29 removed every fixed compact annulus and cancelled both explicit
  `1/(12*w)` terms. The remaining near term is local at the simple Gamma pole and can be attacked
  from existing K0 recurrence, residue, reciprocal-Gamma, principal-log, and square-root facts.
  The shifted-tail child and both outer-edge limits instead require unbounded complex Stirling
  control not currently in K0. Closing the near child changes the exact frontier from
  `near + tail` to `tail` alone, so it is not an isolated local-continuity exercise.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Source audit and noncircularity

- Nemes, arXiv `1310.0166`, Section 2, equation `(15)`, remains the primary source for the two
  Boyd rays. The audited local source is
  `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`, SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Mathlib proves the local human-standard Gamma facts needed here:
  `Complex.Gamma_add_one`, `Complex.tendsto_self_mul_Gamma_nhds_zero`, and the entire reciprocal
  theorem `Complex.differentiable_one_div_Gamma`.
- The project definition is fixed:
  `GammaStar(w)=Gamma(w)/(sqrt(2*pi)*exp((w-1/2)*log(w)-w))`, with principal complex logarithm.
  Loop 29 already proves the exact paired normal form and no remainder representation is imported.
- This is a formal local-removability reduction, not a literature novelty or RH-progress claim.
  Equation `(15)`, a Binet/Plemelj formula, the shifted-tail bound, and every outer-edge bound are
  inadmissible premises.

## Exact mathematical target

For every `z` with `Re z > 0`, prove the complete canonical discrepancy limit

```text
BoundaryTraceDiscrepancy(z,n) -> 0.
```

The first attack is fixed as follows. For the principal square root, define

```text
S(w) = sqrt(w) * exp(w - w*log(w)) / sqrt(2*pi).
```

Prove globally, including the totalized value at `w=0`,

```text
w * GammaStar(w) = Gamma(w+1) * S(w),

1/GammaStar(w)
  = sqrt(2*pi) * sqrt(w) * exp(w*log(w)-w) / Gamma(w+1).
```

The proof must establish rather than assume that `w*log(w) -> 0` at `w=0`. These identities then
give continuous extensions with value zero for both `w*GammaStar(w)` and `1/GammaStar(w)`.

Use those extensions in the exact Loop 29 normal form. For every fixed `delta > 0`, prove the
right-offset uniform limit

```text
ShiftedBoundaryPairIntegrand(z,epsilon,.) -> AxisPairIntegrand(z,.)
```

uniformly on `[-delta,delta]` as `epsilon -> 0+`. The one-sided filter is mandatory: the
canonical offsets are positive, while the principal logarithm and square root have a negative-real
branch cut, so a two-sided near-zero statement is neither required nor silently admitted.

Deduce:

1. the near residual tends to zero for `epsilon -> 0+`;
2. the canonical near residual tends to zero as `n -> infinity`;
3. for every fixed `A>0`, the complete discrepancy tends to zero if and only if the canonical
   shifted-tail residual beyond `A` tends to zero.

After this chain compiles, continue within the campaign by attacking the tail if a noncircular
uniform majorant can be derived. A tail estimate may not be promoted to a premise.

## Proposed Lean surface

Names may be adjusted for type correctness, but the global removable identities, right-sided
filter, canonical near limit, and final tail-only equivalence are fixed.

```lean
def deBruijnNewmanPolymathScaledGammaZeroFactor (w : Complex) : Complex :=
  Complex.sqrt w * Complex.exp (w - w * Complex.log w) /
    (Real.sqrt (2 * Real.pi) : Complex)

theorem continuousAt_complex_self_mul_log_zero :
    ContinuousAt (fun w : Complex => w * Complex.log w) 0

theorem deBruijnNewmanPolymath_self_mul_scaledGamma_eq_zeroFactor
    (w : Complex) :
    w * deBruijnNewmanPolymathScaledGamma w =
      Complex.Gamma (w + 1) * deBruijnNewmanPolymathScaledGammaZeroFactor w

theorem deBruijnNewmanPolymath_inv_scaledGamma_eq_zeroFactor
    (w : Complex) :
    (1 : Complex) / deBruijnNewmanPolymathScaledGamma w =
      (Real.sqrt (2 * Real.pi) : Complex) * Complex.sqrt w *
        Complex.exp (w * Complex.log w - w) / Complex.Gamma (w + 1)

theorem deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_zero :
    ContinuousAt
      (fun w : Complex => w * deBruijnNewmanPolymathScaledGamma w) 0

theorem deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_zero :
    ContinuousAt
      (fun w : Complex => (1 : Complex) /
        deBruijnNewmanPolymathScaledGamma w) 0

theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_near
    {z : Complex} (hz : 0 < z.re) {delta : Real} (hdelta : 0 < delta) :
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (nhdsWithin 0 (Set.Ici 0))
      (Set.Icc (-delta) delta)

theorem deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto_canonical
    {z : Complex} (hz : 0 < z.re) {delta : Real} (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun n : Nat => deBruijnNewmanPolymathBoydBoundaryNearResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta)
      Filter.atTop (nhds 0)

theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_tail
    {z : Complex} (hz : 0 < z.re) {A : Real} (hA : 0 < A) :
    Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (nhds 0) <->
      Filter.Tendsto
        (fun n : Nat => deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (nhds 0)
```

The production module must expose an aggregate certificate containing both global scaled-Gamma
removable identities, their zero continuity, the near uniform limit, the canonical near-integral
limit, and the final tail-only iff. If the shifted tail is also controlled, include the
unconditional discrepancy limit and close the Loop 28 inner trace.

## Success, falsification, and meaningful partial

- `success_criterion`: compile the canonical trace discrepancy limit for every `Re z > 0`, and
  thereby discharge the Loop 27 inner-boundary clause without a new premise.
- `minimum_hard_gap_reduction`: compile the complete aggregate chain above, ending in the exact
  tail-only iff. A theorem that only shows a Gamma factor tends to zero, or only proves pointwise
  convergence at `(epsilon,y)=(0,0)`, is insufficient.
- `falsification_criterion`: Lean proves a different principal-square-root factor, a nonzero
  totalized endpoint value, failure of the claimed right-sided uniform convergence, or a mismatch
  between the regularized pair and the registered axis kernel. Record the corrected statement and
  do not change the Loop 27-29 definitions to force agreement.
- `branch_guard`: do not replace `nhdsWithin 0 (Ici 0)` by `nhds 0` unless Lean independently
  proves the two-sided statement. A negative-offset branch mismatch is a valid falsification, not
  a reason to blur the filter.
- `local_stop`: stop when the full discrepancy limit compiles, a falsification compiles, or the
  minimum exact near-zero elimination and tail-only iff compile and the remaining tail estimate is
  stated precisely as an obstruction. Local stop never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes the Gamma recurrence and residue, reciprocal-Gamma
  entire function, project principal Stirling main term, Loop 29 exact pole cancellation, compact-
  annulus elimination, three-scale partition, and near-plus-tail iff.
- `still_open_before`: no near-zero uniform limit, canonical near-residual limit, shifted-tail
  bound, complete discrepancy limit, inner trace, outer-edge decay, equation `(15)`, effective
  `R2`, Table 1, H6-E/G8, or RH is proved.
- `anti_substitution`: do not assume continuity of inverse scaled Gamma at zero, a scaled-Gamma
  near bound, the near residual limit, the tail limit, equation `(15)`, either outer-edge limit,
  Binet/Plemelj, or complex Stirling decay. The zero continuity must be derived from the project
  definition and compiled Gamma/log/square-root facts.
- `conjecture_status`: no model-original conjecture is admitted as a premise. The local
  identities are proof targets, and the tail remains open unless independently proved by Lean.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTraceNearZero.lean`.
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
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 30
  Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: no compaction in Loop 30 route selection. Current governance, persistent
  Goal, HANDOFF, relevant Targets/TargetChecks, the H6 attempt tail, hard-gap DAG, complete Loop 29
  outcome, Gamma and square-root source APIs, external ledger, public baseline CI, and git status
  were re-read before this selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.

## Local outcome

The preregistered minimum hard-gap reduction compiled in full. The 613-line production module
proves both global totalized scaled-Gamma removable identities, their zero continuity, joint
continuity of the exact pole-free pair on closed right-offset slabs, right-sided uniform
convergence on every fixed near interval, fixed and canonical near-residual convergence, and the
exact tail-only trace iff. The aggregate theorem is
`deBruijnNewmanPolymathBoydBoundaryTraceNearZeroCertificate`.

The full success criterion was not reached. A bounded tail attack found no unconditional
closed-half-plane second-order complex Stirling estimate in mathlib or current K0. Existing
half-plane bounds retain growth hypotheses, and existing effective consequences assume the `R2`
bound that this route must prove. Thus
`OBS-H6-BOYD-R2-BOUNDARY-TRACE-NEAR-ZERO-SCALED-GAMMA-01` is closed, while
`OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01` remains the sole inner-trace child. The
discrepancy limit, inner trace, outer edges, equation `(15)`, effective `R2`, Table 1, H6-E/G8,
and RH remain open and unassumed.

Targets, eight exact TargetChecks, nine selected standard-only axiom prints, three forbidden
scans, `git diff --check`, and the full 8,735-job build pass. Every selected declaration depends
only on `propext`, `Classical.choice`, and `Quot.sound`. Public implementation and closure evidence
are pending.
