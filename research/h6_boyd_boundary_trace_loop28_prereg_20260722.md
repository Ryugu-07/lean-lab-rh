# H6 Boyd Boundary Trace Loop 28 Preregistration

Date: 2026-07-22

Campaign: `PROOF-ATTEMPT-20260722-H6-BOYD-BOUNDARY-TRACE-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED`

## Opening

RH is the goal. Loop 28 directly attacks the inner-boundary clause left by the Loop 27 finite
Cauchy projection. The complete Boyd--Nemes equation `(15)` remains the parent target. The new
mechanism separates the already integrable imaginary-axis jump from the genuinely missing
uniform approach of the positive-real offset lines. Every retained claim is decided by Lean.

## Baseline and route selection

- `parent_commit`: `ad85b72c35c8a3f956bcc88b6c2aff2971a1c42c`.
- `baseline_public_ci`: Lean Action run `29886581281`, build job `88818256523`, passed in `1m57s`
  for the Loop 27 final ledger.
- `selected_node`: `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01`, immediately upstream of
  `H6.debruijn-newman.boyd-r2-equation-15`, the effective `R2` estimate, and the Polymath
  Proposition 6.1 final-region certificate.
- `value_ranking`: retain H6-Q1. The two outer rectangle residuals require a complex second-order
  Stirling estimate not present in K0. The inner trace contains an independent part that is
  attackable now: the exact imaginary-axis jump is already represented by two integrable Boyd
  rays. Closing its truncation limit and isolating only the offset-to-boundary discrepancy removes
  tail truncation and orientation from that clause without assuming a Stirling bound.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Source audit and noncircularity

- Nemes, arXiv `1310.0166`, Section 2, equation `(15)`, gives the two positive-ray resurgence
  integrals. The audited local source is
  `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`, SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Loop 27 already compiles the exact reflection jump and proves that the complete source Boyd
  integral is `deBruijnNewmanPolymathBoydBoundaryJumpProjection`.
- Nemes's stated sector bound for `R_N` is not an admissible premise here because its proof in the
  source uses equation `(15)`. Loop 28 must not use that bound, equation `(15)`, or any equivalent
  representation to justify the boundary approach.
- The truncated projection below introduces no new mathematical criterion. It is the finite
  interval truncation of the two already source-aligned Boyd jump rays.

## Exact mathematical target

For every `z` with `Re z > 0`, prove the canonical inner-boundary limit

```text
FiniteBoundaryProjection(z, epsilon_n, T_n) -> BoundaryJumpProjection(z),
epsilon_n = Re(z)/(n+2),
T_n       = |Im(z)|+n+1.
```

This is the third clause of
`deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate`. It does not by itself prove
equation `(15)`; the two outer-edge residual limits remain separate obligations.

The attack must proceed through the following fixed decomposition.

1. Truncate both source jump rays at `T` with every sign and normalization explicit.
2. Prove those truncations tend to the complete boundary-jump projection along the canonical
   heights `T_n`.
3. Write the finite offset-line projection as one paired vertical-line integrand.
4. Prove that paired integrand tends pointwise, at every nonzero imaginary-axis point, to the
   exact jump integrand as the real offset tends to zero.
5. Define the canonical trace discrepancy as the finite offset projection minus the truncated
   jump projection, and prove that the desired inner-boundary limit is equivalent to this one
   discrepancy tending to zero.
6. Attempt to prove the discrepancy limit. If only pointwise convergence is available, identify
   the first exact uniform-integrability or two-scale estimate still missing near zero or on the
   growing tails.

## Proposed Lean surface

Names may be adjusted for type correctness, but the quantifiers, signs, canonical sequences, and
normalizations are fixed.

```lean
def deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection
    (z : Complex) (T : Real) : Complex :=
  ((integral s in 0..T,
      deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s) -
    (integral s in 0..T,
      deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s)) /
    (2 * Real.pi * Complex.I * z ^ 2)

theorem deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop
    (z : Complex) :
    Filter.Tendsto
      (deBruijnNewmanPolymathBoydBoundaryHeight z)
      Filter.atTop Filter.atTop

theorem deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_tendsto
    {z : Complex} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n => deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop
      (nhds (deBruijnNewmanPolymathBoydBoundaryJumpProjection z))

def deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand
    (z : Complex) (epsilon y : Real) : Complex :=
  Complex.I *
    (deBruijnNewmanPolymathBoydR2CauchyWeight
        (epsilon + y * Complex.I) /
          (epsilon + y * Complex.I - z) -
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        (-epsilon + y * Complex.I) /
          (-epsilon + y * Complex.I - z))

theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto
    (z : Complex) {y : Real} (hy : y != 0) :
    Filter.Tendsto
      (fun epsilon : Real =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (nhds 0)
      (nhds (Complex.I *
        (((y : Complex) * Complex.I) *
          deBruijnNewmanPolymathScaledGammaBoundaryJump
            ((y : Complex) * Complex.I) /
          ((y : Complex) * Complex.I - z))))

def deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy
    (z : Complex) (n : Nat) : Complex :=
  deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
      (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
    deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
      (deBruijnNewmanPolymathBoydBoundaryHeight z n)

theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_discrepancy
    {z : Complex} (hz : 0 < z.re) :
    Filter.Tendsto
        (fun n => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop
        (nhds (deBruijnNewmanPolymathBoydBoundaryJumpProjection z)) <->
      Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (nhds 0)
```

The production module should also expose an aggregate certificate containing the exact
truncation limit, the paired-line representation, pointwise boundary convergence, and the final
iff. If the full discrepancy limit compiles, include it and discharge the third Loop 27 clause.

## Success, falsification, and meaningful partial

- `success_criterion`: compile the canonical inner-boundary limit for every `Re z > 0` without a
  new premise.
- `minimum_hard_gap_reduction`: all of the following compile as one auditable chain: canonical
  height tends to infinity; exact truncated jump projections tend to the full source projection;
  the finite inner projection has the paired shifted-line representation; that paired integrand
  converges pointwise at every nonzero boundary point; and the complete inner-trace limit is iff
  the single named discrepancy tends to zero. A mere definition of the discrepancy or a generic
  integral truncation lemma is insufficient.
- `falsification_criterion`: Lean proves that the proposed axis orientation, coefficient, pointwise
  boundary value, or equivalence has a different sign or power of `z`. Record the corrected exact
  statement and do not alter the existing Boyd integral or Loop 27 projection to force agreement.
- `local_stop`: stop when the inner-boundary limit compiles, a falsification compiles, or the full
  minimum reduction compiles and the remaining first obstruction is an exact uniform-integrability
  statement over the canonical growing intervals. Local stop never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes both exact reflection jumps, the direct/inverse `R2`
  split, opposite-half-plane analyticity, source Boyd ray integrability, complete jump projection,
  finite right/left Cauchy rectangles, and the canonical residual identity.
- `still_open_before`: neither outer-edge residual limit nor the canonical inner-boundary limit is
  proved. No complex second-order Stirling estimate is available. Equation `(15)`, effective
  `R2`, Table 1, H6-E/G8, and RH remain open.
- `anti_substitution`: do not assume equation `(15)`, either outer residual limit, the desired
  inner trace, a Binet formula, a Plemelj theorem specialized to this function, second-order
  Stirling decay, a uniform-dominating function, or interchange of an offset limit with a growing
  interval integral.
- `conjecture_status`: no model-original conjecture is admitted as a premise. A named discrepancy
  or conditional uniformity statement may identify the residual but cannot be used to claim the
  inner trace or equation `(15)` unconditionally.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryTrace.lean`.
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
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 28
  Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: no new compaction at Loop 28 route selection. Current governance, V4.1,
  HANDOFF, Targets/TargetChecks, the H6 attempt log, hard-gap DAG, route card, complete Loop 27
  preregistration/outcome, relevant production modules, Nemes's local source, mathlib interval and
  dominated-convergence APIs, and the external ledger were re-read before selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.
