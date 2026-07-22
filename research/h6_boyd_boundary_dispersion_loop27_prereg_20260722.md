# H6 Boyd Boundary Dispersion Loop 27 Preregistration

Date: 2026-07-22

Campaign: `PROOF-ATTEMPT-20260722-H6-BOYD-BOUNDARY-DISPERSION-01`

Mode: `PROOF-ATTEMPT`

Status: `LOCAL_IMPLEMENTATION_VERIFIED_PUBLIC_IMPLEMENTATION_CI_PENDING`

## Opening

RH is the goal. This campaign directly attacks Boyd--Nemes equation `(15)` at `N = 2`. Loop 25
reduced that equation to one exact positive-real contour equality. Loop 26 certified the first
adjacent Puiseux jumps but found that the available origin chart meets its exact radius boundary at
the first adjacent saddles. Loop 27 changes mechanisms: it uses the already compiled reflection
product for the actual scaled Gamma function to turn the exponential ray weights in `(15)` into a
boundary jump, then attacks that jump as a two-half-plane Cauchy projection. The compiler decides
every retained claim.

## Baseline and route selection

- `parent_commit`: `5e0ded1d18d016a161d51c181791cb893011d5da`.
- `baseline_public_ci`: Lean Action run `29738150076`, build job `88338316298`, passed in `2m5s`
  for the Loop 26 final ledger.
- `selected_node`: `OBS-H6-BOYD-R2-GLOBAL-CUT-STITCHING-01`, immediately upstream of
  `H6.debruijn-newman.boyd-r2-equation-15`, the effective `R2` estimate, and the Polymath
  Proposition 6.1 final-region certificate.
- `value_ranking`: retain H6-Q1 but pivot from inverse-chart stitching to a direct boundary-value
  decomposition of the scaled Gamma function. This reuses the actual equation `(15)`, the compiled
  Gamma reflection product, and Loop 25 right-half-plane analyticity while bypassing the Loop 26
  first-chart radius barrier.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Source audit and normalization

- Nemes, arXiv `1310.0166`, Section 2, defines
  `GammaStar(z) = sum_{n<N} (-1)^n gamma_n/z^n + R_N(z)` and
  `1/GammaStar(z) = sum_{n<N} gamma_n/z^n + inverseR_N(z)`, then states Boyd's resurgence
  formulas as equation `(15)` for `Re z > 0`. The project source file is
  `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`, SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Boyd 1994, *Gamma function asymptotics by an extension of the method of steepest descents*,
  Proc. R. Soc. Lond. A 447, 609--630, DOI `10.1098/rspa.1994.0158`, equations `(2.14)` and
  `(4.2)`, is the primary derivation cited by Nemes.
- The project definition
  `deBruijnNewmanPolymathScaledGamma z = Gamma z / GammaStirlingMain z` is Nemes's
  `GammaStar(z)`. The project definition
  `deBruijnNewmanPolymathGammaStirlingR2 z = GammaStar(z) - 1 - 1/(12*z)` is exactly `R_2`.
- The existing theorem `deBruijnNewmanPolymathScaledGamma_mul_neg` proves Nemes equation `(28)`
  in the actual principal-power normalization. No boundary-value or asymptotic formula is imported
  from prose.

## Fixed mathematical objects

Write `G(z)` for the project scaled Gamma and `R2(z)` for the project remainder. Define

```text
inverseR2(z) = 1/G(z) - 1 + 1/(12*z),
J(z)         = G(z) - 1/G(-z).
```

For `s > 0`, put `q(s) = exp(-2*pi*s)`. The compiled product identity gives the exact boundary
relations

```text
q(s) G( i*s) = J( i*s),
q(s) G(-i*s) = J(-i*s).
```

For `z != 0`, direct source-normalized algebra gives

```text
J(z) = R2(z) - inverseR2(-z).
```

Thus `J` is the boundary difference of an `R2` function analytic in the right half-plane and a
reflected inverse remainder analytic in the left half-plane.

## Exact mathematical target

For every `z` with `Re z > 0`, prove the Boyd--Nemes representation

```text
R2(z) = BoydR2Integral(z).
```

The proof must pass through the following exact boundary-dispersion chain.

1. Prove both exponential boundary-jump identities for every `s > 0`, with the signs and the
   project principal branches fixed by `deBruijnNewmanPolymathScaledGamma_mul_neg`.
2. Prove `J(z) = R2(z) - inverseR2(-z)` for every nonzero `z`, and prove `inverseR2` is analytic
   on the right half-plane while `z -> inverseR2(-z)` is analytic on the left half-plane.
3. Rewrite the complete source-defined Boyd `R2` integral exactly as the upward imaginary-axis
   boundary projection

   ```text
   -(1/(2*pi*i*z)) * integral_(xi on i*R) xi*J(xi)/(xi-z) dxi,
   ```

   or an equivalent pair of positive-ray Bochner integrals whose equality to the displayed
   projection is compiler checked. No orientation or normalization may be left to prose.
4. Establish a finite-contour Cauchy projection identity. It must split the right-half-plane
   contribution of `R2` from the left-half-plane contribution of `inverseR2(-z)` and expose every
   non-imaginary boundary edge explicitly. A removable Cauchy kernel or an equivalent disk/rectangle
   construction may be used.
5. Pass the boundary to infinity and to the imaginary axis by proving the required edge limits.
   The resulting right-half-plane projection is `R2(z)` and the reflected left-half-plane
   projection is zero. Substitute the boundary-jump rewrite to close equation `(15)`.

## Proposed Lean surface

Names and finite-contour parameterization may be adjusted for type correctness, but the
quantifiers, signs, and normalization are fixed.

```lean
def deBruijnNewmanPolymathScaledGammaInverseR2 (z : Complex) : Complex :=
  1 / deBruijnNewmanPolymathScaledGamma z - 1 + 1 / (12 * z)

def deBruijnNewmanPolymathScaledGammaBoundaryJump (z : Complex) : Complex :=
  deBruijnNewmanPolymathScaledGamma z -
    1 / deBruijnNewmanPolymathScaledGamma (-z)

theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_I
    {s : Real} (hs : 0 < s) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump ((s : Complex) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma ((s : Complex) * Complex.I)

theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_neg_I
    {s : Real} (hs : 0 < s) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump (-(s : Complex) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma (-(s : Complex) * Complex.I)

theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders
    {z : Complex} (hz : z != 0) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump z =
      deBruijnNewmanPolymathGammaStirlingR2 z -
        deBruijnNewmanPolymathScaledGammaInverseR2 (-z)

theorem deBruijnNewmanPolymathScaledGammaInverseR2_differentiableOn_rightHalfPlane :
    DifferentiableOn Complex deBruijnNewmanPolymathScaledGammaInverseR2
      {z : Complex | 0 < z.re}

theorem deBruijnNewmanPolymathBoydR2Integral_eq_boundaryJumpProjection
    {z : Complex} (hz : 0 < z.re) :
    deBruijnNewmanPolymathBoydR2Integral z =
      deBruijnNewmanPolymathBoydBoundaryJumpProjection z

theorem deBruijnNewmanPolymathBoydBoundaryProjection_finiteContour
    (parameters satisfying the registered finite-domain inequalities) :
    finiteImaginaryBoundary =
      -2 * Real.pi * Complex.I * z *
          deBruijnNewmanPolymathGammaStirlingR2 z + explicitEdgeResidual

theorem deBruijnNewmanPolymathBoydBoundaryProjection_eq_R2
    {z : Complex} (hz : 0 < z.re) :
    deBruijnNewmanPolymathBoydBoundaryJumpProjection z =
      deBruijnNewmanPolymathGammaStirlingR2 z
```

The final theorem may use the existing Loop 25 implication from the positive-real contour equality
or prove the right-half-plane statement directly.

## Proof strategy fixed before editing

1. Derive the two ray identities by specializing the compiled reflection product at `i*s`, proving
   the exponential value exactly, and cancelling only with already compiled nonvanishing theorems.
2. Introduce the source-aligned inverse remainder and prove the jump split by field algebra. Prove
   its right-half-plane analyticity from the compiled nonvanishing and differentiability of `G`.
3. Rewrite each existing `Ioi 0` integrand pointwise using the jump identities. Preserve the
   existing integrability certificates and combine the two rays with an explicit orientation
   theorem.
4. Build a generic finite right/left half-plane Cauchy projection certificate using mathlib's
   rectangle or circle Cauchy integral API. Use a divided-slope/removable kernel at the evaluation
   point if the finite contour crosses the Cauchy pole. Keep all vertical, horizontal, and outer
   edges in the theorem statement.
5. Instantiate the certificate with `z*R2(z)` and the reflected inverse remainder. Attempt to
   prove the edge limits from project facts. If the necessary second-order Stirling decay is not
   derivable from the current library, stop only after the exact finite projection and the exact
   named decay hypotheses have compiled.

## Success, falsification, and meaningful partial

- `success_criterion`: compile
  `forall z, 0 < z.re -> R2(z) = BoydR2Integral(z)`, thereby proving Boyd--Nemes equation `(15)`
  at `N = 2` without adding a nonstandard premise.
- `minimum_hard_gap_reduction`: all of the following must compile as one auditable chain:
  the two exact ray-jump identities; the exact split into `R2` and reflected `inverseR2`; analytic
  separation on opposite half-planes; the complete Boyd-integral boundary-jump rewrite; and either
  a finite-contour Cauchy identity with every residual edge explicit or an exact iff/reduction from
  equation `(15)` to named edge-vanishing limits. The first three algebraic/analytic items alone
  are insufficient.
- `falsification_criterion`: a compiled theorem shows that either ray sign, the inverse-remainder
  normalization, the imaginary-axis orientation, or the Cauchy projection coefficient differs
  from the fixed formulas. Record the exact corrected statement and do not repair it by redefining
  the project `R2` or Boyd integral.
- `local_stop`: stop when equation `(15)` compiles, a falsification theorem compiles, or the full
  minimum hard-gap reduction compiles and the remaining first obstruction is an exact project-
  specific edge-decay/asymptotic statement. Local stop returns to value-ranked route selection and
  never pauses the persistent RH Goal.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes the actual scaled-Gamma reflection product, its
  nonvanishing on both imaginary rays, exact Boyd `N = 2` ray integrability, right-half-plane
  analyticity of the actual `R2` and Boyd integral, the actual positive-real inverse-Jacobian
  remainder, and the Loop 25 iff reducing equation `(15)` to positive-real contour equality.
- `still_open_before`: no inverse-`R2` object is registered; no exponential ray weight has been
  rewritten as a Gamma boundary jump; no two-half-plane projection theorem is available; no
  second-order Stirling decay on unbounded contour edges is compiled. Equation `(15)`, effective
  `R2`, Table 1, H6-E/G8, and RH remain open.
- `anti_substitution`: do not assume equation `(15)`, a Binet/Stieltjes remainder formula, a
  Plemelj theorem specialized to this function, second-order Stirling asymptotics, edge decay,
  boundary homology, the Loop 26 exterior inverse charts, or any model-original analytic premise.
- `conjecture_status`: no model-original conjecture is admitted as a premise. Conditional finite-
  contour or limit statements may identify the residual but cannot be used to claim equation
  `(15)` unconditionally.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathBoydBoundaryDispersion.lean`.
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
- This preregistration alone must be committed and pass public Lean Action CI before any Loop 27
  Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: Loop 27 begins after one inherited compaction following Loop 26 closure.
  Canonical governance, V4.1, `HANDOFF.md` plus its auditor diff, Targets/TargetChecks, the current
  H6 attempt, hard-gap DAG, Loop 26 preregistration, relevant production definitions, Nemes's local
  source, and the external ledger were re-read before this route selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.

## Outcome

- `classification`: `MEANINGFUL_PARTIAL / HARD_GAP_REDUCED`.
- `success_criterion`: not met. Boyd--Nemes equation `(15)` is not claimed.
- `minimum_hard_gap_reduction`: met. Lean compiles both exact ray jumps, the exact direct/inverse
  `R2` split, analytic separation on opposite half-planes, the complete Boyd boundary-jump
  rewrite, exact finite right/left rectangle projections, and a canonical finite identity with
  every outer-edge residual named.
- `aggregate_certificate`:
  `deBruijnNewmanPolymathBoydBoundaryDispersionCertificate`.
- `conditional_closure`:
  `deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_boundaryDispersionLimits` proves equation `(15)`
  from the three clauses of `deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate`.
- `first_remaining_obstruction`: `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01`, consisting of the
  two named outer-edge residual limits and the inner boundary-trace limit. The needed complex
  second-order Stirling/closed-half-plane control is not in mathlib or current project K0.
- `mechanical_result`: the 750-line production module, Targets, eight exact TargetChecks, ten
  selected axiom prints, forbidden scans, `git diff --check`, and full 8,732-job build pass. All
  selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- `public_preregistration`: commit `d3d95ed555139112f5826bde32c3bd1a767d499e`, Lean Action run
  `29884574692`, build job `88812386449`, passed in `1m52s` before source editing.
- `public_implementation`: pending.
- `compaction_state_after`: two compaction recoveries occurred in Loop 27; authoritative files were
  re-read after each.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active. Local stop returns to value-ranked
  route selection after the planned one-loop rest.
