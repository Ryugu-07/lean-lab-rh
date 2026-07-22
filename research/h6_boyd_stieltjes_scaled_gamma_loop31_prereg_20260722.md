# H6 Boyd Stieltjes Scaled-Gamma Loop 31 Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H6-BOYD-STIELTJES-SCALED-GAMMA-01`

Mode: `LITERATURE`

Status: `PREREGISTERED / PROOF_SOURCE_FROZEN_PENDING_PUBLIC_CI`

## Opening

RH is the goal. Loop 31 attacks the shared analytic input behind the sole remaining inner-trace
child and both Loop 27 outer-edge limits. It reconstructs the Stieltjes representation of the
actual project scaled Gamma from mathlib's Gamma limit formula and factorial Stirling theorem,
then extracts the mean `1/12` of the periodic kernel to obtain direct and inverse second-order
complex Stirling bounds. The formula and bounds may then be used to close the shifted tail and
the two outer edges. No form of Boyd--Nemes equation `(15)`, no conditional project `R2` bound,
and no unproved log-Gamma formula may be used as a premise. Every retained claim is decided by
Lean.

## Baseline and route selection

- `parent_commit`: `eed4a6fc3640582cfb52e39c67642b46a14fcfed`.
- `baseline_public_ci`: Lean Action run `29893099154`, build job `88837366066`, passed in `1m49s`
  for the Loop 30 final ledger.
- `selected_nodes`: `OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01` and the two outer-edge clauses
  of `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01`.
- `value_ranking`: all three open limits require the same noncircular closed-right-half-plane
  second-order Stirling control. Attacking only one residual would duplicate this missing input.
  Nemes equation `(13)` provides a source-faithful common parent: after subtracting the kernel
  mean, a bounded periodic primitive gives an `O(|z|^-2)` logarithmic remainder, and the complex
  exponential remainder gives both direct and inverse `R2` bounds. This dominates a tail-only or
  one-edge campaign in hard-gap value.
- `mode_reason`: the central identity is a known Stieltjes representation quoted in the human
  literature. Its reconstruction and exact formal frontier belong to `LITERATURE`, even though
  the campaign then applies it to an open project obligation.
- `persistent_goal`: H6-Q1 and the global RH Goal remain active in every local outcome.

## Primary source and M0 definition alignment

- Primary working source: G. Nemes, arXiv `1310.0166`, Section 2, equation `(13)`, local TeX
  `/Users/karasuakamatsu/Downloads/1310.0166-source/2013155.tex`, SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Nemes defines

  ```text
  Q(t) = (1/2) * ({t} - {t}^2),
  GammaStar(z) = exp(integral_0^infinity Q(t)/(z+t)^2 dt), |arg z| < pi.
  ```

- The proposed Lean kernel uses `Int.fract t = t - floor(t)`, exactly Nemes's fractional part.
  The coefficient, square, denominator, orientation, and Lebesgue measure are unchanged.
- The project function
  `deBruijnNewmanPolymathScaledGamma z = Gamma z / GammaStirlingMain z` uses the same
  `sqrt(2*pi) * exp((z-1/2)*log z-z)` normalization and principal complex logarithm.
- The retained representation is initially restricted to `0 < z.re`. This is a strict
  specialization of `|arg z| < pi`, exactly sufficient for the shifted lines and reflected left
  remainder; it is not a change of normalization or branch.
- Nemes quotes the Stieltjes formula rather than proving it. Loop 31 must reconstruct it from K0:
  `Complex.GammaSeq_tendsto_Gamma`, the exact finite Gamma product, complex
  `tendsto_one_add_div_pow_exp`, and `Real.Stirling.tendsto_stirlingSeq_sqrt_pi`, together with
  finite interval calculus. The cited formula itself is not an admissible premise.

## Exact mathematical target

For real `t`, define

```text
Q(t) = (1/2) * (fract(t) - fract(t)^2).
```

For `Re z > 0`, define the absolutely convergent logarithmic remainder

```text
L(z) = integral over t in (0,infinity) of Q(t)/(z+t)^2.
```

Prove, from the project definitions,

```text
GammaStar(z) = exp(L(z)).
```

The finite reconstruction must expose the exact unit-block identity

```text
integral_0^1 [(u-u^2)/2]/(z+n+u)^2 du
  = (z+n+1/2) * (log(z+n+1)-log(z+n)) - 1,
```

and connect its finite sum to `Complex.GammaSeq`; a theorem which merely postulates an analytic
logarithm of `GammaStar` does not meet the target.

Next prove the exact kernel facts

```text
0 <= Q(t) <= 1/8,
integral_0^1 Q(t) dt = 1/12,
P(u) = u^2/4-u^3/6-u/12,
P'(u) = (u-u^2)/2-1/12,
P(0)=P(1)=0,
|P(u)| <= 1/2 for 0<=u<=1.
```

Unit-block integration by parts and summation must then give, for `Re z > 0`,

```text
|L(z)| <= 1/(4*|z|),
|L(z)-1/(12*z)| <= 2/|z|^2.
```

The constants are deliberately conservative and fixed. Combining these inequalities with the
compiled complex estimate `|exp(w)-1-w| <= |w|^2` for `|w|<=1`, prove for `Re z>0` and
`1 <= |z|`

```text
|GammaStar(z)-1-1/(12*z)| <= 3/|z|^2,
|1/GammaStar(z)-1+1/(12*z)| <= 3/|z|^2.
```

Finally apply these bounds, without strengthening them as premises, to prove:

1. the canonical shifted-tail residual tends to zero for every `Re z>0` and every `A>0`;
2. the Loop 28 inner boundary trace is unconditional;
3. the canonical right `R2` outer-edge residual tends to zero;
4. the canonical reflected inverse-`R2` left outer-edge residual tends to zero;
5. `deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate` and hence Boyd--Nemes equation
   `(15)` hold for every `Re z>0`.

## Proposed Lean surface

Names and syntactic packaging may be adjusted for type correctness, but the actual scaled-Gamma
identity, explicit constants, and registered residuals are fixed.

```lean
def deBruijnNewmanPolymathStieltjesQ (t : Real) : Real :=
  (1 / 2) * (Int.fract t - (Int.fract t) ^ 2)

def deBruijnNewmanPolymathStieltjesLogRemainder (z : Complex) : Complex :=
  integral (fun t : Real =>
    (deBruijnNewmanPolymathStieltjesQ t : Complex) /
      (z + (t : Complex)) ^ 2) (volume.restrict (Set.Ioi 0))

theorem deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes
    {z : Complex} (hz : 0 < z.re) :
    deBruijnNewmanPolymathScaledGamma z =
      Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z)

theorem deBruijnNewmanPolymath_stieltjesLogRemainder_sub_first_norm_le
    {z : Complex} (hz : 0 < z.re) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z)‖ <=
      2 / ‖z‖ ^ 2

theorem deBruijnNewmanPolymathGammaStirlingR2_norm_le_three
    {z : Complex} (hz : 0 < z.re) (hzNorm : 1 <= ‖z‖) :
    ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ <= 3 / ‖z‖ ^ 2

theorem deBruijnNewmanPolymathScaledGammaInverseR2_norm_le_three
    {z : Complex} (hz : 0 < z.re) (hzNorm : 1 <= ‖z‖) :
    ‖deBruijnNewmanPolymathScaledGammaInverseR2 z‖ <= 3 / ‖z‖ ^ 2

theorem deBruijnNewmanPolymathBoydBoundaryTailResidual_tendsto_canonical
    {z : Complex} (hz : 0 < z.re) {A : Real} (hA : 0 < A) :
    Filter.Tendsto
      (fun n : Nat => deBruijnNewmanPolymathBoydBoundaryTailResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (nhds 0)

theorem deBruijnNewmanPolymathBoydBoundaryDispersionLimits :
    deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate
```

The production module must expose an aggregate certificate containing the source-aligned
Stieltjes identity, both explicit second-order bounds, and every downstream limit actually
proved. Full success includes the unconditional dispersion-limit certificate and equation `(15)`.

## Success, falsification, and meaningful partial

- `success_criterion`: compile `deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate` from
  the reconstructed Stieltjes representation and explicit direct/inverse bounds, then compile
  Boyd--Nemes equation `(15)` through the existing Loop 27 theorem.
- `minimum_hard_gap_reduction`: compile the actual project scaled-Gamma Stieltjes identity on
  `Re z>0` and both fixed `3/|z|^2` direct/inverse bounds. This closes the common missing analytic
  input even if one or more residual-limit integrations require a later campaign. A kernel bound,
  a finite-block formula alone, a GammaSeq asymptotic alone, or an `O(1/|z|)` bound is insufficient.
- `falsification_criterion`: Lean derives a different unit-block sign, kernel mean, scaled-Gamma
  normalization, first coefficient, or branch; or a concrete `Re z>0` witness contradicts one of
  the fixed constants. Record the corrected source alignment and do not alter existing `R2`,
  inverse-`R2`, tail, or edge definitions to force agreement.
- `local_stop`: stop when full success compiles, a falsification compiles, or the minimum exact
  representation and second-order bounds compile and every remaining residual-limit failure is
  reduced to a precise named integration obstruction. Local stop never pauses the persistent RH
  Goal.

## Known obstacles and nearest prior attempts

- Loop 25 audited this route but stopped after observing that mathlib had no packaged
  Binet/Stieltjes theorem; it did not attempt the finite GammaSeq reconstruction. Loop 31 is a
  substantive re-entry because its fixed mechanism is the exact unit-block integral plus
  GammaSeq/Stirling limit, not the Loop 25 inverse-Jacobian contour.
- Mathlib has no complex `logGamma` or Euler--Maclaurin theorem. The proof must avoid taking an
  unjustified global logarithm of Gamma and instead compare exponentials with the exact finite
  Gamma product.
- `Int.fract` is discontinuous at integers. Integrability and integration by parts must be done on
  unit blocks where the polynomial representative is valid; endpoint agreement then permits
  summation. No global derivative of `fract` may be asserted.
- The `sqrt(2*pi)` normalization requires the actual factorial Stirling limit. Replacing it with
  an unspecified nonzero constant would not prove the project identity.
- Tail and outer-edge closure require uniform integral estimates from the pointwise
  `3/|z|^2` bounds. Numerical sampling may guide algebra but cannot serve as a premise.

## Assumption frontier and anti-substitution

- `assumption_frontier_before`: K0 includes complex Gamma and GammaSeq convergence, factorial
  Stirling, principal complex log and cpow identities, complex exponential remainder estimates,
  measure and interval-integral calculus, all Loop 27 finite rectangle identities, and Loop 30's
  exact tail-only trace iff.
- `still_open_before`: no Stieltjes/log-Gamma representation, complex second-order Stirling bound,
  shifted-tail limit, inner trace, outer-edge limit, dispersion-limit certificate, equation `(15)`,
  effective Boyd Table 1 certificate, H6-E/G8, or RH is proved.
- `anti_substitution`: do not assume Nemes equation `(13)` or `(15)`, Binet, Euler--Maclaurin,
  complex Stirling asymptotics, either fixed `R2` bound, any residual limit, Phragmen--Lindelof
  growth hypotheses, or the dispersion certificate. Do not derive the new bound from the existing
  conditional `deBruijnNewmanPolymath_relative_stirling_of_R2_bound` chain.
- `conjecture_status`: no model-original conjecture is admitted. All displayed identities and
  inequalities are proof targets.

## Mechanical and publication gates

- Planned production module:
  `LeanLab/Riemann/DeBruijnNewmanPolymathStieltjesScaledGamma.lean`.
- Any retained spine must be imported and registered in `LeanLab/Riemann/Targets.lean`, receive
  name resolution and exact statement witnesses in `LeanLab/Riemann/TargetChecks.lean`, and have
  selected `#print axioms` entries in `LeanLab/Riemann/AxiomsAudit.lean`.
- At loop end update `attempts/h6_polymath_table_row_certificates.md`,
  `research/hard_gap_dag.md`, this preregistration outcome, `HANDOFF.md`, and the external active
  ledger.
- No proof placeholder, custom axiom, opaque or unsafe declaration, native evaluator shortcut, or
  resource-limit relaxation is permitted.
- Run standalone diagnostics, exact witnesses, selected axiom audits, all forbidden scans,
  `git diff --check`, the full project build, and public implementation/evidence/final-ledger CI.
- This preregistration and historical Loop 30 ledger corrections alone must be committed and pass
  public Lean Action CI before any Loop 31 Lean proof-source edit.

## Runtime disclosure

- `compaction_state`: one inherited compaction during Loop 31 route research. After recovery,
  current governance, HANDOFF, relevant Targets/TargetChecks, the H6 attempt tail, hard-gap DAG,
  complete Loop 30 preregistration/outcome, selected AxiomsAudit entries, Nemes equations
  `(13)--(15)`, external ACTIVE, RTK/memory rules, and git status were re-read before selection.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: the persistent RH Goal remains active.

## Outcome

- `result`: `PROVED / KNOWN_THEOREM_FORMALIZED / HARD_GAP_CLOSED`; full success compiled locally.
- `production_module`:
  `LeanLab/Riemann/DeBruijnNewmanPolymathStieltjesScaledGamma.lean`, 2,500 lines.
- `source_reconstruction`: Lean proves the actual project scaled Gamma equals the exponential of
  the Stieltjes integral on `Re z>0`. The proof derives the exact unit-block identity, telescopes
  finite blocks, reconstructs the positive-real value through `Real.BohrMollerup.logGammaSeq` and
  `Stirling.stirlingSeq`, and extends to the right half-plane by differentiability and the complex
  identity theorem. Equation `(13)`, Binet, Euler--Maclaurin, and a complex log-Gamma theorem are
  not premises.
- `explicit_bounds`: centering the periodic kernel at mean `1/12` and integrating its polynomial
  primitive by parts gives `|L(z)-1/(12*z)| <= 2/|z|^2`; the exponential remainder then gives both
  direct and inverse `3/|z|^2` bounds for `Re z>0`, `1<=|z|`.
- `downstream_closure`: indicator dominated convergence proves the canonical growing positive and
  negative shifted tails vanish. Loop 30's exact iff yields every positive-cutoff tail and the
  inner trace. Explicit three-edge estimates bound both canonical outer residuals by
  `24*(|z|+n+1)/(n+1)^2`, hence both vanish. The three unconditional limits instantiate
  `deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate`, and Lean proves Boyd--Nemes
  equation `(15)` for every `Re z>0`.
- `aggregate`: `deBruijnNewmanPolymathStieltjesScaledGammaCertificate` contains the actual
  Stieltjes identity, both explicit second-order bounds, canonical tail, inner trace, dispersion
  certificate, and equation `(15)`.
- `closed_obstructions`: `OBS-H6-BOYD-R2-BOUNDARY-TRACE-SHIFTED-TAIL-01`, its remaining
  uniform-integrability parent, and `OBS-H6-BOYD-R2-BOUNDARY-DISPERSION-LIMITS-01` are closed.
  The inverse-Jacobian global-cut-stitching route remains a bypassed route-specific problem, not a
  premise of equation `(15)`.
- `still_open_after`: unconditional Polymath Table 1 row certificates, source Proposition 6.1/6.3
  instantiation where still required, compact barrier and finite-RH inputs, H6-E/G8, and RH.
- `local_mechanical_audit`: the production source compiles standalone and as a Lake target; the
  Target, ten exact TargetChecks, eleven selected `#print axioms` entries, forbidden scans,
  `git diff --check`, and the full 8,736-job build pass. Every selected declaration depends only
  on `propext`, `Classical.choice`, and `Quot.sound`.
- `public_preregistration`: commit `340e8ebfcf917dd17e03f36a22f2995be62c4058`, CI run
  `29893818120`, build job `88839576741`, passed in `1m32s` before proof editing.
- `public_implementation`: commit `a0931346a32400e937bbb1333ea355649d8ec101`, CI run
  `29916415509`, build job `88911217586`, passed in `2m15s`.
- `public_closure`: pending.
- `compaction_state`: five inherited compaction summaries during Loop 31. After each recovery the
  canonical governance, HANDOFF, relevant Targets/TargetChecks, H6 attempt, hard-gap DAG, complete
  preregistration, current source, selected AxiomsAudit entries, external ACTIVE ledger, and git
  status were re-read before continuing.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `local_stop`: full success has compiled, so Loop 31 stops locally after public implementation,
  closure-evidence, and final-ledger CI. The persistent RH Goal remains active.
