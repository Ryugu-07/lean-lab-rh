# H6 Boyd R2 Loop 12 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-R2-EQ15-01`

Mode: `PROOF-ATTEMPT`

Status: `PARTIAL / BLOCKER_EXPOSED`

## Exact target

Let

```text
GammaStar(z) = Gamma(z) / GammaStirlingMain(z)
R2(z) = GammaStar(z) - 1 - 1/(12*z).
```

For every `z : C` with `0 < Re z`, prove the `N=2` specialization of Boyd/Nemes equation `(15)`:

```text
R2(z)
  = (1/(2*pi*i)) * (i^2/z^2)
      * integral_(0,infinity)
          s*exp(-2*pi*s)*GammaStar(i*s)/(1-i*s/z) ds
    - (1/(2*pi*i)) * ((-i)^2/z^2)
      * integral_(0,infinity)
          s*exp(-2*pi*s)*GammaStar(-i*s)/(1+i*s/z) ds.
```

Both displayed complex Bochner integrands must be proved integrable on `Set.Ioi 0`. The theorem
must use the actual project definitions
`deBruijnNewmanPolymathScaledGamma` and
`deBruijnNewmanPolymathGammaStirlingR2`; no abstract remainder predicate is allowed.

## Proposed Lean declarations

```lean
def deBruijnNewmanPolymathBoydR2PlusIntegrand (z : C) (s : R) : C :=
  ((s * Real.exp (-2 * Real.pi * s) : R) : C) *
    deBruijnNewmanPolymathScaledGamma ((s : C) * Complex.I) /
      (1 - ((s : C) * Complex.I) / z)

def deBruijnNewmanPolymathBoydR2MinusIntegrand (z : C) (s : R) : C :=
  ((s * Real.exp (-2 * Real.pi * s) : R) : C) *
    deBruijnNewmanPolymathScaledGamma (-((s : C) * Complex.I)) /
      (1 + ((s : C) * Complex.I) / z)

theorem deBruijnNewmanPolymathBoydR2_integrableOn
    {z : C} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydR2PlusIntegrand z) (Set.Ioi 0) /\
    IntegrableOn (deBruijnNewmanPolymathBoydR2MinusIntegrand z) (Set.Ioi 0)

theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_integrals
    {z : C} (hz : 0 < z.re) :
    deBruijnNewmanPolymathGammaStirlingR2 z =
      (1 / (2 * Real.pi * Complex.I)) * (Complex.I ^ 2 / z ^ 2) *
          integral (deBruijnNewmanPolymathBoydR2PlusIntegrand z) over Set.Ioi 0 -
      (1 / (2 * Real.pi * Complex.I)) * ((-Complex.I) ^ 2 / z ^ 2) *
          integral (deBruijnNewmanPolymathBoydR2MinusIntegrand z) over Set.Ioi 0
```

The final syntax of the set integrals may follow mathlib notation, but the mathematical factors,
signs, domain, and project functions are fixed by this preregistration.

## Position in the RH graph

- `node_id`: `H6-Q1`
- `relation_to_RH`: known-mathematics bridge toward the unconditional Polymath Table 1 final-region
  certificate, hence weaker than RH but on the selected H6 route.
- `assumption_frontier_before`: Loop 11 publicly compiles branch/conjugation, scaled-Gamma
  continuation, imaginary-axis norms, the Phragmen--Lindelof application interface, reflected
  ray/Stokes transfer, denominator constants, and the final `<41/2000` arithmetic. No effective
  `R2` estimate or Boyd integral representation is K0.
- `hard_gap_before`: the actual Boyd/Nemes equation `(15)`, its absolute integrability, and the
  subsequent Theorem 3 contour rotation are absent. Proposition 6.1 remains conditional on the
  `41/2000` remainder estimate.

## Source alignment

- Primary source: G. Nemes, arXiv `1310.0166`, equation `(15)`, which records Boyd's resurgence
  formula for `Re z > 0`; local TeX SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`.
- Original source: W. G. C. Boyd, Proc. R. Soc. A 447 (1994), 609--630, DOI
  `10.1098/rspa.1994.0158`.
- Project normalization: `GammaStar(z)` is exactly
  `deBruijnNewmanPolymathScaledGamma z`; the `N=2` truncation is exactly
  `1 + 1/(12*z)`, so Nemes's `R_2` is the existing project remainder.
- Coefficient audit: `i^2=(-i)^2=-1`, but the implementation retains the source's two-term form
  until a separate algebraic simplification is proved, preventing a sign from being hidden.

## Success and falsification

- `success_criterion`: both actual kernels are Bochner integrable on `(0,infinity)` and the exact
  project `R2` identity compiles for every `Re z > 0`; exact TargetChecks, selected standard-only
  axiom prints, forbidden scans, full build, and public implementation/evidence CI pass.
- `falsification_criterion`: the source formula requires a different principal-power branch,
  an omitted sector condition, a coefficient convention incompatible with the project `R2`, a
  nonintegrable endpoint, or a sign/factor that prevents exact equality.
- `proper_prefix_rule`: if the identity does not compile, retain only source-exact denominator,
  imaginary-axis kernel, integrability, holomorphy, or positive-real Euler-integral results that
  remove a named equation `(15)` dependency. Merely defining the RHS is not progress.
- `anti_substitution_rule`: do not assume equation `(15)`, the target `R2` bound, an equivalent
  effective Stirling formula, an unspecified asymptotic big O, or a replacement Gamma function.

## Known obstacles and new angle

- Mathlib has Euler's Gamma integral and holomorphy, but no Binet/Stieltjes formula, Boyd
  resurgence formula, or effective complex Stirling remainder.
- Nemes cites Boyd for equation `(15)` rather than reproving it. Reconstructing the equality may
  require a steepest-descent contour decomposition or an equivalent Binet representation.
- The new angle specializes immediately to `N=2`. It avoids arbitrary Stirling coefficients and
  uses Loop 11's exact theorem
  `norm(GammaStar(i*s))^2=1/(1-exp(-2*pi*s))` plus conjugation to control both kernels.
- For `Re z > 0`, denominator geometry gives a uniform nonzero lower bound for
  `1 +/- i*s/z`; the remaining scalar majorant behaves like `sqrt(s)` at zero and like
  `s*exp(-2*pi*s)` at infinity.
- After integrability, the planned identity attack is: derive the positive-real formula from the
  Euler Gamma integral and a source-faithful contour decomposition, prove the integral RHS
  holomorphic on `Re z > 0`, then use the identity theorem. Any failure is logged at its exact
  contour or limit exchange.

## Next decision

- `next_if_success`: preregister the Nemes Theorem 3 contour rotation and derive the uniform
  right-half-plane `R2` estimate, then combine it with the public Loop 11 Stokes/conjugation chain.
- `next_if_blocked`: record the first failed contour identity and switch to a direct proof of
  Stieltjes equation `(13)` or Binet's log-Gamma formula as the missing upstream edge.
- `global_goal`: remains active regardless of this local result.

No Loop 12 proof source may be edited before this preregistration passes public Lean Action CI.

Preregistration commit `00be4a5bfa3c614482aa4374a177fa73fa3bd131` passed public Lean Action CI
run `29659498616`, build job `88119559667`, in `1m31s`. Loop 12 proof-source work is admitted.

## Local outcome

The kernel-integrability half of the success criterion compiles in the 453-line production module
`LeanLab/Riemann/DeBruijnNewmanPolymathBoydR2Integral.lean`. Lean proves the exact positive-ray
weight norm square and the global domination

```text
|s*exp(-2*pi*s)*GammaStar(i*s)| <= sqrt(s)*exp(-pi*s),  s>0,
```

then proves continuity and Bochner integrability of both actual kernels after establishing the
right-half-plane denominator bounds. The source-exact RHS is defined without changing signs or
coefficients, normalized algebraically, and reduced on the positive real axis to one integral
imaginary part by compiled conjugation.

The equality with the actual project `R2` remains open. Nemes states equation `(15)` by citation to
Boyd; the available Euler Gamma integral does not include Boyd's global saddle-coordinate inverse
and Cauchy/resurgence decomposition, and no equivalent theorem exists in mathlib or the project.
`deBruijnNewmanPolymathBoydR2RepresentationAt` is only the name of this open proposition and is not
a theorem or premise. Thus Loop 12 closes as `PARTIAL / BLOCKER_EXPOSED`, with
`hard_gap_delta=0` and `route_infrastructure_delta=1`.

Standalone compilation, exact Targets and three new TargetChecks, selected standard-only axiom
prints, forbidden scan, `git diff --check`, and the full 8,717-job build pass locally.

The next selected upstream edge is the exact positive-real saddle integral obtained from Euler's
Gamma integral by `t=x*exp(u)`. It is a source-faithful first step toward Boyd's steepest-descent
derivation and does not assume equation `(15)`. The global RH Goal remains active.

Implementation commit `75d39360af35c3fc65ef357b3e4d1aa498c32602` passed public Lean Action CI
run `29660452525`, build job `88122109932`, in `2m17s`. The retained proper prefix is publicly
checked; this evidence update does not change the `PARTIAL / BLOCKER_EXPOSED` classification.
