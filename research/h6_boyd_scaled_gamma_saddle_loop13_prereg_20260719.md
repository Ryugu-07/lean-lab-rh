# H6 Boyd Scaled-Gamma Saddle Integral Loop 13 Preregistration

Date: 2026-07-19

Campaign: `PROOF-ATTEMPT-20260719-H6-BOYD-SADDLE-INTEGRAL-01`

Mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED / CI_GATE_PENDING`

## Exact target

Define, for real `x,t`,

```text
phase(t) = t - 1 - log(t)
saddleIntegrand(x,t) = exp(-x*phase(t))/t.
```

Prove for every `x>0`:

```text
IntegrableOn (saddleIntegrand x) (Ioi 0)

GammaStar(x)
  = sqrt(x/(2*pi)) * integral_(0,infinity) saddleIntegrand(x,t) dt,
```

where `GammaStar(x)` is the existing project function
`deBruijnNewmanPolymathScaledGamma (x : C)`. The right side is embedded from `R` into `C`.

## Proposed Lean declarations

```lean
def deBruijnNewmanPolymathBoydSaddlePhase (t : R) : R :=
  t - 1 - Real.log t

def deBruijnNewmanPolymathBoydSaddleIntegrand (x t : R) : R :=
  Real.exp (-x * deBruijnNewmanPolymathBoydSaddlePhase t) / t

theorem deBruijnNewmanPolymathBoydSaddleIntegrand_integrableOn
    {x : R} (hx : 0 < x) :
    IntegrableOn (deBruijnNewmanPolymathBoydSaddleIntegrand x) (Set.Ioi 0)

theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydSaddleIntegral
    {x : R} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : C) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        integral (deBruijnNewmanPolymathBoydSaddleIntegrand x) over Set.Ioi 0 : R) : C)
```

The final set-integral syntax may follow mathlib notation. The phase, sign, domain, normalization,
and actual project scaled-Gamma function are fixed.

## Derivation and source alignment

Start from Euler's real Gamma integral and make only the positive scaling `y=x*t`:

```text
Gamma(x) = x^x * integral_(0,infinity) exp(-x*t)*t^(x-1) dt.
```

For `t>0`, rewrite

```text
exp(x)*exp(-x*t)*t^(x-1)
  = exp(-x*(t-1-log(t)))/t.
```

Then divide by the project's positive-real principal-branch Stirling main term. This is the
standard real saddle integral whose critical point is `t=1`. It is the first exact analytic input
to Boyd's steepest-descent geometry. The subsequent logarithmic coordinate `t=exp(u)` and Boyd's
global inverse-saddle resurgence decomposition are not part of this loop.

## Position in the RH graph

- `node_id`: `H6-Q1`
- `relation_to_RH`: upstream analytic infrastructure for Boyd/Nemes equation `(15)`, then the
  Polymath Proposition 6.1 final-region certificate.
- `assumption_frontier_before`: Loop 12 publicly proves both actual equation `(15)` kernels
  Bochner integrable and defines/reduces the source-exact RHS. It does not identify that RHS with
  the actual project `R2`.
- `hard_gap_before`: Boyd's saddle-coordinate/Cauchy resurgence decomposition, equation `(15)`,
  the contour rotation, effective `R2`, Proposition 6.1/6.3, and all Table 1 certificates remain
  open.

## Success and falsification

- `success_criterion`: both displayed declarations compile for every `x>0`, using Euler's actual
  Gamma integral and the project's actual principal-branch Stirling main term; exact witnesses,
  selected standard-only axiom prints, forbidden scans, full build, and public
  implementation/evidence CI pass.
- `falsification_criterion`: the scaling gives a different phase or factor, positive-real branch
  alignment fails, or the saddle integrand is not integrable on an endpoint.
- `proper_prefix_rule`: if final scaled-Gamma normalization does not compile, retain only an exact
  Euler-Gamma scaling identity or integrability theorem that removes a named step above. A phase
  definition or pointwise algebra alone is not progress.
- `anti_substitution_rule`: do not assume Boyd/Nemes equation `(15)`, any `R2` estimate, an
  effective Stirling theorem, an unspecified asymptotic, or a replacement Gamma function.

## Known obstacles and audited APIs

- Mathlib supplies `Real.Gamma_eq_integral`, `Complex.Gamma_ofReal`, and
  `integral_comp_mul_left_Ioi`; these cover the positive scaling `y=x*t`.
- The principal-power main term must be reduced using positivity of `x` and the exact principal
  complex logarithm on positive reals.
- The real-rpow/exponential identity on `t>0`, integrability transport under pointwise equality,
  and the square-root normalization must all be kernel-checked.
- The all-real-axis substitution `t=exp(u)` is intentionally deferred because its global improper
  change of variables requires a separate split/limit argument.

## Next decision

- `next_if_success`: preregister `t=exp(u)`, then the analytic inverse of
  `w^2/2=exp(u)-u-1` and its adjacent `2*pi*i` saddle-image decomposition.
- `next_if_blocked`: record the exact failed real-rpow, branch, or improper-integral transport and
  attack that lemma directly.
- `global_goal`: remains active regardless of this local result.

No Loop 13 proof source may be edited before this preregistration passes public Lean Action CI.
