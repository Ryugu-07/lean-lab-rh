# H6 x H14 x H12 Height-Ten Riemann--Siegel Low-Zero Preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-LOW-ZERO-01`

Mode: `PROOF-ATTEMPT / LITERATURE / CROSS-ROUTE-REENTRY`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Historical route and new combination

The classical Riemann--Siegel formula verifies low critical-line intervals by combining a short
main sum with a controlled contour remainder. In the interval `13/2<=t<=10`, the natural cutoff
`floor(sqrt(t/(2*pi)))` is one, so the source main sum consists of a single residue.

The project already compiles the exact Titchmarsh--Riemann--Siegel contour identity for
`riemannXi`, the finite residue decomposition for arbitrary `N`, and the analytic continuation
needed on the critical line. Those declarations were built in the H6 de Bruijn--Newman route but
have not been connected to the H14 low-zero datum required by the H12 height-ten certificate.

This differs materially from the previous thirty-term Euler--Maclaurin endpoint evaluator: it
uses one historical Riemann--Siegel residue plus one contour remainder over the complete interval,
rather than extending a table of isolated complex-power centers.

## Exact target

For `s=1/2+iy`, first prove that Schwarz reflection turns the existing finite Riemann--Siegel
identity into an exact real-part formula. At `N=1`, reduce the finite sum to the single source
prefactor:

```text
(1/8) * xi(s)
  = 2 * Re(prefactor(s) + R_(0,1)(s)).
```

The precise Lean form may coerce the real part back to `Complex` or state the equivalent
main-plus-conjugate identity.

Next prove the literal uniform margin

```text
forall y, 13/2 <= y -> y <= 10 ->
  abs (Re (R_(0,1)(1/2+iy))) < abs (Re (prefactor(1/2+iy))).
```

If the source phase makes the raw real-part comparison inconvenient, an equivalent normalized
Hardy-coordinate margin is allowed only when all normalizing factors are compiled and proved
nonzero.

From that margin, compile:

```lean
theorem riemannZeta_criticalLine_ne_zero_thirteenHalves_ten
    {y : Real} (hy0 : 13 / 2 <= y) (hy1 : y <= 10) :
    riemannZeta ((1 / 2 : Complex) + (y : Complex) * Complex.I) ≠ 0

theorem speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten
    {y : Real} (hy0 : 13 / 2 <= y) (hy1 : y <= 10) :
    (speiserZetaDerivRatio
      ((1 / 2 : Complex) + (y : Complex) * Complex.I)).re < 0
```

Names may change for elaboration, but statements may not be weakened.

## Success and partial-progress boundary

Full success requires the uniform remainder margin, actual zeta nonvanishing on the complete
closed interval, and the unconditional quotient sign. The following are meaningful partial but
not full success:

- the exact critical-line conjugation identity;
- the exact `N=1` decomposition;
- a consumer conditional on the unproved uniform margin;
- isolated point bounds;
- an integrability majorant without a replayable strict constant.

Navigation values, external first-zero tables, and floating-point quadrature are not premises.

## Known obstacle and planned attack

The current theorem
`norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_majorant` is intentionally coarse. It bounds
the principal-power phase by `|Im(s)|*pi`, sufficient for integrability and contour shifts but far
too large for the low-height one-term remainder.

The attack order is:

1. expose the exact critical-line real and `N=1` formulas;
2. retain the actual principal argument of the midpoint line instead of replacing it by `pi`;
3. combine that phase with the shifted Gaussian and denominator growth before taking an absolute
   integral;
4. compare a direct sharp source-line bound with the classical Riemann--Siegel remainder
   expansion;
5. kernel-check only the final rational inequalities required uniformly on `[13/2,10]`.

If the direct absolute contour bound is rigorously too weak, record its exact lower bottleneck and
switch to the classical saddle expansion. Do not optimize the endpoint `13/2`.

## Claim and axiom boundary

- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option;
- every admitted theorem must compile and pass exact TargetChecks;
- expected selected axiom frontier: `propext`, `Classical.choice`, and `Quot.sound`;
- no finite or numerical first-zero fact may be imported as an assumption;
- full success closes only the right-high vertical zone of the height-ten boundary;
- the other five vertical zones, complete top, literal height-ten certificate, H12, and RH remain
  separate until their declarations compile.

## Stopping rule

Stop this local subattack only after full success, a rigorous falsification of the proposed
margin form, or an exact proof that both the direct contour and classical remainder attacks need
an unavailable source theorem. Any local stop returns to route selection and never pauses the
parent campaign or global RH Goal.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed;
- `reasoning_effort`: not exposed;
- `budget`: no numerical quota under V4.1;
- `compaction_state`: active Goal state and current worktree re-read before selection;
- `global_goal`: active.
