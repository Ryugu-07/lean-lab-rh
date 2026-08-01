# H6 x H14 x H12 Height-Ten Riemann--Siegel Phase-Norm Preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Parent subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-LOW-ZERO-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-PHASE-NORM-01`

Mode: `PROOF-ATTEMPT / LITERATURE / HISTORICAL-OMISSION-SEARCH`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Source audit and route choice

The existing source-line estimate loses the exact principal argument in
`w ^ (-s)` by replacing it with the uniform bound `|Im(s)| * pi`. That replacement is useful for
integrability but is the exact reason its displayed upper bound cannot certify the low-height
one-term margin.

The classical sources do not supply a directly importable shortcut on the complete target
interval. O'Sullivan's symmetric Riemann--Siegel statement is source-aligned for `t>2*pi`, but
does not state an explicit low-height error constant. Gabcke's simple bound
`|R_0(t)| < 0.127*t^(-3/4)` is stated only for `t>=200`. Titchmarsh gives the historical explicit
calculation, but its simplified displayed remainder bound is also stated only at substantially
higher parameter. None of those high-height constants will be applied on `13/2<=t<=10`.

The selected attack therefore returns to the exact contour already compiled in the project and
retains the principal-argument term before taking norms. This is historical-route reconstruction
aimed at finding a missed closure in the existing source mechanism, not an optimization of an
arbitrary endpoint constant. Independent conjecture proposal and falsification remain open.

## Exact geometric reduction

On the source line for `N=1`, write

```text
w(v) = 3/2 + exp(5*pi*i/4) * v.
```

For `s=1/2+iy` and `w(v) != 0`, prove the exact norm identity

```text
norm (w(v) ^ (-s))
  = norm(w(v))^(-1/2) * exp(y * arg(w(v))).
```

The source line has `arg(w(v))>=0` for `v<=0` and `arg(w(v))<=0` for `v>=0`. Consequently the
power norm is maximized at `y=10` on the negative half-line and at `y=13/2` on the positive
half-line. All other factors in the line-integrand norm are independent of `y`.

Compile those facts as pointwise endpoint domination theorems and then as two half-line integral
bounds. The precise helper names may change, but the endpoint and inequality directions may not.

## Fixed success target

The first fixed producer is a uniform raw-integral norm bound:

```text
forall y, 13/2 <= y -> y <= 10 ->
  norm (deBruijnNewmanRiemannSiegelRawIntegral 1 (1/2+iy)) <= 3/5.
```

A permitted sufficient decomposition is

```text
negative endpoint half-line integral <= 1/10,
positive endpoint half-line integral <= 1/2.
```

The second fixed producer is the prefactor phase margin:

```text
forall y, 13/2 <= y -> y <= 10 ->
  (9/10) * norm (deBruijnNewmanRiemannSiegelPrefactor 1 (1/2+iy))
    < abs (Re (deBruijnNewmanRiemannSiegelPrefactor 1 (1/2+iy))).
```

These two outputs must compose through the exact identity
`R_(0,1)=prefactor*rawIntegral` to the already registered literal declaration

```text
HeightTenRiemannSiegelOneRemainderMargin.
```

Full success additionally requires the existing consumers to become unconditional:

```lean
theorem riemannZeta_criticalLine_ne_zero_thirteenHalves_ten
    {y : Real} (hy0 : 13 / 2 <= y) (hy1 : y <= 10) :
    riemannZeta ((1 / 2 : Complex) + (y : Complex) * Complex.I) != 0

theorem speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten
    {y : Real} (hy0 : 13 / 2 <= y) (hy1 : y <= 10) :
    (speiserZetaDerivRatio
      ((1 / 2 : Complex) + (y : Complex) * Complex.I)).re < 0
```

Lean syntax may use `\u2260` in the declarations; the mathematical statements may not be weakened.

## Navigation and proof boundary

Navigation-only quadrature found endpoint-split absolute integrals near `0.0951` and `0.4525`,
and a prefactor real-to-norm ratio above `0.925` on the target interval. These observations select
the deliberately wider rational targets `1/10`, `1/2`, and `9/10`; no decimal, quadrature result,
external zero table, or floating-point boolean is a premise.

The proof-producing route may split each endpoint integral into an analytic tail and a compact
rational interval cover. The prefactor phase may be bounded through a source-aligned Gamma phase
formula, a proved Taylor/Stirling enclosure, or an equivalent exact real-imaginary enclosure.
Every compact computation must reduce to kernel-checked rational inequalities.

Generic principal-argument lemmas, endpoint monotonicity, an abstract integral consumer, one
half-line bound, or a theorem conditional on either fixed producer are meaningful partial
progress only. They do not close this subattack.

## Failure and stopping rule

If Lean proves one of the frozen rational margins false, record the counter-bound and revisit the
constant only when the source-scale conclusion remains capable of proving the literal remainder
margin. Do not drift into best-constant optimization.

Stop this local subattack only after full success, a rigorous falsification of the phase-norm
route at the required scale, or an exact proof that a required Gamma or improper-integral theorem
is unavailable in the current trusted source boundary. A local stop returns to graph-ranked
historical route selection and never pauses the parent campaign or global RH Goal.

## Claim and axiom boundary

- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option;
- every named output must compile and pass exact TargetChecks;
- expected selected axiom frontier: `propext`, `Classical.choice`, and `Quot.sound`;
- navigation values and external finite-zero data are not premises;
- full success closes only the right-high vertical zone of the height-ten boundary;
- the other vertical zones, complete top, literal height-ten certificate, H12, and RH remain
  separate until their declarations compile.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed;
- `reasoning_effort`: not exposed;
- `budget`: no numerical quota under V4.1;
- `compaction_state`: current governance, source registry, active attempt ledger, DAG, and parent
  preregistration were re-read before selection;
- `global_goal`: active.
