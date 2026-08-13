# H12 Height-Ten Left Low Pole-Cancelled Preregistration

Date: 2026-08-13

Campaign: `PROOF-ATTEMPT-20260813-H12-HEIGHT-TEN-LEFT-LOW-POLE-CANCELLED-01`

Parent: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Primary mode: `DISCOVERY / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / DOCS-ONLY PUBLIC GATE PENDING / GLOBAL_GOAL_ACTIVE`

## Route decision

The middle phase interval `[6,13/2]` is closed. The remaining frozen left producer is

```text
Re(zeta'(iy)/zeta(iy)) > 0 for 0<y<=6.
```

The current reflected evaluator loses useful information as `y` tends to zero because it
approximates `zeta(1-iy)` and its derivative separately near the pole. This is a defect of the
chosen representation, not a singularity of the actual quotient at `iy`: the value at `y=0`
is already compiled and strictly positive.

The direct Hardy--Littlewood eta evaluator was compared and rejected for this endpoint. Its
available derivative error theorem requires a Cauchy radius `0<r<Re(s)`, which cannot be
instantiated on the imaginary axis. Pure continuity was also rejected as the primary endpoint:
it gives an unknown positive radius that cannot join a rational finite subcover.

## Pole cancellation

Let

```text
F(w) = (w-1) zeta(w),       w = 1-iy.
```

Then `F` is entire and `F(1)=1`. For `y>0`, logarithmic differentiation and the functional
equation give

```text
zeta'(iy)/zeta(iy)
  = -F'(1-iy)/F(1-iy)
    - 1/(iy-1) + log(pi)
    - (digamma(1+iy/2) + digamma(3/2-iy/2))/2.
```

The `1/(w-1)` pole has cancelled exactly. Multiplying the second-corrected Euler--Maclaurin
value ball by `w-1` changes its error from `ez` to `y*ez`; differentiating the product changes
the derivative error to `ez+y*ed`. This is the proposed low-height omission repair.

## Fixed mathematical endpoint

First prove reusable no-premise interfaces for the pole-removed value, derivative, quotient,
and regular reflected phase. Then prove the frozen rational theorem

```lean
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_oneQuarter
    {y : Real} (hy0 : 0 <= y) (hy1 : y <= 1 / 4) :
    0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re
```

The endpoint `y=0` may use the existing exact theorem. Every `0<y<=1/4` claim must use the
pole-cancelled evaluator with exact rational centers and interval transport. The split point
`1/4` is frozen for the first attempt.

Also prove a reduction theorem joining this interval to any future producer on `[1/4,6]`.

## Acceptance and falsification

- `full_success`: the displayed `[0,1/4]` theorem, a `[1/4,6]` reduction, exact TargetChecks,
  selected axiom prints, full local build, public implementation CI, immutable evidence, and a
  closure receipt all pass.
- `meaningful_partial`: the pole-cancelled identity and error ball compile, and Lean proves an
  explicit positive-real interval `[0,a]` for a rational `0<a<1/4`; the failed `1/4` margin is
  recorded exactly.
- `mechanism_falsified`: a kernel-checked bound shows that the selected Euler--Maclaurin cutoff
  and center family cannot separate the real component even on the first rational cell. Record
  the exact lost margin and compare a direct Taylor expansion of the actual quotient.

Navigation values, sampled grids, external zero tables, and unknown continuity radii are not
premises. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, opaque proof
escape, or relaxed resource option is permitted.

## Claim boundary

Closing `[0,1/4]` does not close `(0,6]`, the complete left edge, the other height-ten boundary
producers, the height-ten certificate, H12, or RH. The parent campaigns and global RH Goal stay
active regardless of the local outcome.
