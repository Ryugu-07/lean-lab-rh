# H14 x H12 Height-Ten Boundary-Ray Producer Preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-BOUNDARY-RAY-PRODUCER-01`

Primary mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Route selection

The closed rotated-slit consumer reduces the multiplicity-count equality to
`SpeiserRotatedSlitBoundary I 10`. Its four edge clauses were audited separately.

1. The top clause is already implied by the independent source target
   `SpeiserStrictNegativeHorizontal 10`, because `(I*q).im = q.re` for `q=zeta'/zeta`.
2. The bottom quotient is real by the compiled conjugation identities for zeta and its
   derivative. It therefore suffices to prove that the quotient is nonzero.
3. The left and right vertical clauses remain genuine positive-imaginary-ray avoidance
   statements on compact low-height intervals.

The existing one-correction Euler--Maclaurin evaluator unexpectedly makes the bottom clause
analytic rather than computationally large. With cutoff `N=1`, navigation and exact symbolic
simplification give the real centers

`1/2 - 1/(1-sigma)` and `-1/(1-sigma)^2`

for zeta and its derivative. The already compiled remainder formulas have strict margins on
`0 < sigma <= 1/2`; the endpoint `sigma=0` has exact Mathlib value and derivative formulas.
No sampled decimal is a theorem premise.

Select the unconditional bottom proof plus an exact reduction of the complete boundary producer
to only the two vertical clauses and the already required top-sign target. This materially removes
two of the four boundary obligations.

## Exact mathematical targets

For every real `sigma` with `0 <= sigma <= 1/2`, prove

`Re zeta(sigma) < 0`,

`Re zeta'(sigma) < 0`,

and hence

`Re (zeta'(sigma)/zeta(sigma)) > 0`.

Conjugation then makes the quotient real and nonzero, so `I * zeta'/zeta` belongs to the principal
log slit plane on the complete bottom edge.

Define the remaining vertical certificate to assert the same slit-plane membership on
`s=iy` and `s=1/2+iy` for `0 <= y <= t`. Prove that this vertical certificate and
`SpeiserStrictNegativeHorizontal t` imply `SpeiserRotatedSlitBoundary I t`. At height ten, the
same two inputs must construct the literal `LevinsonMontgomeryHeightTenCertificate`.

## Proposed Lean outputs

Production names may change only for elaboration or namespace reasons; statements may not be
weakened.

```lean
theorem riemannZeta_realSegment_re_neg
    {sigma : Real} (hsigma : sigma ∈ Set.Icc (0 : Real) (1 / 2)) :
    (riemannZeta (sigma : Complex)).re < 0

theorem deriv_riemannZeta_realSegment_re_neg
    {sigma : Real} (hsigma : sigma ∈ Set.Icc (0 : Real) (1 / 2)) :
    (deriv riemannZeta (sigma : Complex)).re < 0

theorem speiserZetaDerivRatio_realSegment_re_pos
    {sigma : Real} (hsigma : sigma ∈ Set.Icc (0 : Real) (1 / 2)) :
    0 < (speiserZetaDerivRatio (sigma : Complex)).re

theorem speiserBottom_mem_rotatedSlit
    (sigma : Real) (hsigma : sigma ∈ Set.Icc (0 : Real) (1 / 2)) :
    Complex.I * speiserZetaDerivRatio (sigma : Complex) ∈ Complex.slitPlane

def SpeiserPositiveImaginaryRayVerticalBoundary (t : Real) : Prop :=
  (∀ y : Real, y ∈ Set.Icc (0 : Real) t ->
    Complex.I * speiserZetaDerivRatio ((y : Complex) * Complex.I) ∈
      Complex.slitPlane) /\
  (∀ y : Real, y ∈ Set.Icc (0 : Real) t ->
    Complex.I * speiserZetaDerivRatio
      ((1 / 2 : Complex) + y * Complex.I) ∈ Complex.slitPlane)

theorem SpeiserStrictNegativeHorizontal.toRotatedSlitBoundary_of_vertical
    {t : Real} (hsign : SpeiserStrictNegativeHorizontal t)
    (hvertical : SpeiserPositiveImaginaryRayVerticalBoundary t) :
    SpeiserRotatedSlitBoundary Complex.I t

theorem levinsonMontgomeryHeightTenCertificate_of_verticalRayAvoidance
    (hsign : SpeiserStrictNegativeHorizontal 10)
    (hvertical : SpeiserPositiveImaginaryRayVerticalBoundary 10) :
    LevinsonMontgomeryHeightTenCertificate
```

## Success criteria

Full subattack success requires all of the following:

- exact `N=1` Euler--Maclaurin center identities for zeta and its derivative;
- strict symbolic error margins on the complete open real segment `0 < sigma <= 1/2`;
- exact endpoint handling at `sigma=0`;
- actual-function real-part negativity and quotient positivity, not finite-center proxies;
- unconditional bottom slit-plane membership;
- derivation of top slit-plane membership from `SpeiserStrictNegativeHorizontal t`;
- exact assembly reducing `SpeiserRotatedSlitBoundary I t` to the two vertical clauses;
- the height-ten certificate constructor from top sign and vertical avoidance;
- exact TargetChecks and standard-only axiom prints;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option.

An abstract edge decomposition without the unconditional actual-zeta bottom theorem is not full
success.

## Falsification and stopping criteria

- If the exact `N=1` center simplification differs from the formulas above, recompute the literal
  finite formula before choosing any larger cutoff.
- If either compiled remainder can reach zero anywhere on `0 < sigma <= 1/2`, record the exact
  worst symbolic endpoint and test `N=2`; do not assert a sign from navigation.
- If conjugation proves realness but the quotient sign cannot be recovered from the two strict
  negative real parts, record the exact complex-division mismatch.
- If the bottom closes but top-to-slit or vertical assembly fails because of a convention mismatch,
  preserve the bottom theorem and record the precise `Complex.slitPlane` orientation defect.
- Stop this local subattack after the unconditional bottom and exact two-vertical reduction are
  proved or after the `N=1/N=2` mechanism is rigorously falsified. Local stop never pauses the
  parent campaign or global RH Goal.

## Known obstacles and nearest prior work

- `LevinsonMontgomeryEulerMaclaurin.lean` already proves actual value and derivative error balls,
  but it was previously used at the reflected height-ten endpoint with `N=30`, not on the real
  bottom with `N=1`.
- `BaezDuarteZetaRatio.lean` and `LevinsonMontgomeryJensenTopZeroCount.lean` provide the exact
  conjugation identities for zeta and its derivative.
- `LevinsonMontgomeryHeightTenRotatedSlitWinding.lean` consumes the complete four-edge boundary
  condition but does not prove any edge unconditionally.
- The two low vertical edges still require analytic identities or proof-producing interval
  certificates after this subattack; they are not silently included in the bottom proof.

## DAG position and assumption frontier

Input nodes:

- `H14-H12-HEIGHT-TEN-COUNT-WINDING-CONSUMER-01` (closed);
- one-correction actual-zeta Euler--Maclaurin value and derivative errors (closed);
- zeta and zeta-derivative conjugation (closed);
- `H14-H12-HEIGHT-TEN-TOP-01` (open, reused rather than duplicated).

Output nodes:

- `H14-H12-HEIGHT-TEN-BOTTOM-RAY-01`;
- `H14-H12-HEIGHT-TEN-VERTICAL-RAY-REDUCTION-01`.

The left and right vertical producer, compact-middle top sign, full height-ten certificate,
CountDichotomy, Speiser equivalence, H12, and RH remain open unless their exact Lean declarations
compile.

Assumption-frontier expectation for selected theorems: only `propext`, `Classical.choice`, and
`Quot.sound`.

## Material difference from the preceding subattack

The preceding subattack proved a generic consumer from a four-edge slit-plane hypothesis. This
attack proves one edge unconditionally from actual-function estimates, eliminates the top edge as
a separate hypothesis by reusing the source sign target, and leaves exactly two vertical
one-dimensional producers. It is therefore production work, not another reformulation of the
same four-edge assumption.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from the active Goal context; current governance, route ruling,
  HANDOFF, Targets, TargetChecks, attempts, hard-gap DAG, rotated-slit module, conjugation modules,
  and Euler--Maclaurin evaluator were re-read before selection.
- `global_goal`: active.
