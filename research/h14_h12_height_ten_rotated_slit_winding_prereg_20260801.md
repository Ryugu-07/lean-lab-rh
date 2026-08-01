# H14 x H12 Height-Ten Rotated-Slit Winding Preregistration

Date: 2026-08-01

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-POSITIVE-IMAGINARY-RAY-WINDING-01`

Primary mode: `PROOF-ATTEMPT`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Route selection

The two live producers for `LevinsonMontgomeryHeightTenCertificate` were compared again after
the boundary-neighborhood checkpoint.

1. A quantitative Euler--Maclaurin/Taylor cover of the remaining height-ten top middle would
   close only the strict-horizontal conjunct. It requires new variation estimates or many
   generated finite centers.
2. A direct two-dimensional low-zero box cover would separately exclude every zeta and
   zeta-derivative zero in the open rectangle.
3. A one-dimensional quotient-winding certificate can instead prove the required equality of
   the two multiplicity counts without excluding either divisor in the interior. The existing
   finite argument principle already identifies the count difference with the boundary integral
   of the logarithmic derivative of `zeta'/zeta`.

Select (3). This is not another continuity neighborhood and not numerical constant optimization.
It attacks the independent count conjunct and can later reuse the strict-negative top conjunct.

Navigation-only high-precision sampling found that the actual quotient boundary at height ten
avoids the positive imaginary ray and has zero net winding. The smallest sampled quotient norm
was about `0.188`; the only sampled real-part crossings on the two vertical sides occurred near
heights `6.19` and `6.29`, where the imaginary parts were below `-0.19`. None of these decimal
observations is a theorem premise or a certificate.

## Exact mathematical target

Write

`q(s) = zeta'(s) / zeta(s)`.

For a nonzero complex rotation `c`, suppose `c * q(s)` lies in the principal-log slit plane on
all four sides of

`R_t = {s : 0 <= Re(s) <= 1/2, 0 <= Im(s) <= t}`,

with `t > 0`. Then the same holomorphic branch `Log(c*q)` is available on every boundary side.
The four logarithmic-derivative integrals are endpoint differences of that single branch, so
their oriented sum is exactly zero. The finite multiplicity-bearing argument principle then
forces

`speiserUpperLeftDerivZeroCount t = speiserUpperLeftZetaZeroCount t`.

At `t=10`, take `c=I`. The excluded standard slit is then the positive imaginary ray for `q`.
Combining this count equality with `SpeiserStrictNegativeHorizontal 10` must construct the literal
`LevinsonMontgomeryHeightTenCertificate`.

## Proposed Lean outputs

Production names may change only to resolve namespace or elaboration issues; the statements may
not be weakened.

```lean
def SpeiserRotatedSlitBoundary (c : Complex) (t : Real) : Prop :=
  0 < t ∧ c ≠ 0 ∧
    (∀ sigma ∈ Set.Icc (0 : Real) (1 / 2),
      c * speiserZetaDerivRatio sigma ∈ Complex.slitPlane) ∧
    (∀ sigma ∈ Set.Icc (0 : Real) (1 / 2),
      c * speiserZetaDerivRatio (sigma + t * Complex.I) ∈ Complex.slitPlane) ∧
    (∀ y ∈ Set.Icc (0 : Real) t,
      c * speiserZetaDerivRatio (y * Complex.I) ∈ Complex.slitPlane) ∧
    (∀ y ∈ Set.Icc (0 : Real) t,
      c * speiserZetaDerivRatio ((1 / 2 : Real) + y * Complex.I) ∈
        Complex.slitPlane)

theorem rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_rotatedSlit
    {c : Complex} {t : Real} (h : SpeiserRotatedSlitBoundary c t) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 (1 / 2) 0 t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 (1 / 2) 0 t = 0

theorem speiserUpperLeftCounts_eq_of_rotatedSlitBoundary
    {c : Complex} {t : Real} (h : SpeiserRotatedSlitBoundary c t) :
    speiserUpperLeftDerivZeroCount t = speiserUpperLeftZetaZeroCount t

theorem levinsonMontgomeryHeightTenCertificate_of_positiveImaginaryRayAvoidance
    (hsign : SpeiserStrictNegativeHorizontal 10)
    (hboundary : SpeiserRotatedSlitBoundary Complex.I 10) :
    LevinsonMontgomeryHeightTenCertificate
```

## Success criteria

Full subattack success requires all of the following:

- a generic rotated-slit endpoint formula for a differentiable nonvanishing path;
- exact four-side telescoping for the actual quotient and the project rectangle orientation;
- an actual finite-divisor argument-principle instantiation on `[0,1/2] x [0,t]`;
- exact identification of both compact divisor sums with the existing global upper-left natural
  multiplicity counts;
- the height-ten certificate constructor above;
- exact TargetChecks and standard-only axiom prints;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option.

This subattack does not require the unconditional proof of
`SpeiserRotatedSlitBoundary Complex.I 10`. That is the next finite boundary producer. A theorem
assuming the count equality itself, assuming zero winding, or assuming interior zero-freeness is
not success.

## Falsification and stopping criteria

- If a kernel-checked counterexample shows that a single slit branch on all four sides does not
  telescope under `rectangleBoundaryIntegral` orientation, stop and record the orientation
  defect.
- If the argument-principle divisor sums cannot be identified with the existing strict open-left
  counts at bottom height zero, record the exact convention mismatch; do not alter the counts.
- If the positive-imaginary-ray choice is numerically falsified, retain the generic rotated-slit
  theorem and rerank a different rationally certifiable rotation. Numerical survival is never a
  proof.
- If only a generic path-log lemma compiles without the actual count consumer, classify the loop
  as infrastructure partial, not closure of the count obstruction.

## Known obstacles and nearest prior work

- Mathlib has the principal complex logarithm and slit-plane derivative theorem, but the local
  audit found no packaged winding number or homotopy-index API for this application.
- `LevinsonMontgomeryLeftHalfPlaneWinding.lean` proves one-side endpoint formulas when the quotient
  remains in the strict left half-plane. It does not coordinate one branch around four sides or
  connect a low rectangle to the actual counts.
- `LevinsonMontgomeryFiniteArgumentPrinciple.lean` already provides the exact multiplicity-bearing
  rectangle count. This attack must reuse it rather than create a second divisor convention.
- The bottom starts at height zero, so the existing positive-bottom split theorem cannot be used
  verbatim. The strict-rectangle support must instead be identified directly with the source
  finsets; every source point already has positive imaginary part.

## DAG position and assumption frontier

Input nodes:

- `H12-LM-FINITE-ARGUMENT-PRINCIPLE-01` (closed);
- `H12-LEFT-HALF-PLANE-WINDING-01` (closed infrastructure);
- actual quotient differentiability and horizontal/vertical integrability APIs (closed);
- `H14-H12-HEIGHT-TEN-TOP-01` (still open, but reusable by the final constructor).

Output node:

- `H14-H12-HEIGHT-TEN-COUNT-WINDING-CONSUMER-01`.

The unconditional boundary certificate, full height-ten certificate, count dichotomy, Speiser
equivalence, H12, and RH remain open unless their exact Lean declarations compile.

Assumption-frontier expectation for selected theorems: only `propext`, `Classical.choice`, and
`Quot.sound`.

## Material novelty of this attack angle

The nearest failed/unfinished producer proposed either a two-dimensional zero-free box cover or
separate low-zero enumeration. This attack uses a different invariant: the quotient may have
zeros and poles in the interior, but a single branch cut missed by its one-dimensional boundary
image forces their total multiplicities to agree. It therefore targets exactly the count
difference and can be certified by boundary boxes alone.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: inherited summary; current governance, route ruling, HANDOFF, Targets,
  TargetChecks, active attempts, hard-gap DAG, certificate source, finite argument principle,
  and winding modules were re-read before selection.
- `global_goal`: active.
