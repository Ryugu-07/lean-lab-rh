# H14 x H12 Height-Ten Boundary-Ray Producer Checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-BOUNDARY-RAY-PRODUCER-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / LOCAL_SUBATTACK_STOP /
PARENT_CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Result

The subattack closes the complete real bottom edge of the height-ten rotated-slit condition and
reduces the remaining boundary producer to exactly two vertical ray-avoidance statements plus the
independently tracked strict-negative top target.

The compiled actual-function outputs are:

- `riemannZeta_realSegment_re_neg`;
- `deriv_riemannZeta_realSegment_re_neg`;
- `speiserZetaDerivRatio_realSegment_re_pos`;
- `speiserBottom_mem_rotatedSlit`;
- `SpeiserPositiveImaginaryRayVerticalBoundary`;
- `SpeiserStrictNegativeHorizontal.toRotatedSlitBoundary_of_vertical`;
- `levinsonMontgomeryHeightTenCertificate_of_verticalRayAvoidance`.

For every real `sigma` with `0<=sigma<=1/2`, Lean proves

`Re zeta(sigma)<0`, `Re zeta'(sigma)<0`, and `Re(zeta'(sigma)/zeta(sigma))>0`.

Consequently `I*(zeta'/zeta)` belongs to `Complex.slitPlane` on the complete bottom edge. Given
`SpeiserStrictNegativeHorizontal t`, the top edge also belongs to the same slit plane. Only the
left and right vertical clauses in `SpeiserPositiveImaginaryRayVerticalBoundary t` remain before
the generic rotated-slit consumer applies.

## Proof mechanism

At cutoff `N=1`, the one-correction Euler--Maclaurin finite centers simplify exactly to

`1/2 - 1/(1-sigma)` and `-1/(1-sigma)^2`.

The corresponding errors simplify to

`sigma/8` and `(3*sigma+1)/(8*(sigma+1))`.

These symbolic expressions have strict margins throughout `0<sigma<=1/2`. At `sigma=0`, the
proof uses the exact library formulas for `zeta(0)` and `zeta'(0)`. Conjugation identities then
show that zeta and its derivative are real on the real axis, so their two strict negative signs
give a strictly positive quotient.

## Natural-domain repair

The inherited `zetaAbelContinuationDomain` wrapper only exposes `Re(s)>1/10`, which excludes part
of the intended bottom segment. The project already contained the actual finite-tail identity
`riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos` for `Re(s)>0`. This loop extends the
finite-tail, Euler--Maclaurin value, derivative, and norm-bound interfaces to that natural positive
real-part domain before instantiating them at `N=1`.

This is a domain-interface repair backed by the existing actual-zeta theorem, not an analytic
continuation assumption.

## Audit

- Preregistration commit `87d3d144e237667a8fe54d4d17877ee0767f0ac3` passed Lean Action
  run `30709645182`, build job `91394727872`, in `1m42s`.
- The new module passes standalone warning-as-error at `8743/8743`.
- Targets, TargetChecks, AxiomsAudit, and `LeanLab.lean` pass warning-as-error.
- Selected axiom prints are exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Focused forbidden-token scans and `git diff --check` are clean.
- The full local build passes `8827/8827`.
- No theorem in this checkpoint uses `sorry`, `admit`, `native_decide`, a custom axiom, `opaque`,
  `unsafe`, or a relaxed resource option.

## Strict limit

This checkpoint does not prove either vertical ray-avoidance clause. It also does not prove the
compact-middle portion of `SpeiserStrictNegativeHorizontal 10`. Therefore it does not prove
`SpeiserRotatedSlitBoundary I 10`, the literal height-ten certificate, CountDichotomy, Speiser
equivalence, H12, or RH.

The exact remaining boundary producers are:

1. `I*(zeta'/zeta)(iy)` remains in `Complex.slitPlane` for `0<=y<=10`;
2. `I*(zeta'/zeta)(1/2+iy)` remains in `Complex.slitPlane` for `0<=y<=10`;
3. the compact-middle top strict sign already isolated by the boundary-neighborhood reduction.

## Historical-route interpretation

This result reuses the Johansson-style Euler--Maclaurin evaluator inside the
Levinson--Montgomery/argument-principle route. Its value is diagnostic: it removes two boundary
obligations and makes the surviving source dependencies explicit. It is not a claim that this
historical route is complete or uniquely preferred.

Historical-route omission search remains the current priority. New conjectures may still be
proposed, falsified, and formally tested at any time when they offer a higher-value edge in the
proof graph.

## Publication state

The production implementation is frozen at commit
`82c2e991a22d0a21db318f9023941c7b2a764ff2`. Lean Action run `30711032719`, build job
`91398404697`, passed in `17m17s`.

Seven exact Lean blobs are recorded in the docs-only immutable-evidence file. Public CI for that
evidence record passed at commit `b679dd8d7b73f282f68071842af3cd82f9c99825`: Lean Action run
`30711720009`, build job `91400251532`, in `1m44s`. All seven blob identities match the public
implementation commit.

This local subattack stops successfully. Both vertical producers, the compact-middle top sign,
the parent campaign, and the global RH Goal remain active.
