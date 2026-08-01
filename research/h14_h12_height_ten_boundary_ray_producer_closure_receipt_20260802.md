# H14 x H12 Height-Ten Boundary-Ray Producer Closure Receipt

Date: 2026-08-02

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Closed subattack: `HEIGHT-TEN-BOUNDARY-RAY-PRODUCER-01`

Closed DAG nodes: `H14-H12-HEIGHT-TEN-BOTTOM-RAY-01` and
`H14-H12-HEIGHT-TEN-VERTICAL-RAY-REDUCTION-01`

Status: `LOCAL_SUBATTACK_STOP / PARENT_CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Public chain

1. Preregistration commit `87d3d144e237667a8fe54d4d17877ee0767f0ac3` passed Lean Action
   run `30709645182`, build job `91394727872`, in `1m42s`.
2. Implementation commit `82c2e991a22d0a21db318f9023941c7b2a764ff2` passed Lean Action
   run `30711032719`, build job `91398404697`, in `17m17s`.
3. Immutable-evidence commit `b679dd8d7b73f282f68071842af3cd82f9c99825` passed Lean Action
   run `30711720009`, build job `91400251532`, in `1m44s`.
4. The seven frozen Lean blobs are identical between the implementation and evidence commits.

## Closed statements

For every real `sigma` with `0<=sigma<=1/2`, the actual values satisfy

`Re zeta(sigma)<0`, `Re zeta'(sigma)<0`, and `Re(zeta'(sigma)/zeta(sigma))>0`.

Therefore `I*(zeta'/zeta)` belongs to `Complex.slitPlane` on the complete bottom edge.

For arbitrary `t`, `SpeiserStrictNegativeHorizontal t` and
`SpeiserPositiveImaginaryRayVerticalBoundary t` construct
`SpeiserRotatedSlitBoundary I t`. At `t=10`, the same inputs construct the literal
`LevinsonMontgomeryHeightTenCertificate`.

## Open successors

`SpeiserPositiveImaginaryRayVerticalBoundary 10` remains open on both the left edge `s=iy` and
right edge `s=1/2+iy`. The compact-middle top sign also remains open. Consequently the literal
height-ten certificate, CountDichotomy, Speiser equivalence, H12, RH, and the persistent global
Goal remain active.

Stop only this local producer subattack. Rerank the right critical-line vertical edge, the left
imaginary-axis vertical edge, and the compact-middle top producer by historical-route value and
structural leverage. Historical omission search remains the current priority; independent
conjecture proposal and falsification remain open at all times.
