# H14 x H12 Height-Ten Rotated-Slit Winding Closure Receipt

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Closed subattack: `HEIGHT-TEN-POSITIVE-IMAGINARY-RAY-WINDING-01`

Closed DAG node: `H14-H12-HEIGHT-TEN-COUNT-WINDING-CONSUMER-01`

Status: `LOCAL_SUBATTACK_STOP / PARENT_CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Public chain

1. Preregistration commit `a557c9bf06b970a75e09d66c8a18cf9342b9d7db` passed Lean Action
   run `30707509879`, build job `91389064687`, in `1m44s`.
2. Implementation commit `8ec5dfba37d050dbcb0ac9889b3bc95f9cbf2253` passed Lean Action
   run `30708752970`, build job `91392334217`, in `2m51s`.
3. Immutable-evidence commit `4a7606b1d3b4a49428fbe16a8346ba2f3b6fd65d` passed Lean Action
   run `30708950255`, build job `91392860631`, in `1m51s`.
4. The five frozen Lean blobs are identical between the implementation and evidence commits.

## Closed statement

For arbitrary `c : Complex` and `t : Real`, `SpeiserRotatedSlitBoundary c t` implies exact
equality of the existing multiplicity-bearing zeta and zeta-derivative upper-left zero counts.
The proof uses one principal-log branch around the actual quotient boundary and the existing
finite argument principle.

At height ten, `SpeiserRotatedSlitBoundary Complex.I 10` together with
`SpeiserStrictNegativeHorizontal 10` constructs the literal
`LevinsonMontgomeryHeightTenCertificate`.

## Open successor

The unconditional proposition `SpeiserRotatedSlitBoundary Complex.I 10` remains open and should
be split into bottom, top, left, and right boundary-ray producers. The compact-middle top-sign
producer is also open. Consequently the parent certificate campaign, CountDichotomy, Speiser
equivalence, H12, RH, and the global Goal remain active.
