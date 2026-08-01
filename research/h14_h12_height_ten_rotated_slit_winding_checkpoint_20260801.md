# H14 x H12 Height-Ten Rotated-Slit Winding Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-POSITIVE-IMAGINARY-RAY-WINDING-01`

Status: `ACTUAL_COUNT_CONSUMER_IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
LOCAL_SUBATTACK_STOP / CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Historical-route role

The source count argument needs equality of the zeta and zeta-derivative zero counts below
height ten, with multiplicity. Instead of enumerating both low zero sets or proving a
two-dimensional zero-free decomposition, this checkpoint isolates a one-dimensional sufficient
condition on the boundary image of the actual quotient `zeta'/zeta`.

## Compiled mathematical result

`LeanLab/Riemann/LevinsonMontgomeryHeightTenRotatedSlitWinding.lean` proves without `sorry`:

1. a generic principal-log endpoint formula for the integral of `g'/g` when one nonzero rotation
   of `g` stays in `Complex.slitPlane`;
2. actual horizontal and vertical endpoint formulas for `zeta'/zeta`, including all required
   nonvanishing and integrability facts;
3. exact cancellation of the four oriented edge increments under
   `SpeiserRotatedSlitBoundary c t`;
4. instantiation of the actual finite multiplicity-bearing argument principle on
   `[0,1/2] x [0,t]`;
5. identification of both compact strict-rectangle divisor sums with the existing source counts;
6. `speiserUpperLeftCounts_eq_of_rotatedSlitBoundary`; and
7. `levinsonMontgomeryHeightTenCertificate_of_positiveImaginaryRayAvoidance`.

For `c=I`, the excluded slit for the unrotated quotient is the positive imaginary ray.

## Exact limitation

The theorem `SpeiserRotatedSlitBoundary I 10` is not proved. Thus this checkpoint closes the
consumer from a boundary-ray certificate, not the unconditional height-ten count equality.
Navigation-only sampling that motivated the ray choice is not a theorem premise.

The compact-middle top sign, full `LevinsonMontgomeryHeightTenCertificate`, CountDichotomy,
Speiser equivalence, H12, and RH remain open.

## Local audit

- The new module builds successfully as `8742/8742` jobs.
- The module, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and `LeanLab.lean` pass
  `-DwarningAsError=true`.
- Exact statement witnesses compile for boundary cancellation, count equality, and the
  height-ten constructor.
- Four selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The project Lean-source scan finds no `sorry`, `admit`, or `native_decide`.
- The changed Lean files contain no relaxed resource option, custom axiom, `opaque`, or `unsafe`
  declaration.
- `git diff --check` passes.
- Full `lake build` passes `8826/8826` jobs.

## Next producers

1. Decompose `SpeiserRotatedSlitBoundary I 10` into four exact ray-avoidance edge targets and
   discharge analytically forced edges before adding finite interval certificates.
2. Continue the independent compact-middle producer for `SpeiserStrictNegativeHorizontal 10`.
3. Compose both producers into `levinsonMontgomeryHeightTenCertificate_actual`.

The global RH Goal and parent campaign remain active.

## Public implementation

- Commit `8ec5dfba37d050dbcb0ac9889b3bc95f9cbf2253` passed Lean Action run
  `30708752970`, build job `91392334217`, in `2m51s`.
- The new module, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and `LeanLab.lean` are
  frozen by Git blob in
  `research/h14_h12_height_ten_rotated_slit_winding_evidence_20260801.md`.
- Documentation-only evidence commit `4a7606b1d3b4a49428fbe16a8346ba2f3b6fd65d` passed Lean
  Action run `30708950255`, build job `91392860631`, in `1m51s`; all five frozen Lean blobs are
  unchanged.
