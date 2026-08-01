# H14 x H12 Height-Ten Complete-Boundary Structural Checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Status: `MEANINGFUL_PARTIAL / SUBATTACK_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Historical question

Levinson and Montgomery describe a direct low-height consideration of
`zeta'(it)/zeta(it)` in the proof of their Theorem 9. The current attack reconstructs enough of
their completed-zeta calculation to determine whether the same mechanism proves the project's
two open vertical ray-avoidance clauses, rather than treating the reported transition as an
external numerical fact.

## Compiled results

The no-sorry module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenCompleteBoundary.lean` proves:

1. `logDeriv_riemannZeta_re_eq_archimedean_on_criticalLine`: at every critical-line point where
   actual zeta is nonzero, the real part of its logarithmic derivative is exactly the
   Levinson--Montgomery archimedean term.
2. `levinsonMontgomery_equation_two_one_of_im_pos`: the exact paired-zero formula holds for every
   point with positive imaginary part.
3. `logDeriv_riemannZeta_re_le_archimedean_on_imaginaryAxis`: on `s=iy`, the paired-zero term is
   nonpositive, yielding an exact upper bound by the archimedean term.
4. `levinsonMontgomeryArchimedean_criticalLine_neg_of_thirteenHalves_le`: one digamma shift,
   Stieltjes' remainder, and proof-producing rational `log` and `pi` bounds make the critical-line
   archimedean term strictly negative for `y>=13/2`.
5. `speiserZetaDerivRatio_rightVertical_re_neg_of_thirteenHalves_le`: the proposed right-high
   vertical sign follows conditional only on actual zeta nonvanishing.

The threshold `13/2` is inherited from the preregistered rational partition and is not asserted
to be optimal.

## Route split

The critical line removes the paired-zero contribution exactly, so its high zone is controlled
by Gamma/digamma structure once nonvanishing is known. On the imaginary axis the paired-zero
contribution remains present. Its nonpositivity gives useful direction but does not turn the
left high zone into the same Gamma-only calculation.

This is a genuine structural split in the historical reconstruction. The left edge must retain
a direct actual-zeta evaluator or obtain a sharper theorem about the paired-zero sum; copying the
right-edge argument would hide the unresolved term.

## Exact open producers

- actual zeta nonvanishing on the required critical-line low-height intervals, including
  `[13/2,10]`;
- actual signs and nonvanishing for the remaining five proposed vertical zones;
- the complete top condition `SpeiserStrictNegativeHorizontal 10`;
- `SpeiserRotatedSlitBoundary I 10`;
- the literal `LevinsonMontgomeryHeightTenCertificate`.

The next shared backend should be a proof-producing finite low-height evaluator or uniform
interval cover. Navigation grids and external zero tables remain inadmissible as premises.

## Claim boundary

This checkpoint proves no unconditional complete vertical clause and no height-ten certificate.
It does not prove H12 or RH. It records a useful exact identity, one conditional right-edge zone,
and the reason the left edge requires different mathematics.

## Public gate

The docs-only preregistration commit `b5ce6a81db1c54e166efe62128e450ab59f185a2`
passed Lean Action run `30712326447`, build job `91401847586`, in `2m42s` before production
editing.

Frozen implementation commit `d3d975d3c4202a3d14f8ea2e931a400ea7ef65ff` passed Lean Action
run `30713362289`, build job `91404656086`, in `3m34s`. The five proof and registration blobs
are frozen in
`research/h14_h12_height_ten_complete_boundary_structural_evidence_20260802.md`.

Docs-only immutable-evidence commit `8b7cb43028e04917c510d96b0fe89050a1f7e947` passed Lean Action
run `30713557491`, build job `91405164201`, in `2m50s`; all five frozen Lean blobs are unchanged.
The complete-boundary subattack remains active.

## Local audit

- standalone module build: `8744/8744`;
- new module, Targets, TargetChecks, AxiomsAudit, and project entry: warning-as-error clean;
- selected axiom prints: only `propext`, `Classical.choice`, and `Quot.sound`;
- focused forbidden scan and `git diff --check`: empty;
- full build: `8828/8828`.

## Governance

- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed resource
  option;
- navigation decimals are not premises;
- expected selected axiom frontier: `propext`, `Classical.choice`, and `Quot.sound`;
- historical omission search remains the route-selection default;
- independent conjecture proposal, proof attempt, and falsification remain open;
- global RH Goal remains active.
