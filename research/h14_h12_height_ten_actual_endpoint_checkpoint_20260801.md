# H14 x H12 Height-Ten Actual Endpoint Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Status: `MEANINGFUL_PARTIAL_IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_PENDING /
CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Historical-route role

This checkpoint closes one fixed producer in the historical Levinson--Montgomery height-ten
argument. It combines the already certified thirty-term Johansson-style Euler--Maclaurin center
with analytic remainder and reflection estimates. The target was fixed by the historical proof
dependency; the work is not an open-ended optimization of numerical constants.

Historical-route omission search remains the default selection discipline. Direct RH attacks,
unresolved intermediate propositions, and new conjecture tests remain open at every selection
point.

## Compiled mathematical result

`LeanLab/Riemann/LevinsonMontgomeryHeightTenEndpoint.lean` proves without `sorry`:

1. alternating rational arctangent bounds and a Machin-formula certificate
   `Real.pi < 3142/1000`;
2. `Real.log Real.pi < 229/200` and the exact logarithmic inequalities needed by the reflected
   archimedean term;
3. a reflected archimedean upper bound below `-11/25` at `s=1/2+10i`;
4. actual Euler--Maclaurin value error below `13/250` at `w=1/2-10i`;
5. actual Euler--Maclaurin derivative error below `11/50` there;
6. tighter finite value, derivative, and cross bounds that preserve a strict margin after error
   propagation; and
7. the theorem `speiserStrictNegativePoint_heightTenEndpoint`:

```lean
riemannZeta heightTenEndpoint ≠ 0 /\
  deriv riemannZeta heightTenEndpoint ≠ 0 /\
  (speiserZetaDerivRatio heightTenEndpoint).re < 0
```

Here `heightTenEndpoint = 1/2 + 10i`. This final statement concerns Mathlib's actual
`riemannZeta` and derivative, rather than a finite approximation.

## Claim boundary

The theorem is about one point only. It proves neither a positive-width sigma interval nor a
finite horizontal cover. It also does not enumerate the zeros of zeta and its derivative below
height ten with multiplicity.

Therefore no complete `LevinsonMontgomeryHeightTenCertificate`, CountDichotomy, Speiser
equivalence, H12, or RH is claimed.

## Local audit

- The new module builds successfully as `8740/8740` jobs.
- The new module, `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` pass
  `-DwarningAsError=true`.
- Seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The project Lean-source scan finds no `sorry`, `admit`, or `native_decide`.
- The changed Lean files contain no `maxHeartbeats`, `maxRecDepth`, `axiom`, `opaque`, or
  `unsafe` declaration.
- `git diff --check` passes.
- Full `lake build` passes `8824/8824` jobs.

## Next producers

1. Prove explicit sigma-variation estimates and kernel-check a finite rational subcover of a
   positive-width portion of `0 <= sigma <= 1/2`.
2. Independently construct the actual multiplicity-bearing low-zero count certificate.
3. Compose the horizontal sign and low-zero count producers into
   `levinsonMontgomeryHeightTenCertificate_actual`.

The global RH Goal and this campaign remain active.

## Public implementation

- Commit `3ed50eed1abefea20a810d39ce3ce89f2f61fe3a` passed Lean Action run
  `30668355865`, build job `91280491604`, in `2m50s`.
- The endpoint module, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and
  `LeanLab.lean` are frozen by Git blob in
  `research/h14_h12_height_ten_actual_endpoint_evidence_20260801.md`.
- The documentation-only immutable-evidence commit and its public CI are pending.
