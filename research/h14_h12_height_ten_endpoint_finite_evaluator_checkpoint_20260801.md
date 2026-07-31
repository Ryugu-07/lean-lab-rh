# H14 x H12 Height-Ten Endpoint Finite Evaluator Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Status: `MEANINGFUL_PARTIAL_PUBLIC_IMPLEMENTATION_GREEN /
IMMUTABLE_EVIDENCE_CI_PENDING / CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Historical-route role

This checkpoint continues the finite-height input used on page 52 of Levinson--Montgomery through
Johansson-style Euler--Maclaurin evaluation. It is an omission-seeking reconstruction of a fixed
historical dependency, not a replacement for surveying other RH routes. Direct RH attacks and
new conjecture proposals remain open, but this producer has immediate graph value because the
compiled global count theorem already reduces to the height-ten certificate.

## Compiled mathematical result

`LeanLab/Riemann/LevinsonMontgomeryTranscendentalInterval.lean` now proves binary logarithm range
reduction and scaling-and-squaring error propagation. For the integers from one through thirty,
the selected logarithm ratios remain below the worst case near `0.164`; sixty-fourfold scaling and
a degree-16 Taylor center replace the earlier direct high-order exponential expansion.

`LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurin.lean` rewrites the finite derivative center as an
explicit sum and rational expression. It contains no opaque `deriv` term.

`LeanLab/Riemann/LevinsonMontgomeryHeightTenFiniteEvaluator.lean` proves without `sorry`:

1. thirty independent rational rounded complex-power certificates at
   `w = 1/2 - 10i`, each with norm error at most `1/5000000000`;
2. a thirty-term ordinary partial-sum error at most `3/500000000`;
3. a logarithm-weighted partial-sum error at most `3/100000000`;
4. complete finite Euler--Maclaurin value and derivative center errors at most `1/50000000` and
   `1/1000000` respectively;
5. finite value norm greater than `3/2` and finite derivative norm below `2`; and
6. strict finite cross negativity
   `Re(D * conj Z) < -53/100` for the actual finite centers.

The thirty certificates are separate declarations so the Lean kernel checks them under the
project's default resource limits. No heartbeat or recursion-depth option was raised.

## Claim boundary

The last inequality concerns the finite Euler--Maclaurin centers. It has not yet been combined
with the analytic value and derivative remainder radii or the reflected archimedean logarithmic
derivative upper bound. Consequently this checkpoint does not prove the actual-zeta Speiser sign,
even at the endpoint.

There is also no variation theorem on a positive-width sigma interval, no finite rational
subcover of `0 <= sigma <= 1/2`, and no multiplicity-bearing equality of the zeta and
zeta-derivative zero counts below height ten. Therefore no complete height-ten certificate,
CountDichotomy, Speiser equivalence, H12, or RH is claimed.

## Local audit

- The new module builds successfully as `8739/8739` jobs.
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` pass
  `-DwarningAsError=true`.
- Selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The project Lean-source scan finds no `sorry`, `admit`, or `native_decide`.
- The changed Lean files contain no `maxHeartbeats` or `maxRecDepth` option.
- `git diff --check` passes.
- Full `lake build` passes `8823/8823` jobs.

## Next producers

1. Prove exact endpoint inequalities for the analytic Euler--Maclaurin remainders and the
   reflected archimedean term, then compose them with the finite margins.
2. Establish explicit sigma-variation bounds and kernel-check a finite rational subcover.
3. Independently construct the actual multiplicity-bearing low-zero count certificate.
4. Compose both producers into `levinsonMontgomeryHeightTenCertificate_actual`.

The global RH Goal and this campaign remain active.

## Public implementation

- Commit `9f3d28f7e4c1dbbf7647c8cd1418b50a7c34d656` passed Lean Action run
  `30665506516`, build job `91271458715`, in `6m19s`.
- The three implementation modules, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and
  `LeanLab.lean` are frozen by Git blob in
  `research/h14_h12_height_ten_endpoint_finite_evaluator_evidence_20260801.md`.
- The immutable-evidence documentation commit is pending public CI.
