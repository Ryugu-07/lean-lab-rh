# Height-Ten Complete-Boundary Structural Evidence

Date: 2026-08-02

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Classification: `MEANINGFUL_PARTIAL / SUBATTACK_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Public implementation

Frozen commit: `d3d975d3c4202a3d14f8ea2e931a400ea7ef65ff`

Public Lean Action:

- run: `30713362289`;
- build job: `91404656086`;
- conclusion: `success`;
- duration: `3m34s`.

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenCompleteBoundary.lean` | `6ffda5a242ebbc52a4d4b72825a52b23bb9bfc88` |
| `LeanLab/Riemann/Targets.lean` | `50cdc6a39fb5d198e79eb05072ff2d1f8a423334` |
| `LeanLab/Riemann/TargetChecks.lean` | `39d979903a18cf491dda36262c4e70c4eebd23b8` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `37f5f443207e3f8c94c82bad13a10145959a163a` |
| `LeanLab.lean` | `4b1fdbe83543fb198d26c82b31013b302d921277` |

The immutable-evidence commit is docs only. Its post-push audit must reproduce these five blob
identities exactly.

## Immutable-evidence verification

Docs-only commit `8b7cb43028e04917c510d96b0fe89050a1f7e947` passed Lean Action run
`30713557491`, build job `91405164201`, in `2m50s`. Post-push `git rev-parse` reproduced all five
frozen blob identities exactly.

This closes only the evidence gate for the structural checkpoint. The preregistered complete-
boundary subattack remains active.

## Compiled mathematical content

- exact critical-line equality between `Re(zeta'/zeta)` and the Levinson--Montgomery
  archimedean term wherever actual zeta is nonzero;
- exact positive-height Equation (2.1) with the paired-zero sum;
- imaginary-axis upper bound from nonpositivity of that paired-zero sum;
- proof-producing strict negativity of the critical-line archimedean term for `y>=13/2`;
- actual right-high quotient negativity conditional only on zeta nonvanishing.

## Audit record

- standalone new-module build: `8744/8744`;
- full build: `8828/8828`;
- all production and registration files pass warning-as-error;
- five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
- focused `sorry`, `admit`, `native_decide`, relaxed-resource, `unsafe`, custom-axiom, and
  `opaque` scan: empty;
- `git diff --check`: clean.

## Strict claim boundary

The result does not prove actual zeta nonvanishing on `[13/2,10]`, any unconditional complete
vertical clause, the other five candidate vertical signs, the complete top sign,
`SpeiserRotatedSlitBoundary I 10`, or the literal height-ten certificate. H12 and RH remain open.

The left vertical is not a copy of the critical-line proof: its paired-zero contribution does
not vanish. This exact route split is retained as an open evaluator or zero-sum problem.

Historical omission search remains the selection default, and independent conjecture proposal
and falsification remain open.
