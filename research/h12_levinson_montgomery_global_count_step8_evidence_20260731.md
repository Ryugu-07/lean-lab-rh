# H12 Levinson--Montgomery Global Count Step 8 Immutable Evidence

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Status: `IMMUTABLE_EVIDENCE_CI_REQUIRED / CAMPAIGN_ACTIVE`

## Public implementation receipt

- commit: `6863823d119977a660d0643595cbfc61b7282018`;
- Lean Action run: `30653076645`;
- build job: `91230777600`;
- duration: `2m18s`;
- result: pass;
- run URL:
  `https://github.com/Ryugu-07/lean-lab-rh/actions/runs/30653076645`;
- job URL:
  `https://github.com/Ryugu-07/lean-lab-rh/actions/runs/30653076645/job/91230777600`.

## Frozen Lean set

At the public implementation commit:

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryCriticalStrip.lean` | `9b364839b6fd6a8fb8574324791db56eb487d57e` |
| `LeanLab/Riemann/Targets.lean` | `06156852495ac9d191b9a5a134e3cdfdb08b0789` |
| `LeanLab/Riemann/TargetChecks.lean` | `2038880912b1332d3eef1359e2107a243c743142` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `5c87b5a66c2cea65fdd1fcc0ca71e0a92bf56aff` |
| `LeanLab.lean` | `0ded4bd589c8ce4b69743d6b6a8e5e11fbbb7592` |

This evidence commit is documentation-only and must leave every frozen blob unchanged.

## Proven endpoint

Lean proves the unconditional theorem

```lean
theorem levinsonMontgomeryLogCountBound_actual :
    LevinsonMontgomeryLogCountBound
```

for the actual multiplicity-bearing zeta and zeta-derivative counts at every sufficiently large
real cutoff. The proof combines an adaptive uniform strict-left vertical, principal-log argument
variation bounds on both vertical sides, the public Jensen top estimates, a fixed-bottom bound,
and finite-support transfer from admissible heights to arbitrary large real cutoffs.

Lean also proves the full exact-count branch conditionally from either
`LevinsonMontgomeryNegativeExactCountBase` or the source-shaped
`LevinsonMontgomeryHeightTenCertificate`. The first unavailable theorem is exactly

```lean
theorem levinsonMontgomeryHeightTenCertificate_actual :
    LevinsonMontgomeryHeightTenCertificate
```

No numerical zero table is used as a premise.

## Audit receipt

- standalone warning-as-error production-module compilation: pass;
- warning-as-error `LeanLab.lean`: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- new exact campaign TargetChecks: six;
- selected campaign axiom prints: nine, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder and forbidden-declaration scan: empty;
- `git diff --check`: empty;
- full local build: `8819/8819`, inherited warnings only;
- public implementation build: pass.

## Claim boundary

The unconditional `LevinsonMontgomeryCountDichotomy`, the full Theorem 1 conjunction,
unconditional Speiser equivalence, derivative-zero exclusion, H12, and RH remain open. The
height-ten certificate is a finite low-height proof obligation, not an admitted axiom. The
persistent RH Goal remains active.
