# H12 Levinson--Montgomery Jensen Top Zero-Count Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Public implementation receipt

- commit: `12ddf9bb10f68d3826897bb5403a2ac803da45b0`;
- Lean Action run: `30530385387`;
- build job: `90831064393`;
- duration: `2m52s`;
- result: pass.

## Frozen Lean set

At the public implementation commit:

| file | git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryJensenTopZeroCount.lean` | `bcc912ea1ddd7df02b66ea9997d04057a8061e20` |
| `LeanLab/Riemann/Targets.lean` | `61746c32ab8093fadcd27a4cab51e511d461927d` |
| `LeanLab/Riemann/TargetChecks.lean` | `96caa32f6150ee274197c228a7f6e762fff2b12a` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `4fcb9b83563ac58c8dd91d5f98ec172aa3ac9760` |
| `LeanLab.lean` | `3a5842b0999bbfed15caab316f3842c71caf1880` |

This evidence commit is docs-only and must leave every frozen blob unchanged.

## Proven endpoint

Lean proves:

1. actual zeta and phase-normalized zeta-derivative conjugate-reflection symmetrizations are
   analytic on the fixed outer Jensen ball;
2. actual zeta has uniform polynomial growth on the complete fixed strip;
3. Cauchy's estimate gives uniform polynomial growth for the actual zeta derivative;
4. both actual symmetrizations have fixed quantitative center separation;
5. both multiplicity-bearing divisor sums on the inner ball are `O(log T)`;
6. every actual source crossing on `[0,1]` lies in the corresponding divisor support;
7. the unnormalized derivative center is not silently substituted for the required
   phase-normalized source object.

## Audit receipt

- standalone warning-as-error production-module compilation: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- exact campaign TargetChecks: seven;
- selected campaign axiom prints: seven, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder and forbidden-declaration scan: empty;
- `git diff --check`: empty;
- full local build: `8815/8815`, inherited warnings only;
- public implementation build: pass.

## Claim boundary

This closes the actual local Jensen top zero-count producer compressed into the page-52
source sentence. It does not yet prove the crossing-to-continuous-argument theorem, admissible
cofinal top heights, the global indented argument principle, either Levinson--Montgomery count
output, the complete dichotomy, Speiser equivalence, H12, or RH.
