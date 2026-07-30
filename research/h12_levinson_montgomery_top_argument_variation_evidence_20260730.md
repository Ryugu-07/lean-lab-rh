# H12 Levinson--Montgomery Top Argument Variation Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-TOP-ARGUMENT-VARIATION-01`

Status: `IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Public implementation receipt

- commit: `adfc63d2d4c33fe3535180a8eac83d6d9e703c50`;
- Lean Action run: `30534415162`;
- build job: `90844126333`;
- duration: `2m39s`;
- result: pass.

## Frozen Lean set

At the public implementation commit:

| file | git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryTopArgumentVariation.lean` | `e94373faaa4b34c6709cce076aa8d33e02700400` |
| `LeanLab/Riemann/Targets.lean` | `5ee0e505d0e8d53733a1a929c2f94b0c800532d1` |
| `LeanLab/Riemann/TargetChecks.lean` | `2498ddd5457a4ac9ebf4d884e6dac437d42cda01` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `1ae2d02f957199556b6e2c8a7965af0b6134a832` |
| `LeanLab.lean` | `b25a891456b7ff4da4da1be54b3649d92de5d884` |

This evidence commit is docs-only and must leave every frozen blob unchanged.

## Proven endpoint

Lean proves:

1. a generic finite-crossing theorem for continuous argument variation using local
   half-plane logarithms;
2. support-cardinality charge to an analytic divisor's positive multiplicity finsum;
3. cofinal common zero-free actual top heights on the complete interval `[0,1]`;
4. actual zeta top variation bounded by `O(log(t+2))`;
5. phase-normalized actual derivative top variation bounded by `O(log(t+2))`, with exact
   cancellation of the constant phase from `zeta''/zeta'`;
6. one common constant controlling both actual variations at every sufficiently large
   admissible height and at cofinal such heights.

## Audit receipt

- standalone warning-as-error production-module compilation: pass;
- warning-as-error `LeanLab.lean`: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- exact campaign TargetChecks: nine;
- selected campaign axiom prints: eight, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder and forbidden-declaration scan: empty;
- `git diff --check`: empty;
- full local build: `8816/8816`, inherited warnings only;
- public implementation build: pass.

## Claim boundary

This closes the page-52 crossing-count-to-continuous-argument omission for both actual top
paths. It does not prove the multiplicity-aware global indented argument principle, exact
bottom orientation, either Levinson--Montgomery count identity, the complete dichotomy,
Speiser equivalence, H12, or RH.
