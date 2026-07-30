# H11 PCC Slow-Window Diagonal Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Public implementation receipt

- commit: `bea2f6bbe1106a5c728408fdfdf45d5f49ebd49e`;
- Lean Action run: `30520277721`;
- build job: `90798883929`;
- duration: `2m21s`;
- result: pass.

## Frozen Lean set

At the public implementation commit:

| file | git blob |
| --- | --- |
| `LeanLab/Riemann/PCCSlowWindowDiagonal.lean` | `6c086dc39d9e79a14caa6780c73dc707f7b942d6` |
| `LeanLab/Riemann/Targets.lean` | `67372670be2fbc6ef083344201800a72093530d0` |
| `LeanLab/Riemann/TargetChecks.lean` | `ac8ca926ac8cf0b588b0896da00f606c98b16751` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `43193adc4394e2ef72b99b77c74c44b39c4313b2` |
| `LeanLab.lean` | `5371da0cd681cbe99d774fffcc7af188b5b46c98` |

This evidence commit is docs-only and must leave every frozen blob unchanged.

## Proven endpoint

Lean proves:

1. every fixed positive stage is eventually admissible under fixed-stage error convergence and
   a divergent external cap;
2. the greatest currently admissible stage tends to infinity;
3. that stage is eventually positive and below the cap;
4. its moving-stage error tends to zero;
5. its reciprocal lower window tends to zero and its real upper window tends to infinity;
6. a `Nat.sqrt L` cap retains the eventual square constraint;
7. fixed-stage convergence cannot justify an arbitrary fast diagonal.

## Audit receipt

- standalone warning-as-error module compilation: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- exact campaign TargetChecks: eight;
- selected campaign axiom prints: seven, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder scan: empty;
- custom `axiom`/`constant` scan: empty;
- resource-relaxation scan: empty;
- `git diff --check`: empty;
- full local build: `8813/8813`, inherited warnings only;
- public implementation build: pass.

## Claim boundary

This is the abstract moving-parameter quantifier bridge behind the source's slow-window choice.
It does not instantiate the error family with the actual PCC remainder, prove PCC, prove the
Fujii or Fejer asymptotics, derive HMH, eliminate sparse exceptions, prove H11, or prove RH.
