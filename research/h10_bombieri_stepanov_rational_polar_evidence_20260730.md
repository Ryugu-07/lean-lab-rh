# H10 Bombieri--Stepanov Rational Polar Immutable Evidence

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Public implementation receipt

- commit: `97b055c30194e61853820ab263d949fd49cc12de`;
- Lean Action run: `30518731227`;
- build job: `90794240899`;
- duration: `2m37s`;
- result: pass.

## Frozen Lean set

At the public implementation commit:

| file | git blob |
| --- | --- |
| `LeanLab/Riemann/BombieriStepanovRationalPolar.lean` | `dfcaf27ed486dc63b60d0d8c941c6a3cdf2d9e45` |
| `LeanLab/Riemann/Targets.lean` | `9d13a1da122d4dd2637a43ed25128441db6f3bce` |
| `LeanLab/Riemann/TargetChecks.lean` | `61fbbb263168d4fae500cfdbb1edc3353cbc33ad` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `bd29d901e6136e2944f9b85bf8f1770115f51267` |
| `LeanLab.lean` | `c0150d86d12c1e78ab48d1a5f658803c8f9c2374` |

This evidence commit is docs-only and must leave every frozen blob unchanged.

## Proven endpoint

Lean proves:

1. `i*pPower+j*q` is injective on the bounded source when
   `pPower>0` and `l*pPower<q`;
2. the corresponding finite coefficient family embeds injectively into `K[X]`;
3. composition with `K[X] -> RatFunc K` gives an injective actual function-field
   realization;
4. a smaller-dimensional descent target has a kernel vector whose realized rational function
   is nonzero;
5. basis vectors have the exact prescribed infinity valuation;
6. the equality boundary is sharp: a nonzero two-term source realizes to zero when
   `l=1` and `pPower=q=1`.

No coprimality premise is present.

## Audit receipt

- standalone warning-as-error module compilation: pass;
- warning-as-error `Targets.lean`: pass;
- warning-as-error `TargetChecks.lean`: pass;
- warning-as-error `AxiomsAudit.lean`: pass;
- exact campaign TargetChecks: six;
- selected campaign axiom prints: six, each exactly within
  `[propext, Classical.choice, Quot.sound]`;
- placeholder scan: empty;
- custom `axiom`/`constant` scan: empty;
- resource-relaxation scan: empty;
- `git diff --check`: empty;
- full local build: `8812/8812`, inherited warnings only;
- public implementation build: pass.

## Claim boundary

This is the rational curve `K(t)` specialization of Bombieri's polar-order lemma. It is not the
general smooth projective curve theorem. The actual one-point pole filtration, pole-ordered
basis, Frobenius order multiplication, no-poles-implies-constant theorem, Riemann--Roch
dimensions, point count, Galois lower bound, function-field RH composition, number-field
transfer, H10, and RH remain open.

