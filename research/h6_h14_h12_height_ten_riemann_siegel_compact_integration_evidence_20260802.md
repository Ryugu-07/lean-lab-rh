# Height-ten Riemann--Siegel compact integration evidence

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `EXACT_COMPACT_INTEGRATION / MEANINGFUL_PARTIAL /
TAIL_MASS_OPEN / GLOBAL_GOAL_ACTIVE`

## Frozen implementation

Implementation commit: `687d301d60a4c7bcbae0b4cb36f0a015a94a9b34`

Public Lean Action:

- run: `30723016379`;
- build job: `91429744340`;
- result: passed;
- duration: `2m38s`.

Frozen production blobs:

| file | blob |
| --- | --- |
| `LeanLab.lean` | `29970697ddb856d7a54f942f3c159618df4b4436` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelCompactIntegral.lean` | `61d4845fc6271d0f3bb9fcf4bcb0187e140c6974` |
| `LeanLab/Riemann/Targets.lean` | `7fe438803372222ae626c254087d6bc2bee7f262` |
| `LeanLab/Riemann/TargetChecks.lean` | `d3e9ac2759f46bdde74375860dd9377066dc47c8` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `a4a7a51876ef43bd2526c4c4c9938f3779544ce7` |

This evidence commit is docs only. Its CI and a post-CI `git ls-tree` check must preserve every
blob in this table.

## Immutable evidence verification

Docs-only evidence commit `604e8c73246b1a4eacdf65764ceb7b6caede5493` passed Lean Action run
`30723158790`, build job `91430133639`, in `1m45s`. A post-CI `git ls-tree` check confirms that
all five production blobs remain exactly equal to the frozen table.

## Compiled claim boundary

The frozen implementation proves rational polynomial exponential bounds and exact formal
primitives for both compact pieces of the cutoff-one source contour. These bounds transfer to the
literal Riemann--Siegel line integrand and prove

```text
positive compact mass <= 7/20,
negative compact mass <= 1/10,
combined compact mass <= 9/20.
```

No floating-point value, sampled quadrature, or external boolean is a theorem premise.

## Audit boundary

- production and registration files pass warning-as-error;
- full local build passes `8833/8833`;
- seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
- focused placeholder and patch scans are clean;
- three exact polynomial normalization declarations use theorem-local resource scopes.

## Strict limits

The frozen implementation does not prove either full endpoint mass or their total `<=3/5`. The
two remaining source-contour tails must still total at most `3/20`. Therefore the literal
Riemann--Siegel remainder margin, critical-line interval nonvanishing, any unconditional vertical
boundary zone, the complete height-ten certificate, H12, and RH remain open. The parent campaign
and global Goal remain active.
