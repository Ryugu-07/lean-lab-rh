# H1 Levinson--Siegel Step Geometry Closure Receipt

Date: 2026-07-29

Campaign: `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01`

Node: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`

Classification: `FULL_SUCCESS / STRUCTURAL_OMISSION_GEOMETRY_FORMALIZED`

## Verified public chain

| gate | commit | run | job | result |
| --- | --- | --- | --- | --- |
| docs-only preregistration | `ab02915f8719c6715e0cadd06dcaad9fa7a10a7d` | `30409200376` | `90441363357` | success in `1m30s` |
| frozen implementation | `fb5d03e268849dbac7c7d51375d245eba944a92b` | `30410129919` | `90444149672` | success in `2m6s` |
| immutable evidence | `a7d1e38bba631fb7deb9b9a9adbd19a9198dd9fc` | `30410358415` | `90444833678` | success in `2m1s` |
| final ledger | `f0ebc6755a84626f325ef2a58efdbb4361a6edf4` | `30410543932` | `90445390713` | success in `1m53s` |

The five-file proof and registration diff from the frozen implementation through the final
ledger is empty.

## Closure

Close only:

```text
H1.levinson-siegel.step-geometry
```

Lean proves that the source endpoint and reflection class contains an explicit smooth
normalized logistic family converging pointwise to Siegel's step. Its midpoint slope grows at
least linearly in the sharpness parameter, and every differentiable sharp transition obeys a
general secant-slope derivative lower bound.

Keep open:

- the source hypergeometric optimizer and its exact relation to the compiled witness;
- quantitative polynomial approximation with explicit degree and derivative growth;
- mollified zeta mean-value estimates uniform in the growing complexity;
- the actual Levinson--Conrey auxiliary count and Littlewood-lemma bridge;
- critical-line zero proportions and sparse off-line exception exclusion;
- H1 and RH.

The persistent RH Goal remains active. Return to fresh cross-family historical omission
selection. Original conjectures and direct proof attempts remain open at every selection.
