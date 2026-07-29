# H2 Classical Detector Inverse Mellin Closure Receipt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-01`

Node: `H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-LINE-01`

Classification: `FULL_SUCCESS / KNOWN_INVERSE_MELLIN_EDGE_FORMALIZED`

## Verified public chain

| gate | commit | run | job | result |
| --- | --- | --- | --- | --- |
| docs-only preregistration | `b760e6becaa981c412ba2d3935daaecc82a50742` | `30412943783` | `90453042732` | success in `2m7s` |
| frozen implementation | `8c5d820a92178dfd3ad3582e9ffe733a7377bb0e` | `30414837829` | `90458965005` | success in `2m59s` |
| immutable evidence | `292edf1ee14cab188b2b8696df2f7722350f4f58` | `30415037051` | `90459582118` | success in `2m10s` |
| final ledger | `2749e85f2ab999ab5adaf87431453a3dcea8aa6a` | `30415195469` | `90460076360` | success in `1m59s` |

The five-file proof and registration diff from the frozen implementation through the final
ledger is empty.

## Closure

Close only:

```text
H2.classical-detector.inverse-mellin-line
```

Lean proves Gamma vertical integrability for every positive line, specializes Mellin inversion
to the exponential kernel, justifies the actual detector coefficient sum-integral exchange on
`Re(z)+c>1`, and discharges `ClassicalDetectorInverseMellinLine` with no extra premise.

Keep open:

- the infinite contour shift to `Re(w)=1/2-Re(rho)`;
- both horizontal-edge limits for the actual Gamma-Mobius-zeta factor;
- the shifted detector and dyadic-block identity;
- Type-I/Type-II and large-value production;
- zero-density estimates and sparse-exception exclusion;
- H2 and RH.

The persistent RH Goal remains active. Return to fresh cross-family historical omission
selection after this receipt is public green. Original conjectures and direct proof attempts
remain open at every selection.
