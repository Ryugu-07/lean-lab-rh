# H7 Connes Nested-Projection Positive-Type Closure Receipt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01`

Node: `H7-CONNES-NESTED-PROJECTION-POSITIVE-TYPE-01`

Classification: `FULL_SUCCESS / SOURCE_POSITIVE_TYPE_HINGE_FORMALIZED`

## Verified public chain

| gate | commit | run | job | result |
| --- | --- | --- | --- | --- |
| docs-only preregistration | `59a6d8aa74fb48c3123e391e50e2e932408bcf66` | `30411132179` | `90447227409` | success in `1m33s` |
| frozen implementation | `25c18e31cd882f9ad2f43fe26900e450d98c0500` | `30411787173` | `90449324931` | success in `2m1s` |
| immutable evidence | `78f1810d722e9b846a4fb7c4b40c8d78b3edf95a` | `30411999399` | `90450005443` | success in `1m31s` |
| final ledger | `6ad4a77323b3fa163fe415d26fd01b0ce1073c92` | `30412182228` | `90450618374` | success in `1m32s` |

The five-file proof and registration diff from the frozen implementation through the final
ledger is empty.

## Closure

Close only:

```text
H7.connes.nested-projection-defect-positive-type
```

Lean proves that exact nesting of finite complex orthogonal projections makes their difference
an orthogonal projection and identifies the corresponding convolution-square trace exactly
with a Frobenius norm square. It also proves that individual projection laws without nesting
are insufficient by a dimension-one negative example.

Keep open:

- the actual number-field adèle-class Hilbert space and cutoff projections;
- the exact source containment `Q'_Lambda <= S_Lambda`;
- trace-class and normalization control;
- prolate and archimedean cutoff asymptotics;
- the uniform distributional limit to the complete Weil distribution;
- unconditional Weil positivity on an RH-equivalent test class;
- Hilbert--Polya, H7, and RH.

The persistent RH Goal remains active. Return to fresh cross-family historical omission
selection. Original conjectures and direct proof attempts remain open at every selection.
