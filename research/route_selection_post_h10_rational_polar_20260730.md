# Route Selection after the H10 Rational Polar Realization

Date: 2026-07-30

Status: `H11_PCC_SLOW_WINDOW_DIAGONAL_LOCAL_SUCCESS`

Parent campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Parent public closure:

- implementation `97b055c30194e61853820ab263d949fd49cc12de`, Lean Action run
  `30518731227`, build job `90794240899`, in `2m37s`;
- immutable evidence `bb2f134424bf4d569d22219fa8acad06c500ef35`, Lean Action run
  `30518970625`, build job `90794957095`, in `1m38s`.

## Fresh comparison

| family | exact live producer | reading |
| --- | --- | --- |
| H1 mollifiers | source-strength long mollified moments | deep analytic input already isolated |
| H2 density | Mobius-twisted fourth moment and Type-I bow exclusion | exact source obstacles already isolated |
| H7 spectral | actual Rayleigh-excess/ground-gap rate | exact source spectral obstacle already isolated |
| H10 function fields | general-curve pole filtration and Riemann--Roch dimensions | valuable but currently a broad geometry stack after the actual `K(t)` specialization |
| H11 statistics | PCC-to-HMH moving-window diagonal and Fejer-kernel cancellation | successful recent historical argument with a specific unformalized quantifier step |
| H12 Speiser | global indented count and top variation | broad global contour package |

H11 is selected because Goldston--Lee--Schettler--Suriajaya v4 contains a precise inference not
yet represented in Lean. PCC is stated uniformly on each fixed compact interval
`0<lambda0<=lambda<=lambda1<infinity`, while Remark 1 then chooses
`lambda0(T)->0` and `lambda(T)->infinity`, slowly enough to preserve the asymptotic and the
constraint `lambda(T)^2<=L(T)`.

Pointwise or locally uniform convergence does not justify an arbitrary moving parameter. It does
justify a sufficiently slow one by a diagonal construction. The selected campaign formalizes
that exact quantifier bridge and a counterexample to the arbitrary-fast version.

## Selected node

Campaign:
`LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01`

Node:
`H11-GOLDSTON-PCC-SLOW-WINDOW-DIAGONAL-01`

Mode: `LITERATURE / OMISSION-AUDIT / FALSIFICATION`

This node does not prove PCC, Fujii's moment theorem, the Fejer-kernel asymptotic, HMH,
density-one critical zeros, sparse-exception exclusion, H11, or RH. It tests whether the source's
moving-window passage is logically available from its stated fixed-window uniformity.

## Local outcome

The selected bridge compiles. The greatest currently admissible stage tends to infinity while
staying below any prescribed divergent cap and carrying the error to zero. A `Nat.sqrt L` cap
retains the exact square constraint from Section 8. The fixed-stage-convergent fast-diagonal
counterexample also compiles, so the result licenses a sufficiently slow choice and no stronger
moving-parameter claim.

The next source-facing H11 edge is no longer the abstract diagonal argument. It is to express the
actual PCC remainder as a fixed-stage error family and verify that the source's fixed compact
uniformity supplies each hypothesis before composing the selected window with the
PCC-to-HMH calculation.
