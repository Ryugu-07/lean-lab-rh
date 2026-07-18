# Route Selection after the Polymath Criterion

Date: 2026-07-18

Decision: select
`LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`.

## Authoritative starting point

Campaign `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01` is publicly closed. Lean now
proves that the three source-aligned initial, final, and barrier region predicates for the second
row of Polymath Table 1 imply `deBruijnNewmanAllZerosReal (1 / 5)`. None of those three predicates
is currently proved.

The exact open numerical frontier is therefore visible in the type of
`deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_row`; there is no remaining hidden
simple-zero or repeated-zero hypothesis.

## Source audit

- D. H. J. Polymath, arXiv `1904.12438`, Theorem 1.2, Theorem 1.3, Corollary 1.4, Sections 7--8,
  and Table 1 give the criterion, the effective Riemann--Siegel approximation, the nonvanishing
  test, and the numerical row.
- Platt--Trudgian, arXiv `2004.09765`, verifies RH through height `3*10^12` by interval arithmetic
  and uses the second row to obtain `Lambda<=0.2`.
- The public computational repository `km-git-acc/dbn_upper_bound` was inspected at commit
  `5fde84e11ba80adad5c225a4eaa0a28b68dc925d`. It contains the relevant Arb programs, stored sums,
  and the output file
  `windnum_nolemma_x5000000194858_y_0.16733_1_t_0_0.186.txt`.
- That repository does not grant a software license in its `LICENSE` file. No code or data is
  vendored. Its decimal/Arb output is navigation evidence only and cannot be a Lean premise.

## Value comparison

1. **Polymath Table 1 certificates.** Directly consumes the newly compiled criterion and reaches
   the strongest audited unconditional H6 upper bound. It has precise success and failure
   surfaces: finite-height RH, effective Riemann--Siegel bounds, and a compact barrier winding
   certificate.
2. **W2/G7 direct positivity.** RH-equivalent and therefore logically stronger, but the latest
   project audit found no new global cancellation mechanism after the prime-kernel indefiniteness
   obstruction.
3. **M2/G3 explicit approximants.** RH-equivalent through the compiled Baez--Duarte criterion,
   but no materially new residual estimate or approximation family was found in this selection.
4. **H10 function-field continuation.** The finite spectral-rigidity endpoint is compiled, while
   the number-field transfer remains heuristic and currently has less immediate Lean leverage.
5. **H1/H2 counting infrastructure.** Mathematically central, but it does not presently attach to
   a source theorem as directly as the exposed H6 certificate frontier.

## Selected fixed endpoint

Prove, without hypotheses, the three specialized region predicates at

```text
t0 = 93/500
X  = 5*10^12 + 194858
y0 = 16733/100000
```

and then compile `deBruijnNewmanAllZerosReal (1/5)`. The campaign may span multiple loops. A
conditional bridge, a numerical rerun, or a generic interval helper is a checkpoint rather than
campaign success.

The first unavoidable subedge is the exact transport from a source-aligned finite-height RH
statement through `H_0(z)=(1/8)xi((1+i*z)/2)` to the specialized initial region. This is selected
for Loop 1 because it fixes the sign, factor-of-two, zero-height boundary, and exact height
coverage before any computational certificate format is designed.

The persistent RH Goal remains active regardless of this campaign's local outcome.
