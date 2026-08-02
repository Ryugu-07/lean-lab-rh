# Route Selection after H12 Reflected Evaluator

Date: 2026-08-02

Decision: select `PROOF-ATTEMPT-20260802-H12-H1-LOW-ZERO-MASS-01`.

Selected node: `H12-H1-LOW-ZERO-MASS-01`.

Open parent: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`.

Global RH Goal: active.

## Selection rule

Historical replay is an omission search. The selected attack must preserve a source mechanism
that the previous reduction discarded, weaken a previously stated producer, or import a proved
input from another historical family. Ease of formalization is not a selection reason. Original
conjectures, falsification, and direct RH attacks remain open.

## Cross-family comparison

| family | exact live edge | present value |
| --- | --- | --- |
| H12 direct evaluator | Kernel-check a finite rational subcover for the reflected quotient on `[13/2,7]`. | Exact and feasible, but it treats every point separately and discards the negative paired-zero mass in the historical formula. |
| H1 x H12 low-zero mass | Certify one critical-line zero in `[14,15]`, retain its single negative term in Levinson--Montgomery equation `(2.1)`, and close `[13/2,7]` uniformly. | **Select.** Navigation shows a conservative rational margin; this converts a continuum table into one historical low-zero sign bracket and tests a cross-route repair. |
| H1 mollifier | Prove the arbitrary-length mollified moment or a last-exception localizer. | High RH relevance, but no new source input changes the deep moment frontier in this checkpoint. |
| H7 spectral/trace | Prove the actual finite-prime ground-state rate and compact-uniform transform convergence. | Highest structural rank, but the source operator and coercive comparison remain unavailable; the present H1 x H12 bridge has an exact existing producer. |
| H10 function field | Construct a regularized number-field trace with a uniform infinite tail. | The finite rigidity mechanism is compiled, while the number-field object remains the exact broad gap. |
| H11 statistics | Amplify one sparse off-line orbit into a nonvanishing statistical defect. | Existing density-scale information still permits the last sparse exception. |

## Material difference

The preceding checkpoint built an actual second-corrected Euler--Maclaurin reflected evaluator and
stopped at a finite-subcover producer. The new attack does not improve its constants. It returns to
the exact Levinson--Montgomery decomposition

```text
Re(zeta'/zeta)(iy) = archimedean(iy) + paired-zero-sum(iy)
```

and retains one term of the paired-zero sum. For a critical-line zero
`rho=1/2+i*gamma`, that term is

```text
-1 / (2 * (1/4 + (y-gamma)^2)).
```

Thus `13/2<=y<=7` and `14<=gamma<=15` give the uniform bound `<=-1/145`. A six-step digamma shift
is navigationally sufficient to prove the archimedean term `<3/500`; these rational bounds have
strict combined margin.

## Exact next campaign

The fixed producer and all claim boundaries are recorded in
`research/h12_h1_low_zero_mass_prereg_20260802.md`. No navigation decimal or known zero table may
enter a Lean premise. The actual low-zero producer must be a kernel-checked
`HardyXiBracketsZero 14 15`, most naturally through the compiled Riemann--Siegel or
Euler--Maclaurin machinery.

This selection does not prove the low-zero bracket, the residual interval, the complete boundary,
the height-ten certificate, H12, or RH.
