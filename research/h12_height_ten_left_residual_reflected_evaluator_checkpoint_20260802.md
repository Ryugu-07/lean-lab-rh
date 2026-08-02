# H12 Height-Ten Residual-Left Reflected Evaluator Checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`.

Global RH Goal: active.

## Selection rationale

The user confirms that historical-route coverage is an omission search, not a bibliography task.
The default main line remains reconstruction of major human routes far enough to test neglected
branches, weakened premises, and cross-route repairs. Original conjectures, falsification, and
direct RH attacks remain open at every stage.

The selected work stays inside the historical Levinson--Montgomery boundary argument. It does not
optimize the already closed `y>=7` threshold. It builds the missing actual quotient evaluator for
the residual interval `13/2<=y<=7`.

## Compiled outputs

`LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurinSecond.lean` proves:

1. the exact extraction of `s*N^(-s-1)/12` from the first corrected Euler--Maclaurin formula;
2. the cubic periodic kernel bound `|B_3({u})|<=1/48`;
3. the actual-zeta value formula and error ball of order `N^(-Re(s)-2)`;
4. dominated parameter differentiation with majorant
   `1/48*log(u)*u^(-epsilon-3)`;
5. an explicit finite derivative center and actual-zeta derivative error ball.

`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftResidual.lean` proves:

1. a twice-shifted digamma--Stirling enclosure with radius
   `27/(128*||s/2+3||^2)`;
2. the exact positive-imaginary-axis reflection identity for `Re(zeta'/zeta)`;
3. a generic consumer from second-corrected reflected margins to actual zeta and derivative
   nonvanishing, strict negative quotient real part, and the rotated slit condition.

Principal declarations:

- `riemannZeta_eq_eulerMaclaurinTwoZetaApprox_add_remainder_of_re_pos`;
- `norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos`;
- `eulerMaclaurinTwoZetaDerivApprox_eq_finiteFormula`;
- `norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos`;
- `abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_shiftTwoApprox_le`;
- `logDeriv_riemannZeta_re_reflection_on_imaginaryAxis`;
- `speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_reflected_eulerMaclaurinTwo`.

## Navigation gate

Navigation-only arithmetic indicates that the second correction reduces the useful cutoff from
the earlier large table to the low tens. It also identifies the inherited unshifted reflected
archimedean upper as the immediate lost margin; two source-valid digamma shifts restore pointwise
margin in navigation.

No decimal, grid point, external boolean, or navigation estimate is a Lean premise.

## Exact remaining obstruction

The existing proof-producing logarithm and scaling-and-squaring backend can enclose finite centers
near fixed rational points. A new producer must build a finite rational subcover of `[13/2,7]`,
kernel-check the rounded value and derivative centers on each piece, and discharge the three
generic margins. Until that theorem compiles, the residual interval remains open.

This checkpoint does not prove the full left vertical, complete boundary, height-ten certificate,
H12, or RH.

## Audit state

The production modules, project entry, Targets, exact TargetChecks witnesses, and AxiomsAudit
compile. The selected declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
Focused forbidden-token and declaration scans are clean, `git diff --check` is clean, and the full
local build passes `8837/8837`. Public CI and immutable evidence are recorded separately once
complete.

## Runtime

- model: Codex, GPT-5 family; exact serving variant is not exposed;
- reasoning effort: not exposed;
- numerical loop budget: none under V4.1;
- compaction: resumed from an inherited summary before round 128 and re-read canonical governance,
  Targets, the active attempt log, hard-gap DAG, and the complete-boundary preregistration;
- global Goal: active.
