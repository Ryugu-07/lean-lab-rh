# R3 Symmetry-Paired Li Zero Formula Campaign

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-SYMMETRIC-ZERO-01`

Route: R3, Li and Weil positivity

Status: `LOCAL_VERIFICATION_COMPLETE`

Fixed target and admission conditions:
`research/r3_li_symmetric_zero_prereg_20260715.md`.

## Attempt A

The admitted proof is one indivisible batch:

1. compile the two preregistered falsification witnesses;
2. construct the multiplicity-preserving divisor-index reflection equivalence;
3. normalize the finite differentiated zero contribution to the reflected raw Li term plus its
   reciprocal compensation;
4. average the already summable contribution along the equivalence;
5. derive cancellation of the Hadamard linear term from `riemannXi (1-s) = riemannXi s`;
6. prove the unconditional all-index symmetry-paired zero formula;
7. under RH, identify every paired term with a half norm square and prove the entire coefficient
   family is real and nonnegative.

No helper alone counts as campaign progress.

## Attempt A Result

All seven mathematical steps in the indivisible batch compile.

- `not_summable_liRawZeroTerm_one_nat_succ` rejects direct absolute summability of the raw first
  Li term using the harmonic sequence while retaining squared-reciprocal summability.
- `liRawZeroTerm_pair_quarter_two` checks the off-critical pair `rho=1/4`, `m=2` is `-32/9`, so
  unconditional termwise positivity is not smuggled into the proof.
- `riemannXiDivisorZeroReflectEquiv` is an involution on the full divisor index. Its value is
  exactly `1-rho`, and the explicit finite copy index is transported through the proved divisor
  multiplicity equality.
- `riemannXiLiZeroContribution_eq_reflected_raw` is the all-index finite algebraic
  normalization. Averaging this summable contribution along the reflection equivalence gives
  `summable_riemannXiSymmetrizedLiZeroTerm`.
- `hadamard_polynomial_add_half_reciprocal_tsum_eq_zero` derives cancellation of the linear
  Hadamard term from the xi functional equation at `0` and `1`; it is not an assumed coefficient
  identity.
- `liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm` proves the unconditional
  all-index raw paired formula with the project shift `n -> lambda_(n+1)` intact.
- Under `RiemannHypothesis`, each paired term is exactly half a complex norm square.
  `liCoefficientCandidate_im_eq_zero` and `liCoefficientCandidate_re_nonneg` therefore hold for
  every project index.

## Verification

- `rtk lake env lean LeanLab/Riemann/LiSymmetricZeroFormula.lean`: passed without warnings.
- `rtk lake build LeanLab.Riemann.LiSymmetricZeroFormula`: passed, 8,624 jobs, with the new module
  warning-free.
- Exact `TargetChecks` statement witnesses passed.
- The eight selected declarations in `AxiomsAudit` use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `rtk lake build`: passed, 8,660 jobs. Replayed warnings are confined to pre-existing modules.
- Placeholder, explicit declaration, `native_decide`, and resource-relaxation scans are empty.
- `rtk git diff --check`: passed.
- Publication commit, push, and public Lean Action CI remain pending.

## Progress Accounting

Result: `BRIDGE_REDUCED`.

Route-local `hard_gap_delta=2`: the compensated-series/Hadamard-polynomial representation is
normalized to a summable symmetry-paired raw zero formula, and the complete RH-forward
all-index real-nonnegativity direction is closed. The RH assumption frontier is unchanged because
the positivity result assumes RH. The reverse Li/Bombieri-Lagarias implication from all-index
nonnegativity to RH remains open and is not used.

Next state after public verification: `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.
