# R3 All-Index Li Zero Formula Campaign

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-ZERO-FORMULA-01`

Route: R3, Li and Weil positivity

Status: `BRIDGE_REDUCED`

Fixed target and admission conditions:
`research/r3_li_zero_formula_prereg_20260715.md`.

## Attempt A

The proof is decomposed internally, but the campaign result is indivisible:

1. expand every derivative-defined Li candidate into a finite sum of iterated derivatives of
   `logDeriv riemannXi`;
2. define the explicit compensated zero derivative term;
3. prove its higher-order series is locally uniformly summable on the xi nonzero set using a
   compact-set far-zero bound dominated by `const * |rho|^(-2)`;
4. invoke `iteratedDerivWithin_tsum` and transport from within derivatives to ordinary derivatives
   at `1`;
5. use one fixed genus-one Hadamard polynomial and combine the identities for every index.

No partial helper is recorded as campaign progress unless the final all-index formula passes all
admission gates.

## Candidate Audit

- C1, the all-index Leibniz bridge alone, was rejected as too partial and retained only as a helper.
- C2, the fixed Hadamard-polynomial wrapper alone, was rejected as a quantifier wrapper and retained
  only as a helper.
- C3, immediate replacement by the raw classical zero sum, was rejected because the available
  squared reciprocal estimate does not make that uncompensated series absolutely convergent.
- C4, a full Weil explicit formula, was deferred to the separate R5 route family.
- C5, the all-index compensated derivative-to-zero bridge, was selected and completed.

## Compiled Result

`LeanLab/Riemann/LiZeroFormula.lean` defines the multiplicity-bearing zero index, the compensated
log-derivative term, its exact derivative family, and the open xi nonzero set. Lean proves:

1. the order-`k` derivative of `1 / (z-rho) + 1 / rho`, including the special order-zero
   compensation;
2. summability of the compensated zero series at every xi-nonzero point;
3. compact-local uniform summability of every positive-order derivative series;
4. the hypotheses needed by `iteratedDerivWithin_tsum` on the xi nonzero set and the resulting
   termwise-differentiation identity at `1`;
5. a single degree-at-most-one Hadamard polynomial giving every iterated log-derivative at `1`;
6. the finite all-index Leibniz expansion from the derivative-defined Li family;
7. `exists_liCoefficientCandidate_eq_hadamard_zero_formula`, which combines these facts for every
   natural index with no extra assumptions.

The local-uniform proof does not assume a numerical zero cutoff. On each compact set, finitely many
near zeros are discarded through the cofinite filter; every remaining term is bounded by
`k! * 2^(k+1) * |rho|^(-2)`, and the previously proved squared reciprocal series supplies the
summable majorant.

## Adversarial Results

- Indexing check passed: project index `n` remains classical `lambda_(n+1)`.
- Branch check passed: the complex logarithm enters only through the existing analytic germ near
  `1`; the global identity uses `logDeriv`, not a global logarithm branch.
- Multiplicity check passed: the divisor subtype index retains analytic multiplicity.
- Pole-separation check passed: `1` belongs to the xi nonzero set, hence differs from every indexed
  zero value.
- Compensation check passed: `1 / rho` is present at derivative order zero and differentiates to
  zero at positive order.
- Interchange check passed: pointwise summability was not substituted for local uniform
  summability.
- Exponential-factor check passed: `P.derivative` remains explicit in the final formula.
- Strength check passed: no RH, zero simplicity, zero ordering, positivity, or numerical premise is
  used.

## Literature

- Xian-Jin Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, JNT 65
  (1997), DOI `10.1006/jnth.1997.2137`.
- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, JNT 77 (1999), DOI `10.1006/jnth.1999.2392`.

This is classified `KNOWN_THEOREM_FORMALIZED_AND_PROJECT_ALIGNED`; no new mathematical theorem is
claimed.

## Verification

- `rtk lake env lean LeanLab/Riemann/LiZeroFormula.lean`: passed without warnings.
- `rtk lake build LeanLab.Riemann.LiZeroFormula`: passed, 8,623 jobs.
- `rtk lake env lean LeanLab/Riemann/Targets.lean`: passed.
- `rtk lake build LeanLab.Riemann.Targets`: passed, 8,649 jobs.
- `rtk lake env lean LeanLab/Riemann/TargetChecks.lean`: exact statement witness passed.
- `rtk lake env lean LeanLab/Riemann/AxiomsAudit.lean`: passed; the five selected new declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- `rtk lake build`: passed, 8,659 jobs. Replayed warnings are confined to pre-existing unrelated
  modules; the new module is warning-free.
- Full project source scan found no `sorry`, `admit`, project `axiom`, `native_decide`, or resource
  relaxation token.
- `rtk git diff --check`: passed.
- Implementation commit `88037ad4423c430809f3f381fd354699dc307827` is public on `main`.
- Lean Action CI run `29397368460`, build job `87293810332`, succeeded in 1m48s.

## Progress Accounting

Result: `BRIDGE_REDUCED`.

Route-local `hard_gap_delta=1`: the fixed all-index derivative-to-compensated-zero edge is removed.
The RH assumption frontier is unchanged. The raw classical zero-sum normalization/convergence,
all-index positivity, exact Li/RH equivalence, and RH remain open.

Next state after publication: `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.
