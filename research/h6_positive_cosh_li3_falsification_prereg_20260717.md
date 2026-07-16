# H6 Positive-Cosh Third-Li Falsification Preregistration

Date: 2026-07-17

Campaign: `AUDIT-20260717-H6-POSITIVE-COSH-LI3-01`

Mode: `FALSIFICATION`

Status: `LOCAL_IMPLEMENTATION_COMPLETE_PUBLIC_CI_PENDING`

## Route selection

The publicly closed H6-Z campaign proves the first two Li expressions of the exact theta heat
family from positivity of its hyperbolic kernel and one weighted Cauchy--Schwarz inequality. A
fresh selection compares direct H6-E zero continuation, the quantitative H6-Q endpoint, a third
theta-specific Li inequality, W2/G7 arithmetic positivity, and M2/G3 target-coupled
approximants. The last two routes have no new explicit cancellation identity or approximant in
the current conjecture pool, while the generic adjacent-gap and reverse-heat mechanisms already
have compiled obstructions.

Before investing in a source-specific third-moment proof, this audit tests the strongest tempting
generic extrapolation from H6-Z: that a positive even `cosh` transform, and hence its ordinary
positive moment/Hankel inequalities, should force the third Li differential expression to be
nonnegative. A two-atom model has a completely exact Lean surface and can decide that mechanism
without weakening the third coefficient or relying on floating-point signs.

## Exact mathematical endpoint

Let `L=log 2` and define the normalized positive two-atom transform

`G(s) = (1/8) * cosh((2*s-1)*L)/cosh(L)
       + (7/8) * cosh((2*s-1)*(10*L))/cosh(10*L)`.

Both coefficients of the unnormalized `cosh` atoms are strictly positive. Define

`Li1(G) = (G'/G)(1)`,

`Li2(G) = 2*(G'/G)(1) + (G'/G)'(1)`, and

`Li3(G) = 3*(G'/G)(1) + 3*(G'/G)'(1) + (1/2)*(G'/G)''(1)`.

The indivisible falsification endpoint proves:

1. `G` is entire and satisfies `G(1-s)=G(s)`;
2. both atom coefficients are strictly positive and `G(1)=1`;
3. with
   `beta=(1/8)*(3/5)+(7/8)*10*(1048575/1048577)`,
   `gamma=(1/8)+(7/8)*100`, and
   `delta=(1/8)*(3/5)+(7/8)*1000*(1048575/1048577)`,
   the first three Li values equal
   `2*beta*L`,
   `4*(beta*L+(gamma-beta^2)*L^2)`, and
   `6*beta*L+12*(gamma-beta^2)*L^2+
      (4*delta-12*beta*gamma+8*beta^3)*L^3`;
4. the first two values are strictly positive real numbers;
5. the third value is a strictly negative real number.

The sign in item 5 must be proved from exact rational arithmetic and Mathlib's certified bounds
`0.6931471803 < log 2 < 0.6931471808`. Numerical integration or decimal evaluation is not an
accepted premise.

## Proposed Lean interface

```lean
def h6PositiveCoshAudit (s : Complex) : Complex :=
  (1 / 8) * Complex.cosh ((2 * s - 1) * Real.log 2) /
      Real.cosh (Real.log 2) +
    (7 / 8) * Complex.cosh ((2 * s - 1) * (10 * Real.log 2)) /
      Real.cosh (10 * Real.log 2)

def h6PositiveCoshAuditLiOne : Complex :=
  logDeriv h6PositiveCoshAudit 1

def h6PositiveCoshAuditLiTwo : Complex :=
  2 * logDeriv h6PositiveCoshAudit 1 +
    deriv (logDeriv h6PositiveCoshAudit) 1

def h6PositiveCoshAuditLiThree : Complex :=
  3 * logDeriv h6PositiveCoshAudit 1 +
    3 * deriv (logDeriv h6PositiveCoshAudit) 1 +
    (1 / 2) * iteratedDeriv 2 (logDeriv h6PositiveCoshAudit) 1

theorem h6PositiveCoshAudit_entire :
    Differentiable Complex h6PositiveCoshAudit

theorem h6PositiveCoshAudit_reflection (s : Complex) :
    h6PositiveCoshAudit (1 - s) = h6PositiveCoshAudit s

theorem h6PositiveCoshAudit_one : h6PositiveCoshAudit 1 = 1

theorem h6PositiveCoshAuditLiOne_re_pos :
    0 < h6PositiveCoshAuditLiOne.re

theorem h6PositiveCoshAuditLiTwo_re_pos :
    0 < h6PositiveCoshAuditLiTwo.re

theorem h6PositiveCoshAuditLiThree_re_neg :
    h6PositiveCoshAuditLiThree.re < 0

theorem h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi :
    Differentiable Complex h6PositiveCoshAudit ∧
    (∀ s, h6PositiveCoshAudit (1 - s) = h6PositiveCoshAudit s) ∧
    0 < h6PositiveCoshAuditLiOne.re ∧
    0 < h6PositiveCoshAuditLiTwo.re ∧
    h6PositiveCoshAuditLiThree.re < 0
```

The implementation may expose auxiliary derivative and hyperbolic-value lemmas, but it may not
replace the exact two atoms, weights, standard Li differential convention, or strict third-order
sign by a weaker abstract moment tuple.

## Relation to RH and DAG

- `node_id`: H6-X/H6-E
- `gap_id`: G8
- `relation_to_RH`: obstruction below an attempted all-order positive-kernel Li mechanism
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- `expected_hard_gap_delta`: 0
- `expected_obstruction_node`: `OBS-H6-POSITIVE-COSH-LI3-01`

This finite transform is not the theta kernel and does not prove or falsify RH. If the endpoint
compiles, it proves that positivity of a `cosh` kernel and the resulting generic moment-matrix
positivity do not by themselves extend the H6-Z first-two argument to all Li indices. Any
successful continuation must use quantitative shape information about `Phi`, its heat tilt, or a
different all-index invariant.

## Sources and originality boundary

- Bombieri and Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, JNT 77
  (1999), gives the general all-index zero/Li framework.
- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*,
  arXiv:1904.12438, gives the exact positive `cosh`/theta heat family used by H6-Z.
- Sekatskii, *Generalized Bombieri--Lagarias' theorem and generalized Li's criterion*,
  arXiv:1304.7895, records generalized derivative criteria for broader zero sets.

A targeted primary-source search found general Li criteria and the theta heat transform, but no
claim that positivity of an arbitrary even transform forces even the third Li value. The model
is a project-generated obstruction test, not a novelty or priority claim.

## Boundary and finite-model checks

- One positive atom gives positive first three values in direct symbolic evaluation, so at least
  two atoms are required for the tested failure.
- A random finite-measure screen found negative generic third values; it was used only to select a
  rationally normalizable model and is not proof evidence.
- Choosing atoms at `log 2` and `10*log 2` makes both hyperbolic tangents exact rationals:
  `3/5` and `1048575/1048577`.
- The fixed weights make the normalized masses at `s=1` exactly `1/8` and `7/8`.
- The proposed third-value polynomial is negative throughout Mathlib's certified interval for
  `log 2`; the formal proof must establish this directly.

## Success, falsification, and stop criteria

- `success_criterion`: the exact positive two-atom transform, standard first-three Li values,
  first-two positive signs, and strict third negative sign compile; an aggregate exact witness,
  standard-only axiom audit, forbidden scans, full build, and public CI all pass.
- `falsification_criterion`: any registered algebraic or sign clause fails for the fixed model.
  Record the exact compiler or mathematical boundary instead of changing atoms after proof edits.
- `forbidden_success`: proving negativity for a free moment tuple; using floating-point
  evaluation; omitting entire-ness, reflection, coefficient positivity, or `G(1)=1`; changing the
  Li convention; or asserting anything about the actual theta kernel from this model.
- `local_stop`: close after the exact obstruction is compiled and audited, or after a registered
  clause is refuted and recorded. Do not grow a general exponential-polynomial library.

No Lean proof source has been edited in this campaign before this preregistration.

## Registered implementation result

Preregistration commit `316ece356aaf5a11f2ddd18ff91da7a9f2ac73e3` passed public Lean Action CI
run `29542262029`, build job `87766756340`, in `1m56s`, before proof-source edits.

`H6PositiveCoshLiAudit.lean` now compiles the exact fixed endpoint. The aggregate theorem
`h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi` carries the positive coefficients,
entire-ness, reflection, normalization, three exact standard Li formulas, and strict real sign
pattern `(+,+,-)`. The third sign uses Mathlib's certified lower bound for `log 2` and exact
rational algebra, not a numerical premise.

The standalone module, exact Targets and TargetChecks, five standard-only axiom prints,
forbidden declaration/proof/resource scans, `git diff --check`, and the 8,694-job full build pass
locally. Classification is `BRANCH_FALSIFIED`, with `hard_gap_delta=0`. Public implementation CI
and immutable evidence backfill remain before closure.
