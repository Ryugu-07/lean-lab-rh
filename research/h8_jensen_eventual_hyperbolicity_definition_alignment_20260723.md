# H8 Jensen Eventual-Hyperbolicity Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H8-JENSEN-EVENTUAL-HYPERBOLICITY-01`

Lean module: `LeanLab/Riemann/JensenEventualHyperbolicity.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

## Polynomial dictionary

| Source object | Lean object | Alignment |
| --- | --- | --- |
| Real coefficient sequence `gamma(n)` | `a : Nat -> Real` | Generic coefficient input. The campaign does not instantiate the xi Taylor coefficients. |
| Classical Jensen polynomial `J^{d,n}(X)` | `jensenPolynomial a d n` | Exact finite sum `sum_{j=0}^d choose(d,j) * a(n+j) * X^j`. |
| Hyperbolic/real-rooted polynomial | `JensenHasOnlyRealRoots p` | Every complex zero of the mapped real polynomial has imaginary part zero. The predicate is root-based and does not use numerical approximations. |
| Fixed-degree eventual hyperbolicity | `forall d, eventually n in atTop, JensenHasOnlyRealRoots ...` | Exact quantifier order proved by `jensenSingleDefect_eventually_hasOnlyRealRoots`. |
| All-degree/all-shift hyperbolicity | `forall d n, JensenHasOnlyRealRoots ...` | The stronger conclusion falsified for the generic defect sequence. For actual xi coefficients this remains the RH-bearing open condition. |

## Model alignment

`jensenSingleDefectCoefficients m` is one at every index except `m+1`, where it is zero.

- If `n+d <= m`, the Jensen window lies before the defect. Lean proves the polynomial is exactly
  `(1+X)^d`, so every prescribed finite initial wedge can be passed by placing the defect later.
- If `m+1 < n`, the window lies after the defect. Lean again proves exact equality with
  `(1+X)^d`; therefore every fixed degree is eventually real-rooted.
- At degree `2` and shift `m`, the coefficient window is `(1,0,1)`. Lean proves the polynomial is
  exactly `1+X^2`, evaluates it at `I`, and proves the root is nonreal.

The all-one sequence is used only as a finite-window reference. Its Jensen polynomial identity is
proved coefficientwise from `Polynomial.coeff_one_add_X_pow`.

## Source quantifier boundary

The Griffin--Ono--Rolen--Zagier and Griffin--Ono--Rolen--Thorner--Tripp--Wagner results prove, for
the relevant xi sequence, eventual hyperbolicity after fixing the degree. The RH criterion requires
every degree and every shift. The Lean model is a counterexample to the generic implication

`fixed-degree eventual hyperbolicity -> all-degree/all-shift hyperbolicity`.

It is not a counterexample to either source theorem because its coefficient sequence is not the xi
sequence. It also does not refute the Jensen--Polya equivalence, which retains the all-index
hypothesis.

## Duran 2024 boundary

Duran's Brenke-polynomial construction supplies additional real-rootedness criteria equivalent to
Laguerre--Polya membership and hence new RH-equivalent families for a zeta-related function. No
Brenke polynomial is represented in the Lean module. The source is recorded because it updates the
historical map, but it does not provide the missing all-index proof and is not used as a premise.

## Deliberately absent claims

- No actual xi Taylor coefficient is defined or estimated.
- No source eventual-hyperbolicity theorem is re-proved.
- No statement says eventual hyperbolicity is useless for every possible xi-specific argument.
- No finite root computation is promoted to an infinite conclusion.
- No RH implication is claimed for the generic coefficient model.

The surviving H8 gap is an actual-xi mechanism uniform in both degree and shift, or another theorem
that closes every exceptional window rather than moving the cutoff separately for each degree.
