# R3 Reverse Li Criterion Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01`

Mode: `INDEPENDENT_AUDIT -> LITERATURE -> DISCOVERY -> FALSIFICATION -> FORMALIZATION`

Route family: R3, Li and Weil positivity.

## Fixed Gap And Indivisible Endpoint

The preceding campaign proves the exact all-index symmetry-paired zero formula and the forward
implication

```lean
RiemannHypothesis -> forall n, 0 <= (liCoefficientCandidate n).re
```

The remaining fixed R3 edge is the converse. This campaign is admitted only as one indivisible
attempt at the following endpoint:

```lean
theorem riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg
    (hLi : forall n : Nat, 0 <= (liCoefficientCandidate n).re) :
    RiemannHypothesis

theorem riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg :
    RiemannHypothesis <->
      forall n : Nat, 0 <= (liCoefficientCandidate n).re
```

The project index remains shifted by one: `liCoefficientCandidate n` is classical
`lambda_(n+1)`. No phase-recurrence lemma, transformed-zero extremum, tail estimate, or reality
lemma counts as a successful campaign by itself.

## Source Reconstruction

- Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's Criterion for the Riemann
  Hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI
  `10.1006/jnth.1999.2392`, proves a general multiset criterion under a weighted reciprocal
  summability hypothesis.
- Jeffrey C. Lagarias, *Li Coefficients for Automorphic L-Functions*, Annales de l'Institut
  Fourier 57 (2007), 1689-1740, DOI `10.5802/aif.2311`, Theorem 2.4, records equivalence of RH,
  all-index real-part nonnegativity, subexponential lower bounds, and root growth.
- Alina Bucur, Anne-Maria Ernvall-Hytonen, Almasa Odzak, and Lejla Smajlovic, *On a Li-type
  criterion for zero-free regions of certain Dirichlet series with real coefficients*, LMS
  Journal of Computation and Mathematics 19 (2016), 259-280, DOI
  `10.1112/S1461157016000115`, Theorem 3.3, writes out the maximal transformed-zero proof,
  the strict modulus gap, the far/near tail split, and the simultaneous Diophantine phase step.

The source proof takes transformed zeros of maximal modulus, separates them from the remaining
zeros by a strict gap, shows the remaining contribution is a polynomial factor times a strictly
smaller exponential, and chooses arbitrarily large even indices for which every maximal phase is
close to `1`. The resulting Li coefficient has a negative real part of exponential size.

## Project-Specialized Discovery

The source arranges maximal zeros into real points and conjugate pairs and then writes a cosine
sum. The project does not need that extra divisor permutation. For a finite maximal set, normalize
each dominant transformed value to `Complex.Circle`; compactness of the finite product of circles
gives an unbounded even subsequence on which all normalized powers return simultaneously to `1`.
This aligns arbitrary phases directly and therefore needs only the already compiled reflection
equivalence `rho |-> 1-rho`.

For `rho != 0,1`, put

```text
q(rho) = 1 - 1/rho,
orbitRadius(rho) = max |q(rho)| |q(rho)^(-1)|.
```

Reflection sends `q` to `q^(-1)`. An off-critical zero gives `orbitRadius > 1`; conversely,
`orbitRadius <= 1` forces `Re(rho)=1/2`. Since `q(rho)` and its inverse tend to `1` as
`|rho| -> infinity` inside the critical strip, any radius above `1` is attained on a finite
multiplicity-bearing divisor subset.

## Candidate Generation And Falsification

At most five candidates were considered.

### C1: project-specialized maximal-orbit Bombieri-Lagarias argument

Proposed result: prove the exact endpoint above using the existing paired zero formula, divisor
reflection, local finiteness, and squared reciprocal summability.

Adversarial tests:

- `q=R>1`: the coefficient contains `1-R^m` and is eventually negative.
- `q=-R`: odd indices can hide the sign, so the selected subsequence must be even.
- finitely many unrelated complex phases: termwise sign fails, so simultaneous recurrence is
  required; alignment of only one phase is insufficient.
- no a priori largest transformed zero: `q(rho) -> 1` at large height and compact-local divisor
  finiteness must be used to prove attainment, not assumed.
- a growing near-zero set: its cardinality must be controlled from the compiled
  `sum |rho|^(-2)`, while the far set must use a quadratic binomial remainder.
- the fixed point `rho=1/2`: its orbit radius is `1` and it cannot enter a maximal set with
  radius greater than `1`.

Decision: **SELECTED**. It survives the tests and reuses the exact strongest infrastructure in the
current project.

### C2: positivity implies the root-growth condition directly

Proposed result: derive `limsup |lambda_n|^(1/n) <= 1` from `Re(lambda_n) >= 0`.

Falsification: nonnegative sequences can grow exponentially, for example `lambda_n=2^n`.
Positivity alone gives no such upper bound.

Decision: rejected.

### C3: Pringsheim power-series route

Proposed result: identify the Li generating series with the transformed xi logarithmic derivative,
use nonnegative coefficients and Pringsheim's theorem to force any finite convergence radius to be
a positive-real singularity, and contradict the zero-free half-plane `Re(s)>1`.

Falsification: the mathematical route survives finite and boundary tests, but pinned Mathlib has no
Pringsheim theorem. The campaign would additionally need the generating-series identity, a formal
nonnegative-coefficient boundary-singularity theorem, analytic continuation of the logarithmic
derivative, and nonremovability at transformed xi zeros.

Decision: deferred; its first formal edge is larger than C1.

### C4: generic Bombieri-Lagarias theorem for arbitrary multisets

Proposed result: first formalize the full abstract multiset theorem and then instantiate it with the
xi divisor.

Falsification: no mathematical counterexample under the published weighted summability hypothesis,
but the abstraction adds convergence conventions, arbitrary half-plane parameters, and multiset
bookkeeping that the project endpoint does not need.

Decision: deferred as over-broad for the fixed edge.

### C5: Weil test-function positivity

Proposed result: bypass Li asymptotics through the complete Weil explicit-formula criterion.

Falsification: no local counterexample, but the project still lacks the complete admissible test
space, exact explicit formula, and density/closure argument. This is a distinct larger route, not a
smaller proof of the current edge.

Decision: deferred to R5.

## Required Lean Dependency Chain

The selected batch must close all of the following together:

1. Prove the exact geometry
   `|1-1/rho| <= 1 <-> 1/2 <= Re(rho)` and its reflected inverse form.
2. Derive nontrivial-zero reflection and `0 < Re(rho) < 1` from the compiled xi functional
   equation; do not add a strip-location premise.
3. Define a reflection-invariant orbit radius and prove that any off-line zero yields radius
   strictly greater than `1`.
4. Use `divisorZeroIndex0_norm_le_finite` to prove that a radius greater than `1` has a nonempty
   finite maximal set and a strict smaller bound on its complement.
5. Prove simultaneous return for a finite family in `Complex.Circle` along arbitrarily large even
   powers. The intended proof uses compact sequential convergence of powers in a finite product,
   not numerical angle approximation.
6. Split the complement at scale proportional to the Li index. Bound the far part by the
   quadratic binomial remainder and the near part by squared reciprocal summability plus the
   strict radius gap.
7. Show the complement is `o(R^m)` while the aligned maximal contribution has a fixed negative
   multiple of `R^m` in real part.
8. Rewrite through
   `liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm`, contradict `hLi`, and obtain
   `RiemannHypothesis` via reflection.
9. Combine with the already compiled RH-forward theorem to prove the exact iff.

## Assumption And Strength Audit

The selected endpoint is RH-equivalent. This is permitted because the campaign is formalizing a
known criterion, not inserting it as an assumption. Every premise of every helper must be
discharged from existing unconditional xi/divisor theorems or from the sole endpoint hypothesis
that all Li coefficient real parts are nonnegative.

Forbidden premises include RH, zero simplicity, an ordering or enumeration of zeros, a largest
zero assumption, a prepackaged spectral gap, unproved zero counts, numerical phase alignment,
Pringsheim's theorem, and any subexponential Li bound stronger than the stated positivity
hypothesis.

Novelty classification if successful:
`KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`.

## Indivisible Stop Conditions

The campaign succeeds only if the exact reverse theorem and iff compile together with target and
axiom audits. Otherwise:

- failure to obtain a finite attained maximum closes `EXTREMAL_ZERO_GAP_IDENTIFIED`;
- failure of the compact simultaneous-return proof closes `FINITE_PHASE_RECURRENCE_GAP_IDENTIFIED`;
- failure to make the complement `o(R^m)` closes `BOMBIERI_LAGARIAS_TAIL_GAP_IDENTIFIED`;
- helpers compiling without the reverse endpoint closes `NO_PROGRESS` for this campaign;
- discovery of a false estimate records a compiled counterexample and closes
  `CONJECTURE_FALSIFIED` or `BRANCH_ELIMINATED` as appropriate.

A local stop returns the persistent RH goal to `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; it does not
pause the global goal.

## Verification Gates

1. The new module and all exact target checks compile with no `sorry`.
2. `#print axioms` for the reverse theorem and iff contains only standard audited dependencies.
3. The full project build passes without resource relaxation.
4. Forbidden-token, explicit-axiom, `native_decide`, and placeholder scans pass.
5. `git diff --check` passes.
6. Research logs distinguish a known criterion formalization from an unconditional proof of RH.

## Local Result

Date: 2026-07-15

All indivisible endpoint and verification gates pass locally. The exact reverse theorem and iff
compile in `LeanLab/Riemann/LiReverseCriterion.lean`, and the selected declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

The implementation refines source steps 4, 6, and 7 without strengthening any premise. For an
arbitrary off-line orbit radius `R0>1`, it chooses `c=(1+R0)/2`; the complete superlevel
`{p | c <= orbitRadius p}` is finite and phase-aligned, while the whole complement is bounded at
once by `m^2*c^m` times the fixed reciprocal-square tsum. Thus no attained global maximum and no
index-dependent far/near split are needed. Polynomial-versus-exponential domination with `c<R0`
then gives the strict contradiction.

Classification:
`KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`, `hard_gap_delta=1`.
L2/G5 is locally complete. The assumption frontier changes only from an unformalized to a compiled
equivalence: neither RH nor all-index Li nonnegativity is proved unconditionally. The persistent RH
goal remains active. Publication and public CI remain pending.
