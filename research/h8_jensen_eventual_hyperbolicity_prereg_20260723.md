# H8 Jensen Eventual-Hyperbolicity Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H8-JENSEN-EVENTUAL-HYPERBOLICITY-01`

Selected node: `H8-JENSEN-EVENTUAL-NOT-GLOBAL-01`

Status: `IMPLEMENTATION_CI_PASSED / EVIDENCE_COMMIT_REQUIRED`

## Selection reason

The H11 horizontal-multiplicity campaign is publicly closed at its finite-hinge and
sparse-exception-model endpoint. Fresh cross-family selection compared H2 zero density, the H7
true-ground-state limit, and H8 Jensen/Laguerre--Polya.

H2's generic finite-or-sparse exception gap is already represented by the compiled H11 model, so
another density-exponent consumer would duplicate the same obstruction without a new localizer.
H7 has already received three consecutive definition-alignment and finite spectral campaigns; its
next step is the difficult arithmetic scalar inequality or infinite ground-state limit. H8 has a
complete literature card but no theorem-producing project campaign, making it the best breadth
correction under the historical omission-search ruling.

The primary-source search found no 2025--2026 theorem controlling Jensen degree and shift
uniformly. It did find an atlas omission: Duran's 2024 Brenke-polynomial framework supplies further
RH-equivalent real-rootedness criteria, but no all-index real-rootedness proof. This strengthens the
need to separate new equivalent polynomial families from an actual uniform mechanism.

## Locked primary sources

1. Michael Griffin, Ken Ono, Larry Rolen, and Don Zagier, "Jensen polynomials for the Riemann zeta
   function and other sequences," arXiv:1902.07321.
   <https://arxiv.org/abs/1902.07321>
2. Michael Griffin, Ken Ono, Larry Rolen, Jesse Thorner, Zachary Tripp, and Ian Wagner, "Jensen
   Polynomials for the Riemann Xi Function," arXiv:1910.01227.
   <https://arxiv.org/abs/1910.01227>
3. David W. Farmer, "Jensen polynomials are not a viable route to proving the Riemann
   Hypothesis," arXiv:2008.07206.
   <https://arxiv.org/abs/2008.07206>
4. Antonio J. Duran, "Brenke polynomials with real zeros and the Riemann Hypothesis,"
   arXiv:2405.18940.
   <https://arxiv.org/abs/2405.18940>

The first two sources establish eventual hyperbolicity for each fixed degree and explain that the
RH criterion still requires every degree and every shift. Farmer supplies the source-level
universality and detection-efficiency critique. Duran extends the space of equivalent polynomial
criteria; no equivalence is used as an unproved premise.

## Exact logical gap

For a coefficient sequence `a`, the degree-`d`, shift-`n` Jensen polynomial uses only the finite
window `a(n), ..., a(n+d)`. The source asymptotics have quantifier order

`forall d, exists N(d), forall n >= N(d), hyperbolic (J(d,n))`.

The RH-bearing criterion has the stronger order

`forall d, forall n, hyperbolic (J(d,n))`.

The campaign will kernel-check one sequence for which the first statement holds, every prescribed
finite initial wedge can be made indistinguishable from an all-hyperbolic sequence, but the second
statement fails at one explicit degree-two window.

## Fixed Lean endpoint

Create `LeanLab/Riemann/JensenEventualHyperbolicity.lean` and compile all of the following without
placeholders:

1. Define the Jensen polynomial of a real coefficient sequence by
   `sum j=0..d, choose(d,j) * a(n+j) * X^j`.
2. Define a root-based predicate saying every complex root of a real polynomial has zero imaginary
   part. Prove the all-one sequence has Jensen polynomial `(1+X)^d` and satisfies the predicate.
3. For each defect location `m+1`, define a sequence equal to one everywhere except at that index,
   where it is zero.
4. Prove every Jensen window with `n+d <= m` agrees with the all-one model. Thus any prescribed
   finite initial wedge can pass exact hyperbolicity checks before the defect.
5. Prove that for every fixed degree, all sufficiently large shifts lie past the defect and have
   only real roots.
6. Prove the degree-two polynomial at shift `m` is `1+X^2`, has the nonreal complex root `I`, and
   therefore the all-degree/all-shift conclusion is false.

Proposed declaration names:

- `jensenPolynomial`
- `JensenHasOnlyRealRoots`
- `jensenPolynomial_const_one`
- `jensenSingleDefectCoefficients`
- `jensenSingleDefect_finiteWedge`
- `jensenSingleDefect_eventually_hasOnlyRealRoots`
- `not_jensenSingleDefect_all_hasOnlyRealRoots`

Names may change to fit the polynomial API, but the finite-wedge and eventual-fixed-degree
quantifiers may not be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires all six endpoint blocks, exact TargetChecks, selected standard-only axiom
prints, an empty forbidden scan, full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the exact window-locality theorem and the explicit future nonreal
root, plus the first precise API obstruction to the eventual quantifier theorem.

`SOURCE_FALSIFIED` would require a counterexample to a cited source theorem under its exact xi
coefficient and normalization hypotheses. The planned model does not seek or claim this.

## Claim boundary

- The defect sequence is a generic coefficient model, not the xi Taylor sequence.
- The model does not refute eventual fixed-degree hyperbolicity; it satisfies that property.
- The model does not refute the Jensen--Polya equivalence; it falsifies only promotion from
  eventual fixed-degree or finite-wedge checks to the all-index conclusion.
- Duran's Brenke criteria are recorded as additional equivalences, not RH progress.
- No numerical root computation is a premise.
- No H8 theorem becomes an RH premise unless it is proved for the actual xi coefficients and has
  the required all-degree/all-shift quantifiers.

## Mechanical gates

Before proof-source editing:

- publish this preregistration and require public Lean Action CI;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register exact Targets and TargetChecks;
- print selected transitive axioms;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- run `git diff --check`, the module build, full build, and public CI;
- record the exact source and model definition alignment.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL` at an exact API obstruction,
`SOURCE_FALSIFIED`, or proof that the endpoint already exists in the project. Local stop returns
the persistent RH Goal to the unfinished historical atlas. H8 remains open unless an actual
all-index xi theorem is proved or the route is mathematically ruled out. Original conjecture and
direct RH attempts remain open throughout.

## Implementation result

Preregistration commit `0275ab15b83a253b9a4eb9fcfa4a575943b89b33` passed public Lean Action
run `29949869070`, build job `89024569873`, in `1m54s` before proof-source editing.

All six fixed endpoint blocks are locally complete in
`LeanLab/Riemann/JensenEventualHyperbolicity.lean`. The combined theorem
`exists_eventually_realRooted_not_all_realRooted` supplies one coefficient sequence with
fixed-degree eventual real-rootedness but failure of the all-degree/all-shift property. Separate
theorems preserve the arbitrary finite-wedge equality and the exact `1+X^2` witness.

Two Targets, seven exact TargetChecks, and six selected axiom prints compile. The selected axioms
are only `propext`, `Classical.choice`, and `Quot.sound`. This is full success at the registered
generic falsification endpoint, with `rh_frontier_delta=0` and `route_infrastructure_delta=1`.
Actual-xi all-index hyperbolicity and RH remain open. The production forbidden scan is empty,
`git diff --check` passes, the H8 module has no local warning, and the full `8,744`-job build
passes. Frozen implementation commit `ca656cb6e24b5084b403d53e5a3763dc34b642be` passed public Lean
Action run `29950744385`, build job `89027520728`, in `2m4s`. Lean proof source is frozen;
immutable-evidence publication and its own public CI are the next gate.
