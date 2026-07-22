# H11 Pair-Correlation Horizontal-Multiplicity Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H11-PCC-HORIZONTAL-MULTIPLICITY-01`

Selected node: `H11-PCC-HORIZONTAL-MULTIPLICITY-01`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

## Selection reason

The H12 Speiser count-consumer campaign reached its registered local stop and its final-ledger
commit passed public CI. Fresh cross-family selection compared the untested H2 density and H11
statistics families, the partially audited H10 function-field transfer, and the open H7 spectral
limit. H11 is selected because a source development missed by the 2026-07-22 atlas materially
changes the route boundary.

Goldston, Lee, Schettler, and Suriajaya, arXiv:2503.15449v4 (revised 2026-03-30), prove without
assuming RH that their pair-correlation conjecture implies asymptotically 100 percent of zeta
zeros are simple and on the critical line. Their mechanism uses horizontal multiplicity: an
off-line zero and its functional-equation reflection have the same ordinate and therefore create
extra diagonal terms. The source explicitly corrects the earlier statement that pair correlation
provides no horizontal information.

This is a real historical-map correction, but not RH. A finite or density-zero family of off-line
zeros contributes a nonzero horizontal-multiplicity excess while remaining invisible after
normalization by the total zero count. The campaign reconstructs this exact hinge and tests the
last-exception gap rather than treating a proportion-one conclusion as universal zero location.

## Locked primary sources

1. Daniel A. Goldston, Junghun Lee, Jordan Schettler, and Ade Irma Suriajaya,
   "Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I: Simple and Critical
   Zeros," arXiv:2503.15449v4, 2026-03-30.
   <https://arxiv.org/abs/2503.15449v4>
2. Siegfred A. C. Baluyot, Daniel A. Goldston, Ade I. Suriajaya, and Caroline L.
   Turnage-Butterbaugh, "Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of
   Simple Zeros and Critical Zeros," arXiv:2501.14545, revised 2026-03-22.
   <https://arxiv.org/abs/2501.14545>
3. H. L. Montgomery, "The pair correlation of zeros of the zeta function," 1973.
   <https://websites.umich.edu/~hlm/paircor1.pdf>

The first source is the proof spine. The second records the authors' correction of their own 2024
scope statement and the symmetric-diagonal mechanism. No random-matrix heuristic is a premise.

## Source-exact count hinge

For the multiplicity-bearing multiset of zeros with `0 < gamma <= T`, the source defines

- `N(T)`: total zero count;
- `H(gamma)`: number of multiplicity copies on the horizontal line of ordinate `gamma`;
- `N_circ(T) = sum_rho H(im rho)`: ordered equal-ordinate pair count.

The finite combinatorial step is

`N_simple_critical(T) >= 2 * N(T) - N_circ(T)`.

The horizontal multiplicity hypothesis gives `N_circ(T) = (1 + o(1)) T L`, while
Riemann-von Mangoldt gives `N(T) = (1 + o(1)) T L`. Hence the lower bound yields density one of
simple critical zeros. It does not imply that `N_circ(T) - N(T)` vanishes.

The exact last-exception localizer is stronger: if `N_circ(T) = N(T)` at a height containing a
given zero, then every horizontal fiber below that height is a singleton. Functional-equation
reflection then forces each such zero to be simple and to have real part `1/2`.

## Fixed Lean endpoint

Create `LeanLab/Riemann/PairCorrelationHorizontalMultiplicity.lean` and compile all of the
following without placeholders:

1. A finite multiplicity-copy population, its ordinate fiber size, total count, horizontal ordered
   pair count, and simple-critical count.
2. Under a permutation realizing `rho |-> 1 - conj rho`, prove the source inequality in the
   subtraction-free form
   `2 * totalCount <= simpleCriticalCount + horizontalPairCount`.
3. Prove that `horizontalPairCount = totalCount` forces every copy to have singleton ordinate
   fiber and real part `1/2`.
4. Build an explicit reflected family consisting of one persistent off-line pair and `n` distinct
   simple critical points. Prove its total count is `n+2`, horizontal pair count is `n+4`, critical
   count is `n`, both relevant proportions tend to `1`, and an off-line point exists for every
   `n`. This is a Lean countermodel to promoting density one to universal line location from the
   count logic alone.
5. Instantiate the finite definitions on actual positive-height nontrivial zeta zeros, with
   analytic multiplicity, and compile an exact cofinal-count conditional consumer into
   `Mathlib.RiemannHypothesis`. If the current divisor API blocks this instantiation, stop at the
   first exact missing theorem and record it rather than weakening the endpoint.

Proposed declaration names:

- `horizontalMultiplicity`
- `horizontalPairCount`
- `simpleCriticalCount`
- `two_mul_card_le_simpleCriticalCount_add_horizontalPairCount`
- `all_critical_of_horizontalPairCount_eq_card`
- `pccExceptionalModel_horizontalPairCount`
- `pccExceptionalModel_pairRatio_tendsto_one`
- `pccExceptionalModel_has_offLine`
- `riemannHypothesis_of_cofinal_exactHorizontalPairCount`

Names may change to fit local APIs, but the mathematical endpoint may not be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires all five endpoint blocks, exact TargetChecks, a standard-only axiom audit,
forbidden scan, full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires blocks 1-4 and an exact API or analytic obstruction for block 5.

`SOURCE_FALSIFIED` requires a Lean counterexample to the finite source inequality under the exact
reflection and multiplicity hypotheses, or a source-definition mismatch that invalidates the
claimed implication.

The expected countermodel in block 4 falsifies only the stronger inference
"asymptotically 100 percent critical implies RH." It does not falsify the source theorem.

## Known obstacles and claim boundary

- The pair-correlation conjecture itself is unproved and may not be inserted as a project premise.
- The source proves a density-one conclusion, not RH.
- Standard asymptotic error permits a fixed, finite, or sufficiently sparse horizontal excess.
- Functional-equation symmetry alone does not amplify one off-line orbit to positive density.
- A candidate amplification theorem would need arithmetic or Euler-product input and must pass the
  conjecture-admission and countermodel gates before use.
- No result in this campaign changes the unconditional RH frontier unless the exact source
  analytic input or a last-exception amplification theorem is itself proved.

## Mechanical gates

Before proof-source editing:

- publish this preregistration and require public Lean Action CI;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register the exact target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- run the full build and public CI;
- record definition alignment, source version, failures, and the surviving gap.

## Stop and successor rule

Stop this local campaign at the first of:

1. `FULL_SUCCESS`;
2. `MEANINGFUL_PARTIAL` at an exact actual-zeta/divisor API obstruction;
3. `SOURCE_FALSIFIED`;
4. proof that the proposed endpoint duplicates an existing project theorem.

Local stop returns the persistent RH Goal to cross-family historical omission search. The H11
family remains open unless the route itself is mathematically ruled out. Original conjecture and
direct RH attempts remain open throughout.

## Implementation result

The preregistration commit `10c016f9395b7bd3c2c2d4e99c4148471540f31f` passed public Lean
Action run `29945736404`, build job `89010521220`, in `1m35s` before proof-source editing.

All five fixed endpoint blocks are locally complete in
`LeanLab/Riemann/PairCorrelationHorizontalMultiplicity.lean`:

1. the finite multiplicity-copy definitions and source inequality compile;
2. exact pair-count equality forces singleton critical fibers;
3. the persistent off-line-pair model has pair and critical ratios tending to one;
4. the actual positive-height zeta cutoff and reflection permutation compile;
5. zeta and xi analytic multiplicities are proved equal locally, and exact cofinal equality
   conditionally implies `Mathlib.RiemannHypothesis`.

Six exact TargetChecks compile. The six selected axiom prints contain only `propext`,
`Classical.choice`, and `Quot.sound`. This is `FULL_SUCCESS` at the registered infrastructure and
falsification endpoint, with `rh_frontier_delta=0` and `route_infrastructure_delta=1`. PCC, sparse
exception amplification, exact cofinal equality, and RH remain open. The production forbidden
scan is empty, `git diff --check` passes, the H11 module build has no local warning, and the full
`8,743`-job build passes. Public implementation CI is the next gate.
