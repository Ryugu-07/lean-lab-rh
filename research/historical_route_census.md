# Historical RH Route Census

Date: 2026-07-16

Status: `ACTIVE_ATLAS_INPUT`

This is a route map, not a ranking of authors and not a promise to formalize every route. Its time
horizon is 1859 to the present. The purpose is to prevent recency bias, repeated same-route work,
and selection by isolated proof claims.

Current authority is [`rh_governance_current.md`](rh_governance_current.md). Under V4.1 this census
informs value-ranked `ROUTE_SELECTION`; it is not a proof-admission gate. RH and every open route
remain directly attackable.

Coverage labels:

- `UNMAPPED`: no source-faithful route card yet;
- `MENTION_ONLY`: named in the portfolio but no complete frontier audit;
- `PARTIAL`: some mechanisms or counterexamples audited;
- `SOURCE_ALIGNED`: exact route statement and first gap are checked;
- `DEEP_FORMALIZATION`: major exact results are compiled in Lean.

## Initial Census

| route_id | priority | route family | RH strength | current coverage | next census deliverable |
| --- | --- | --- | --- | --- | --- |
| H0 | CANONICAL | Riemann's xi function, functional equation, explicit formula, and prime-counting error terms | EQUIVALENT / FOUNDATION | DEEP_FORMALIZATION / CHEBYSHEV_MELLIN_EVIDENCE_PUBLIC_GREEN | Campaign `LITERATURE-20260728-H0-CHEBYSHEV-MELLIN-01`, frozen implementation `0ff8a577cb4eb247d6cfdbc03d82a5d7dd36707e` and immutable evidence `f038d09b6e3f8d337a59472d4eb8175e48e6f6d1`, compiles the exact `psi`/von Mangoldt partial sum, the `Re(s)>1` Mellin and `-zeta'/zeta` identities, and the cancellation-preserving ordered Dirichlet bridge from any `psi(N)-N=O(N^r)` hypothesis to `Re(s)>r`. An alternating control proves that this ordered convergence cannot be identified with Mathlib's absolute `LSeriesSummable`. The RH-strength error estimate, local uniform continuation, reverse zero exclusion, H0, and RH remain open. |
| H1 | CANONICAL | Classical critical-line methods: Hardy-Littlewood, Selberg, Levinson-Conrey mollifiers, critical-zero proportions | PARTIAL_PROGRESS | DEEP_FORMALIZATION / SELBERG_LOCAL_PRODUCER_EVIDENCE_PUBLIC_GREEN | Operational audit splits the compressed H1 row into Hardy--Littlewood oscillation, Selberg's 1942 squared-root-mollifier sign-change method, and Levinson--Conrey's off-line argument-principle method. Campaign `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01` compiles the actual local integral-gap detector, strict-sign transport through the nonnegative square, actual critical-line zeta-zero production, finite injective assembly, and an arbitrary-multiplier control; frozen implementation and immutable evidence are public-green. Selberg's global moment production, the Hardy Abel law, every quantitative critical-zero count and proportion, H1, and RH remain open. |
| H2 | CANONICAL | Zero-free regions, zero-density estimates, moments, mean values, subconvexity, and Lindelof-type bounds | RH_IMPLIED / PARTIAL_PROGRESS | DEEP_FORMALIZATION / CLASSICAL_DETECTOR_MELLIN_PARTIAL | Campaign `LITERATURE-20260729-H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01` compiles the common Ingham--Huxley/Maynard--Pratt/Guth--Maynard entry mechanism through the exact truncated-Mobius coefficient gap, actual zeta-product L-series, exponential smoothing, full forward Mellin transform, removable Gamma-pole cancellation at an actual zeta zero, retained translated-zeta residue, and a cardinality-audited finite detector. The first unavailable theorem is `ClassicalDetectorInverseMellinLine`; the infinite contour shift, horizontal-edge decay, shifted detector identity, Type-I/Type-II counts, large-value estimates, density exponents, actual-zeta bow exclusion, H2, and RH remain open. |
| H3 | CANONICAL | Nyman-Beurling and Baez-Duarte Hilbert-space closure criteria | EQUIVALENT | DEEP_FORMALIZATION | Consolidated route card from the compiled criterion through Burnol's obstruction to the still-open unconditional approximation edge. |
| H4 | CANONICAL | Li/Keiper coefficients and Bombieri-Lagarias transformed-zero criteria | EQUIVALENT | DEEP_FORMALIZATION | External source audit of the project-specific all-index reverse theorem and a clean statement crosswalk. |
| H5 | CANONICAL | Weil explicit formula, test-function algebra, and positivity criteria | EQUIVALENT | DEEP_FORMALIZATION | Freeze the full admissible class and isolate the one canonical unconditional positivity gap; reclassify fixed-test subedges as infrastructure. |
| H6 | CANONICAL | de Bruijn-Newman heat flow and zero dynamics | EQUIVALENT | DEEP_FORMALIZATION | The source card plus completed H6 campaigns cover the exact heat family, threshold theory, strip contraction, zero dynamics, finite heat-Li signs, the TP2/PF5 boundary, and Boyd asymptotics; `Lambda = 0` remains open. |
| H7 | CANONICAL | Hilbert-Polya, self-adjoint operators, trace formulae, and noncommutative geometry | STRUCTURAL_ANALOGY / POTENTIAL EQUIVALENCE | SOURCE_ALIGNED | [`door_atlas_ranked_20260722.md`](door_atlas_ranked_20260722.md) now separates the compiled finite matrix/certificate interface, the open scalar Herglotz even-simplicity inequality, and the later true-ground-state convergence edge. |
| H8 | CANONICAL | Entire-function geometry: Laguerre-Polya class, Jensen polynomials, de Branges/canonical systems | EQUIVALENT / STRUCTURAL_ANALOGY | DEEP_FORMALIZATION / RKHS_UPPER_HALF_PLANE_PUBLIC_GREEN | The generic Jensen eventual-to-global promotion is formally falsified, Suzuki's proposed reciprocal-log-derivative limit has a compiled regularity/pole audit, and frozen implementation `462c88ad1f80772e9485ce224e16e63c9fd39e8e` reconstructs the complete upper-half-plane producer in Conrey--Li Theorem 2: arbitrary finite shifted-kernel positivity, ratio real-part nonnegativity, and Cayley contraction. The concrete actual-xi RKHS/positive shift operator and the second Hardy-RKHS continuation to `Im z > -1/2` remain open. |
| H9 | CANONICAL | Arithmetic equivalents: Riesz exponential smoothing, Mertens and Chebyshev error terms, Redheffer matrices, Pólya/Turán Liouville sums, Robin/Lagarias divisor-sum inequalities, Farey-type criteria, Conrey character sums | EQUIVALENT / FAILED STRENGTHENINGS | DEEP_FORMALIZATION / CONREY_SEVEN_FLAT_IMMUTABLE_EVIDENCE_GREEN | Redheffer determinant final ledger `6dfb8689243824598d865c911f64c46a0dc8de18`, characteristic-polynomial final ledger `2799ec66850919db744026ae58aaea4c2bd2f769`, Riesz Mellin-boundary final ledger `18110c4a553e710fcb67fbe5617562fc573eca45`, and Farey transform final ledger `8a84e18a30e95bf1be423a949438deb0fdfafabb` are public-green. Farey Lean compiles pair normalization and the exact Mertens transform. The Conrey generic rationality-gap audit is public-green; campaign `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01` compiles the actual `q=7` Legendre Fourier series as identically zero on `[3/7,4/7]`, with an irrational zero and strict `7 mod 8` scope; frozen implementation and immutable evidence are public-green. The source-permitted `3 mod 8` flat-branch repair, ordered Franel discrepancy, every RH-equivalent estimate, Mertens growth, non-unit Redheffer estimates, Riesz decay and continuation, H9, and RH remain open. |
| H10 | CANONICAL | Function-field analogues, Bombieri-Stepanov, Frobenius/cohomology, Weil conjectures, and Deligne weights | STRUCTURAL_ANALOGY | SOURCE_ALIGNED | The finite power-sum rigidity theorem is public; campaign `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01` now tests whether ordinary summable power traces are compatible with nonzero reciprocal pairing after countable infinite transfer. |
| H11 | SUPPORTING | Zero statistics, Montgomery pair correlation, random-matrix models, and quantum chaos | CONDITIONAL / PARTIAL_PROGRESS | SOURCE_ALIGNED / EXACT_BOUNDARY_EVIDENCE_PUBLIC_GREEN | The horizontal-multiplicity consumer, finite triangular mass, and exact moving-window overlap now compile. Frozen implementation `4bf9342866283d3b8d07f275ca8199e52413fd0b` and immutable evidence `ed2a400a98ca543d3a2795a80ea08544bcbb5df6` preserve a nonnegative local top-boundary remainder, its `U*boundaryCount^2` bound, and a loss-free one-sided inequality. Only termwise full triangular replacement at `T+U` is falsified, not the source's `O(L^2)` proposition. PCC, Fujii's second moment, absolute-error strength, sparse-exception amplification, H11, and RH remain open. |
| H12 | SUPPORTING | Speiser-type derivative criteria, value distribution, and complex dynamics | EQUIVALENT / PARTIAL_PROGRESS | SOURCE_ALIGNED | The ranked atlas fixes the left-half-strip `zeta'` exclusion edge and its possible role as an exceptional-zero localizer. |
| H13 | SUPPORTING | Generalized zeta/L-functions and automorphic transfer | STRUCTURAL_ANALOGY / GENERALIZATION | DEEP_FORMALIZATION | The exact modulus-one Dirichlet-family equivalence, all-family implication, zeta-factor transfer, and extra-factor obstruction now compile; actual generalized RH and p-adic/archimedean individual-zeta transfer remain open. |
| H14 | SUPPORTING | Rigorous computation and finite-height zero verification | FINITE_VERIFICATION | DEEP_FORMALIZATION / TURING_COMPLETENESS_CONSUMER_COMPILED | The arbitrary-height symmetric finite-orbit theorem compiles, so finite verification plus the two basic zeta symmetries cannot alone promote to a global claim. Campaign `LITERATURE-20260729-H14-TURING-COMPLETENESS-CONSUMER-01` compiles the complementary positive mechanism: actual multiplicity-bearing xi divisor candidates plus an exact rectangle argument-principle count imply finite completeness and critical-line location throughout that rectangle. Interval root isolation, Turing's average bound, every concrete certified height, the global tail reduction, and RH remain open. |

An independent auditor may add a route only with a primary-source anchor and a reason it is not a
subroute of an existing row. Renaming a route does not create a new campaign slot.

## Required Route Card

Each `CANONICAL` row must receive a separate route card containing:

1. exact mathematical endpoint and relation to standard RH;
2. original/canonical source and at least one later substantial development;
3. strongest unconditional theorem currently known in the route;
4. first unproved edge on every claimed path to RH;
5. assumptions equivalent to, stronger than, or suspiciously close to RH;
6. known counterexamples, saturation results, or expert negative assessments;
7. reusable project infrastructure and missing mathlib prerequisites;
8. three model-generated conjectures: bridge, quantitative, and cross-route;
9. adversarial tests for each conjecture;
10. recommendation `FORMALIZE`, `DISCOVERY`, `MONITOR`, `HEURISTIC_ONLY`, or `PROOF-ATTEMPT`.

## Initial Primary-Source Anchors

These anchors seed the census. They do not replace the route-card source audit.

- H0: Bernhard Riemann, *On the Number of Prime Numbers less than a Given Quantity* (1859),
  [Clay translation](https://www.claymath.org/wp-content/uploads/2023/04/Wilkins-translation.pdf);
  Enrico Bombieri, [official Clay problem description](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).
- H1: N. Levinson, *More than one third of the zeros of Riemann's zeta-function are on
  sigma=1/2*, Advances in Mathematics 13 (1974), 383-436; J. B. Conrey,
  [*More than two fifths of the zeros of the Riemann zeta function are on the critical line*](https://eudml.org/doc/153151),
  J. reine angew. Math. 399 (1989), 1-26.
- H3: L. Baez-Duarte,
  [*A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis*](https://arxiv.org/abs/math/0202141)
  (2002/2003).
- H4: X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, J. Number
  Theory 65 (1997), 325-333; E. Bombieri and J. C. Lagarias,
  [*Complements to Li's Criterion for the Riemann Hypothesis*](https://math.lsa.umich.edu/~lagarias/doc/bombieri.ps)
  (1999).
- H5: A. Weil, *Sur les formules explicites de la theorie des nombres premiers* (1952). Later
  source normalization must be tied to the exact test class used by the project.
- H6: B. Rodgers and T. Tao,
  [*The de Bruijn-Newman constant is non-negative*](https://arxiv.org/abs/1801.05914)
  (2018/2020), with de Bruijn and Newman treated as the canonical predecessors.
- H7: A. Connes,
  [*Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*](https://arxiv.org/abs/math/9811068)
  (1998); L. de Branges,
  [*The Riemann hypothesis for Hilbert spaces of entire functions*](https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society-new-series/volume-15/issue-1/The-Riemann-hypothesis-for-Hilbert-spaces-of-entire-functions/bams/1183553352.short)
  (1986).
- H8: M. Griffin, K. Ono, L. Rolen, and D. Zagier,
  [*Jensen polynomials for the Riemann zeta function and other sequences*](https://arxiv.org/abs/1902.07321)
  (2019); D. Farmer,
  [*Jensen polynomials are not a plausible route to proving the Riemann Hypothesis*](https://arxiv.org/abs/2008.07206)
  (2020/2022), as required negative evidence.
- H9: J. C. Lagarias,
  [*An Elementary Problem Equivalent to the Riemann Hypothesis*](https://arxiv.org/abs/math/0008177)
  (2000/2002).
- H10: P. Deligne,
  [*La conjecture de Weil I*](https://publications.ias.edu/book/export/html/368), Publications
  Mathematiques de l'IHES 43 (1974), 273-308.
- H11: H. L. Montgomery,
  [*The pair correlation of zeros of the zeta function*](https://websites.umich.edu/~hlm/paircor1.pdf)
  (1973). Its headline analysis assumes RH and must not be used as an unconditional RH premise.

## Census Completeness Criteria

The census is complete only when:

- every `CANONICAL` row is at least `SOURCE_ALIGNED`;
- a clean-context review checks whether a major historical route family is missing;
- the project records a three-route shortlist with a common scoring rubric;
- the shortlist contains at least one classical analytic route and at least one structural route;
- any re-entry into a previously exhausted route states its materially new attack angle;
- all exact-equivalence routes state why proving another equivalent reformulation does or does not
  make the unconditional direction easier.

These criteria measure atlas coverage. Incomplete coverage does not suspend the global Goal or
block a separately preregistered proof attempt.

## 2026-07-22 Historical Door Survey completion

[`door_atlas_ranked_20260722.md`](door_atlas_ranked_20260722.md) supplies the common source-backed
card schema for every H0-H14 family and adds a distinct countermodel control card. The census is
now complete within its stated 2026-07-22 source boundary. This is auditable coverage, not a claim
that no historical paper or future route exists.

The selected opening is the H5/H7 finite-prime Weil ground-state program introduced in the
2025-2026 Connes sources. Its real-zero approximant theorem is proved in the cited source; simple
even ground states and convergence to the Riemann xi transform remain open. H1's 2025
short-mollifier derivative-combination optimization is the runner-up, with both long mean values
and the sparse-exception barrier still operative. `rh_frontier_delta=0`.
