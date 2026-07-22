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
| H0 | CANONICAL | Riemann's xi function, functional equation, explicit formula, and prime-counting error terms | EQUIVALENT / FOUNDATION | DEEP_FORMALIZATION | Separate classical explicit-formula results from the later Weil-positivity route; map exact prime-error equivalents. |
| H1 | CANONICAL | Classical critical-line methods: Hardy-Littlewood, Selberg, Levinson-Conrey mollifiers, critical-zero proportions | PARTIAL_PROGRESS | SOURCE_ALIGNED | [`route_card_H1_critical_line_mollifiers_20260717.md`](route_card_H1_critical_line_mollifiers_20260717.md) fixes the `>5/12` frontier, density-one insufficiency, and three audited candidates. |
| H2 | CANONICAL | Zero-free regions, zero-density estimates, moments, mean values, subconvexity, and Lindelof-type bounds | RH_IMPLIED / PARTIAL_PROGRESS | LOCAL_IMPLEMENTATION_COMPLETE | [`route_card_H2_density_moments_20260717.md`](route_card_H2_density_moments_20260717.md) now adds Maynard--Pratt's half-isolated detector and bow obstruction; Lean proves the finite-line positive criterion and a critical-reflection-symmetric finite bow countermodel. Actual-zeta bow exclusion remains open. |
| H3 | CANONICAL | Nyman-Beurling and Baez-Duarte Hilbert-space closure criteria | EQUIVALENT | DEEP_FORMALIZATION | Consolidated route card from the compiled criterion through Burnol's obstruction to the still-open unconditional approximation edge. |
| H4 | CANONICAL | Li/Keiper coefficients and Bombieri-Lagarias transformed-zero criteria | EQUIVALENT | DEEP_FORMALIZATION | External source audit of the project-specific all-index reverse theorem and a clean statement crosswalk. |
| H5 | CANONICAL | Weil explicit formula, test-function algebra, and positivity criteria | EQUIVALENT | DEEP_FORMALIZATION | Freeze the full admissible class and isolate the one canonical unconditional positivity gap; reclassify fixed-test subedges as infrastructure. |
| H6 | CANONICAL | de Bruijn-Newman heat flow and zero dynamics | EQUIVALENT | DEEP_FORMALIZATION | The source card plus completed H6 campaigns cover the exact heat family, threshold theory, strip contraction, zero dynamics, finite heat-Li signs, the TP2/PF5 boundary, and Boyd asymptotics; `Lambda = 0` remains open. |
| H7 | CANONICAL | Hilbert-Polya, self-adjoint operators, trace formulae, and noncommutative geometry | STRUCTURAL_ANALOGY / POTENTIAL EQUIVALENCE | SOURCE_ALIGNED | [`door_atlas_ranked_20260722.md`](door_atlas_ranked_20260722.md) now separates the compiled finite matrix/certificate interface, the open scalar Herglotz even-simplicity inequality, and the later true-ground-state convergence edge. |
| H8 | CANONICAL | Entire-function geometry: Laguerre-Polya class, Jensen polynomials, de Branges/canonical systems | EQUIVALENT / STRUCTURAL_ANALOGY | SOURCE_ALIGNED | The generic Jensen eventual-to-global promotion is formally falsified; the atlas now also records Suzuki 2026's finite self-adjoint characteristic functions and audits the regularity/pole boundary of the proposed `z^2*xi/xi'` limit. |
| H9 | CANONICAL | Arithmetic equivalents: Mertens and Chebyshev error terms, Robin/Lagarias divisor-sum inequalities, Farey-type criteria | EQUIVALENT | SOURCE_ALIGNED | The ranked atlas distinguishes equivalent divisor inequalities from Conrey's 2024 character-sum proof program and the Mertens counterexample. |
| H10 | CANONICAL | Function-field analogues, Bombieri-Stepanov, Frobenius/cohomology, Weil conjectures, and Deligne weights | STRUCTURAL_ANALOGY | SOURCE_ALIGNED | The finite power-sum rigidity theorem is public; campaign `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01` now tests whether ordinary summable power traces are compatible with nonzero reciprocal pairing after countable infinite transfer. |
| H11 | SUPPORTING | Zero statistics, Montgomery pair correlation, random-matrix models, and quantum chaos | HEURISTIC_ONLY / CONDITIONAL | SOURCE_ALIGNED | The ranked atlas records that the modern unconditional Montgomery theorem explicitly supplies no on-line/off-line information. |
| H12 | SUPPORTING | Speiser-type derivative criteria, value distribution, and complex dynamics | EQUIVALENT / PARTIAL_PROGRESS | SOURCE_ALIGNED | The ranked atlas fixes the left-half-strip `zeta'` exclusion edge and its possible role as an exceptional-zero localizer. |
| H13 | SUPPORTING | Generalized zeta/L-functions and automorphic transfer | STRUCTURAL_ANALOGY / GENERALIZATION | SOURCE_ALIGNED | Campaign `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01` preregisters the exact modulus-one Dirichlet-family inclusion and the one-way zeta-factor transfer boundary; actual generalized RH and p-adic/archimedean transfer remain open. |
| H14 | SUPPORTING | Rigorous computation and finite-height zero verification | FINITE_VERIFICATION | SOURCE_ALIGNED | The ranked atlas fixes finite certification as a supporting interface and prohibits finite-to-global promotion without an analytic reduction theorem. |

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
