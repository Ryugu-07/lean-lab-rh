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
| H2 | CANONICAL | Zero-free regions, zero-density estimates, moments, mean values, subconvexity, and Lindelof-type bounds | RH_IMPLIED / PARTIAL_PROGRESS | SOURCE_ALIGNED | [`route_card_H2_density_moments_20260717.md`](route_card_H2_density_moments_20260717.md) separates zero-free, density, moment, and subconvexity strengths and audits three candidates. |
| H3 | CANONICAL | Nyman-Beurling and Baez-Duarte Hilbert-space closure criteria | EQUIVALENT | DEEP_FORMALIZATION | Consolidated route card from the compiled criterion through Burnol's obstruction to the still-open unconditional approximation edge. |
| H4 | CANONICAL | Li/Keiper coefficients and Bombieri-Lagarias transformed-zero criteria | EQUIVALENT | DEEP_FORMALIZATION | External source audit of the project-specific all-index reverse theorem and a clean statement crosswalk. |
| H5 | CANONICAL | Weil explicit formula, test-function algebra, and positivity criteria | EQUIVALENT | DEEP_FORMALIZATION | Freeze the full admissible class and isolate the one canonical unconditional positivity gap; reclassify fixed-test subedges as infrastructure. |
| H6 | CANONICAL | de Bruijn-Newman heat flow and zero dynamics | EQUIVALENT | SOURCE_ALIGNED | [`route_card_H6_de_bruijn_newman_20260717.md`](route_card_H6_de_bruijn_newman_20260717.md) fixes `0 <= Lambda <= 0.22`, the exact `Lambda = 0` edge, and three audited candidates. |
| H7 | CANONICAL | Hilbert-Polya, self-adjoint operators, trace formulae, and noncommutative geometry | STRUCTURAL_ANALOGY / POTENTIAL EQUIVALENCE | PARTIAL | Separate proved spectral realizations and trace identities from the missing positivity, self-adjointness, or full zero-spectrum correspondence. |
| H8 | CANONICAL | Entire-function geometry: Laguerre-Polya class, Jensen polynomials, de Branges/canonical systems | EQUIVALENT / STRUCTURAL_ANALOGY | MENTION_ONLY | Record exact equivalences, eventual finite-degree hyperbolicity results, known insufficiency warnings, and the first non-tautological global edge. |
| H9 | CANONICAL | Arithmetic equivalents: Mertens and Chebyshev error terms, Robin/Lagarias divisor-sum inequalities, Farey-type criteria | EQUIVALENT | UNMAPPED | Compare which forms expose a usable quantitative mechanism and which merely restate RH in harder arithmetic clothing. |
| H10 | CANONICAL | Function-field analogues, Bombieri-Stepanov, Frobenius/cohomology, Weil conjectures, and Deligne weights | STRUCTURAL_ANALOGY | UNMAPPED | Build an early Bombieri-Stepanov proof card, then map the exact ingredient that forces the finite-field critical line and explain the number-field transfer gap. |
| H11 | SUPPORTING | Zero statistics, Montgomery pair correlation, random-matrix models, and quantum chaos | HEURISTIC_ONLY / CONDITIONAL | MENTION_ONLY | Separate conditional theorems and numerical laws from statements capable of excluding a single off-line zero. |
| H12 | SUPPORTING | Speiser-type derivative criteria, value distribution, and complex dynamics | EQUIVALENT / PARTIAL_PROGRESS | UNMAPPED | Exact criterion, derivative-zero frontier, and relation to existing xi divisor infrastructure. |
| H13 | SUPPORTING | Generalized zeta/L-functions and automorphic transfer | STRUCTURAL_ANALOGY / GENERALIZATION | UNMAPPED | Identify which mechanisms are specific to zeta and which survive for Selberg-class or automorphic L-functions. |
| H14 | SUPPORTING | Rigorous computation and finite-height zero verification | FINITE_VERIFICATION | UNMAPPED | State certified scope, interfaces useful to analytic bounds, and the prohibition on finite-to-global promotion. |

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
