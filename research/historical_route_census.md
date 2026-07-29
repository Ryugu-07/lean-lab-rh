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
| H1 | CANONICAL | Classical critical-line methods: Hardy-Littlewood, Selberg, Levinson-Conrey mollifiers, critical-zero proportions | PARTIAL_PROGRESS | DEEP_FORMALIZATION / HARDY_1914_INFINITY_PUBLICLY_CLOSED | The project compiles Hardy's complete 1914 route to infinitely many actual critical-line nontrivial zeros: equations (1)--(3), all-order actual Xi-integral differentiation, a principal-branch Jacobi cusp transform, all-order tangential theta flatness, the unconditional Abel-moment law, and the sign-amplification consumer. Frozen implementation `75f5c575b2c3f050f0e5703efb5ce6851d97775c` and final ledger `2365765bf5ec9eb155312dce119fe6cccbbbff56` are public-green. The Selberg local detector, short-mollifier variational sufficiency, and Levinson-Siegel step geometry also compile. Quantitative Hardy--Littlewood counts, Selberg's global positive-proportion moments, the actual Levinson--Conrey auxiliary count, sparse-exception exclusion, H1, and RH remain open. |
| H2 | CANONICAL | Zero-free regions, zero-density estimates, moments, mean values, subconvexity, and Lindelof-type bounds | RH_IMPLIED / PARTIAL_PROGRESS | DEEP_FORMALIZATION / CLASSICAL_DETECTOR_DYADIC_DICHOTOMY_LOCAL | The project compiles the common Ingham--Huxley/Maynard--Pratt/Guth--Maynard detector through the exact truncated-Mobius coefficient gap, forward and inverse Mellin transforms, the actual one-pole infinite contour shift, and Maynard--Pratt Appendix C's finite dyadic Type-I/Type-II alternative at the literal rounded source scales. The local endpoint `classicalDetectorDyadicDichotomy_endpoint` includes actual head, far-tail, retained-residue, and logarithmic block-count estimates. The first open source edges are now rarity estimates for the actual Type-I blocks and actual Type-II shifted integrals; density exponents, actual-zeta bow exclusion, H2, and RH remain open. |
| H3 | CANONICAL | Nyman-Beurling and Baez-Duarte Hilbert-space closure criteria | EQUIVALENT | DEEP_FORMALIZATION | Consolidated route card from the compiled criterion through Burnol's obstruction to the still-open unconditional approximation edge. |
| H4 | CANONICAL | Li/Keiper coefficients and Bombieri-Lagarias transformed-zero criteria | EQUIVALENT | DEEP_FORMALIZATION | External source audit of the project-specific all-index reverse theorem and a clean statement crosswalk. |
| H5 | CANONICAL | Weil explicit formula, test-function algebra, and positivity criteria | EQUIVALENT | DEEP_FORMALIZATION | Freeze the full admissible class and isolate the one canonical unconditional positivity gap; reclassify fixed-test subedges as infrastructure. |
| H6 | CANONICAL | de Bruijn-Newman heat flow and zero dynamics | EQUIVALENT | DEEP_FORMALIZATION | The source card plus completed H6 campaigns cover the exact heat family, threshold theory, strip contraction, zero dynamics, finite heat-Li signs, the TP2/PF5 boundary, and Boyd asymptotics; `Lambda = 0` remains open. |
| H7 | CANONICAL | Hilbert-Polya, self-adjoint operators, trace formulae, and noncommutative geometry | STRUCTURAL_ANALOGY / POTENTIAL EQUIVALENCE | SOURCE_ALIGNED / CONNES_PROJECTION_DEFECT_PUBLICLY_CLOSED | [`door_atlas_ranked_20260722.md`](door_atlas_ranked_20260722.md) separates the compiled finite-prime Weil matrix/certificate interface, open scalar Herglotz inequality, and true-ground-state convergence edge. The Berry--Keating `H=xp` half-line entry is publicly closed as a non-L2 mode obstruction. Campaign `LITERATURE-20260729-H7-CONNES-PROJECTION-DEFECT-01` publicly compiles the distinct original Connes trace hinge from Theorem 5 equations `(23)`--`(25)`: exact nesting makes the defect trace a Frobenius norm square, while a dimension-one nonnested control is negative. The actual adèle projections, trace class, distributional Weil limit, full pure continuity, compact-graph Weyl no-go, H7, and RH remain open. |
| H8 | CANONICAL | Entire-function geometry: Laguerre-Polya class, Jensen polynomials, de Branges/canonical systems | EQUIVALENT / STRUCTURAL_ANALOGY | DEEP_FORMALIZATION / CONREY_LI_HALF_STRIP_CONSUMER_PUBLICLY_CLOSED | The generic Jensen eventual-to-global promotion is formally falsified, Suzuki's proposed reciprocal-log-derivative limit has a compiled regularity/pole audit, and frozen implementation `c8605da897d423a7bdab4e4bd49426c482b8f7a5` compiles the Conrey--Li Theorem 2 chain from upper RKHS shift semipositivity through the exact shifted-kernel/Hardy-defect factorization, dense kernel-multiplier extension, adjoint analytic continuation, and pointwise Cayley contraction on `Im z>-1/2`. The abstract consumer campaign is publicly closed, but it assumes rather than constructs the concrete half-strip Hardy RKHS. The actual `F(W)` space, actual-xi positive shift, Cayley-to-`W` continuation step, H8, and RH remain open. |
| H9 | CANONICAL | Arithmetic equivalents: Riesz exponential smoothing, Mertens and Chebyshev error terms, Redheffer matrices, Pólya/Turán Liouville sums, Robin/Lagarias divisor-sum inequalities, Farey-type criteria, Conrey character sums | EQUIVALENT / FAILED STRENGTHENINGS | DEEP_FORMALIZATION / CONREY_SEVEN_FLAT_PUBLICLY_CLOSED | Redheffer determinant final ledger `6dfb8689243824598d865c911f64c46a0dc8de18`, characteristic-polynomial final ledger `2799ec66850919db744026ae58aaea4c2bd2f769`, Riesz Mellin-boundary final ledger `18110c4a553e710fcb67fbe5617562fc573eca45`, and Farey transform final ledger `8a84e18a30e95bf1be423a949438deb0fdfafabb` are public-green. Farey Lean compiles pair normalization and the exact Mertens transform. The Conrey generic rationality-gap audit is public-green; campaign `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01` publicly closes the actual `q=7` Legendre Fourier series as identically zero on `[3/7,4/7]`, with an irrational zero and strict `7 mod 8` scope. The source-permitted `3 mod 8` flat-branch repair, ordered Franel discrepancy, every RH-equivalent estimate, Mertens growth, non-unit Redheffer estimates, Riesz decay and continuation, H9, and RH remain open. |
| H10 | CANONICAL | Function-field analogues, Bombieri-Stepanov, Frobenius/cohomology, Weil conjectures, and Deligne weights | STRUCTURAL_ANALOGY | SOURCE_ALIGNED | The finite power-sum rigidity theorem is public; campaign `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01` now tests whether ordinary summable power traces are compatible with nonzero reciprocal pairing after countable infinite transfer. |
| H11 | SUPPORTING | Zero statistics, Montgomery pair correlation, random-matrix models, and quantum chaos | CONDITIONAL / PARTIAL_PROGRESS | SOURCE_ALIGNED / EXACT_BOUNDARY_EVIDENCE_PUBLIC_GREEN | The horizontal-multiplicity consumer, finite triangular mass, and exact moving-window overlap now compile. Frozen implementation `4bf9342866283d3b8d07f275ca8199e52413fd0b` and immutable evidence `ed2a400a98ca543d3a2795a80ea08544bcbb5df6` preserve a nonnegative local top-boundary remainder, its `U*boundaryCount^2` bound, and a loss-free one-sided inequality. Only termwise full triangular replacement at `T+U` is falsified, not the source's `O(L^2)` proposition. PCC, Fujii's second moment, absolute-error strength, sparse-exception amplification, H11, and RH remain open. |
| H12 | SUPPORTING | Speiser-type derivative criteria, value distribution, and complex dynamics | EQUIVALENT / PARTIAL_PROGRESS | DEEP_FORMALIZATION / LEFT_HALF_PLANE_WINDING_FINAL_LEDGER_PUBLIC_GREEN | The multiplicity-bearing count consumer, paired zero-mass identity, explicit Gamma bridge, vertical signs, local critical-zero indentations, and common zero-free horizontal slices compile. The contour work proves both that nonvanishing alone does not control winding and the exact positive counterpart: a strict left-half-plane path has a principal-log primitive and zero closed-path logarithmic winding. Campaign `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01` also compiles the actual horizontal `zeta'/zeta` derivative and endpoint formula under an explicit strict-negative hypothesis; frozen implementation, immutable evidence, and final ledger are public-green. An actual strict-negative height, the global indented argument principle, Jensen top variation, both analytic count outputs, Speiser equivalence, H12, and RH remain open. |
| H13 | SUPPORTING | Generalized zeta/L-functions and automorphic transfer | STRUCTURAL_ANALOGY / GENERALIZATION | DEEP_FORMALIZATION | The exact modulus-one Dirichlet-family equivalence, all-family implication, zeta-factor transfer, and extra-factor obstruction now compile; actual generalized RH and p-adic/archimedean individual-zeta transfer remain open. |
| H14 | SUPPORTING | Rigorous computation and finite-height zero verification | FINITE_VERIFICATION | DEEP_FORMALIZATION / TURING_COMPLETENESS_CONSUMER_COMPILED | The arbitrary-height symmetric finite-orbit theorem compiles, so finite verification plus the two basic zeta symmetries cannot alone promote to a global claim. Campaign `LITERATURE-20260729-H14-TURING-COMPLETENESS-CONSUMER-01` compiles the complementary positive mechanism: actual multiplicity-bearing xi divisor candidates plus an exact rectangle argument-principle count imply finite completeness and critical-line location throughout that rectangle. Interval root isolation, Turing's average bound, every concrete certified height, the global tail reduction, and RH remain open. |

## 2026-07-30 H1 Hardy--Littlewood finite mean-square selection

The omission search re-enters the 1921 Hardy--Littlewood quantitative critical-line proof at its
finite Dirichlet-polynomial hinge. This is not constant optimization: the source proves the
stronger Lemma 6 estimate `O(N / log N)`, while the subsequent finite Lemma 8 mean-square
argument only needs a universal `O(N)` off-diagonal bound. Campaign
`LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01` preregisters that weakened
kernel estimate, the exact finite norm-square expansion, and a shifted `O(L+N)` polynomial
mean square.

The source's uniform infinite-series truncation, eta-primitive identification, actual source
coordinate second moment, count parameter budget, H1, and RH remain open. H2, H7/H8, H10, H11,
H12, and H14 remain live alternatives after this fixed finite campaign.

## 2026-07-30 H1 Hardy--Littlewood finite mean-square result

The omission test succeeds locally. Lean proves that the finite shifted Dirichlet polynomial has
mean square `O(L+N)` and hence `O(L)` for `N<=L`, using a universal linear near/far
off-diagonal bound. The extra `1/log N` saving in source Lemma 6 is therefore not logically
needed at this finite stage.

This does not close the 1921 route. The first remaining source inference is the uniform
conditional-series truncation in Lemmas 3--4, followed by eta-series identification/error
moment, the actual source-X moment, and the count parameter budget. Other historical families
remain live, and original conjectures remain open at every stage.

The finite campaign's implementation, immutable evidence, and final ledger are public green.
After its closure receipt, selection returns to a fresh cross-family rerank rather than
continuing H1 by inertia.

## 2026-07-30 H1 Hardy--Littlewood eta-to-Theta Abel-transfer selection

After the finite mean-square receipt passed public CI, the portfolio was reranked against H2,
H7/H8, H10, H11, H12, and H14. Those families remain at broad global analytic or object
construction producers. The 1921 Hardy--Littlewood proof instead exposes one exact source edge:
Lemma 4 transfers Lemma 3's uniform eta remainder to the logarithmically weighted Theta series
by discrete Abel summation.

Campaign `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01` selects only that
transfer. It will compile the finite identity, reciprocal-log telescope, Cauchy argument, and
uniform ordered-series remainder under an explicit Lemma 3 hypothesis. It will not claim the
actual eta remainder, primitive identification, infinite-series moment, unconditional linear
count, H1, or RH. This is conditional-convergence reconstruction, not numerical optimization.

## 2026-07-30 H1 Hardy--Littlewood eta-to-Theta Abel-transfer result

The selected source inference succeeds locally. Lean compiles Hardy--Littlewood's reciprocal-log
Abel transform and proves that a uniform `Ceta*N^(-sigma)` eta remainder implies ordered Theta
convergence with a uniform `(2/log 2)*Ceta*N^(-sigma)` remainder. The result is quantified over
arbitrary parameter families, so uniformity is not lost when the limit value varies.

This localizes the first genuine remaining analytic obstacle to Lemma 3 itself. The project
still needs its uniform eta remainder in the source region, then the ordered-series/primitive
identification and error moment, actual source-X moment, and parameter budget. The result is
not an unconditional linear count, H1, or RH.

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

## 2026-07-29 H1 Hardy omission re-entry

The H1 row remains deep but not exhausted. The repository now compiles Hardy's positive-real
Cahen-Mellin equation (1), the source's central complex-alpha equation (2), and the complete
conditional Abel-moment contradiction consumer. Campaign
`LITERATURE-20260729-H1-HARDY-COMPLEX-ALPHA-01` closed the exact equation (1) to equation (2)
transition, including exponential xi integrability on the full source strip, analytic
continuation, theta normalization, branch alignment, evenness, and the identity theorem.

This re-entry is materially different from the preceding H1 campaigns: it neither adds another
conditional consumer nor optimizes a critical-zero percentage. It formalizes the missing known
theorem connecting two compiled endpoints. The subsequent tangential theta derivative limit,
Hardy's unconditional infinitude theorem, quantitative Hardy-Littlewood counts, Selberg and
Levinson-Conrey global moments, H1, and RH remain open.

The census interpretation is strengthened accordingly: a family is not exhausted by source
listing or peripheral formalization. Its decisive inference, failed premise, and possible
cross-route repairs must be recorded. Original conjectures and direct RH attacks remain open
during this historical coverage phase.

## 2026-07-29 H1 Hardy tangential-theta selection

After public closure of the complex-alpha equation, a fresh cross-family comparison selects the
remaining Hardy 1914 source edge rather than assuming H1 continuity. Equation (3) and the
tangential theta limit are uniquely positioned between two compiled endpoints: equation (2) and
the conditional consumer proving infinitely many critical-line zeros from
`HardyXiAbelMomentLaw`.

The new attack does not assume the source's general Bohr--Riesz summability theorem. It uses the
compiled Jacobi theta Poisson transformation to move the cusp `-1` to imaginary infinity and
targets all-order Gaussian flatness with every branch and derivative checked in Lean. H2 contour
shifts, H7/H8 concrete spectral objects, H10 geometric transfer, H11 sparse amplification, H12
global counts, and H14 computation remain live alternatives. Quantitative Hardy--Littlewood,
Selberg, and Levinson--Conrey estimates, H1, and RH remain open.

## 2026-07-29 H1 Hardy tangential-theta implementation result

The selected edge succeeds. Lean now proves an exact branch-preserving translation and inversion
of Hardy's theta boundary term from the cusp `-1` to a half-integer theta series at imaginary
infinity. Cauchy estimates plus Gaussian domination establish rapid decay of every iterated
theta derivative after every fixed polynomial loss. Separately, full-strip Xi domination
justifies every derivative of Hardy's actual parameter integral and identifies order `2p` with
the literal Abel moment.

Differentiating the compiled equation (2) yields equation (3) with the source sign and
`4^(2*p)` denominator. The left endpoint proves `hardyXiAbelMomentLaw_unconditional`, and the
existing sign-amplification consumer yields `infinite_criticalLineZeros_hardy`. Frozen commit
`75f5c575b2c3f050f0e5703efb5ce6851d97775c` passed Lean Action run `30435633763`, build job
`90522592740`, in `2m17s`.

This closes Hardy's qualitative infinitude theorem, not the broader H1 family. The next live
historical producers are quantitative Hardy--Littlewood counts, Selberg's global moment
estimates for a positive proportion, and the Levinson--Conrey auxiliary count. Original
conjectures, falsification, and direct RH attacks remain open.

## 2026-07-30 H2 contour-shift omission re-entry

After public closure of the Hardy--Littlewood eta-to-Theta transfer, the census is reranked
across H1, H2, H7/H8, H10, H11, H12, and H14. H2 is selected for a materially new source
edge: not the already compiled local residues or inverse-Mellin line, but the infinite
rectangle that connects them to the classical Type-I/Type-II detector.

Maynard--Pratt Appendix C makes the singularity split explicit. At an actual nontrivial zero
`rho`, the Gamma pole at `w=0` is canceled by `zeta(rho)=0`, while the translated zeta pole at
`w=1-rho` contributes
`Y^(1-rho)*Gamma(1-rho)*M(1)`. The project can encode both decisions in one
`dslope zetaPoleRemoved rho` numerator and can reuse independent rectangle, Gamma-ratio, and
zeta-strip infrastructure.

The selected campaign must prove uniform horizontal-edge decay and actual integrability on the
original and shifted lines. A local residue theorem or conditional contour premise is
insufficient. The later dyadic large-value bounds, zero-density theorem, H2, and RH remain
outside the endpoint. This re-entry tests a decisive historical inference for an overlooked
weakening or cross-route repair; it is not numerical optimization.

## 2026-07-30 H2 contour-shift local implementation result

The selected inference closes locally in Lean. A holomorphic pole-removed numerator encodes the
two distinct singularity decisions without a simple-zero assumption. Fixed-strip Gamma and zeta
estimates discharge both horizontal edges; the actual source and shifted lines are integrable;
and the finite weighted-Cauchy rectangle passes to the exact infinite line identity.

Composing with inverse Mellin proves the shifted smoothed detector series, while absolute
summability exposes the exact coefficient-gap head/tail formula before the source's dyadic
split. The aggregate certificate is `classicalDetectorContourShift_endpoint`.

This audit found no omitted shortcut from the contour shift to H2: the next substantive human
input is the quantitative Type-I/Type-II block and tail control. That successor, the resulting
zero-density estimate, H2, and RH remain open. The local result is
`FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`; public evidence closure is pending.

## 2026-07-30 H7 Fourier-topology omission re-entry

After public closure of the H2 contour shift, the census is reranked across H1, H2, H7/H8, H10,
and H11. H7 is selected because its old source-instantiation boundary has materially changed:
the project now compiles actual finite Weil source blocks, finite-dictionary admissibility, and
the unconditional explicit formula in addition to the earlier parity and Rayleigh-gap
consumers.

Connes's 2026 Fact 6.4 proves that the explicit prolate packet transforms converge to `Xi`
uniformly on closed substrips. Section 6.6 still requires a sufficiently good approximation of
the true ground state by that packet. The phrase hides a topology question when support expands:
ordinary finite-dimensional or unweighted function convergence need not control Fourier values
at nonreal points.

The selected campaign tests this exact boundary. It targets an exponentially weighted `L1`
criterion sufficient for uniform strip convergence and a smooth escaping-packet counterexample
to unweighted promotion. The actual source comparison, simple-even ground states, the
all-real-zero limit, H7, and RH remain open.

## 2026-07-30 H7 Fourier-topology local implementation result

The topology test succeeds in both directions relevant to the audit. Lean proves that
`exp(A*abs(x))`-weighted `L1` error controls centered Fourier error uniformly for every point of
the closed strip `abs(Im z)<=A`, and proves the corresponding two-stage convergence transfer in
the exact ground-state source coordinate.

Lean also constructs a smooth compactly supported packet whose support escapes to `+infinity`.
Its unweighted `L1` mass and squared `L2` mass tend to zero, but its Fourier value at the fixed
interior point `-i/4` remains exactly one. This formally rules out a support-blind interpretation
of "sufficiently good" approximation.

No overlooked shortcut to H7 was found. The source comparison obligation is now more precise:
prove exponential-strip weighted convergence of `theta_x-k_lambda` for each fixed width below
`1/2`, or prove a different estimate strong enough to imply it. Simple-even ground states, the
actual comparison, the all-real-zero limit, H7, and RH remain open.

## 2026-07-30 H2 dyadic detector omission result

After public closure of the H7 Fourier-topology audit, the census is reranked across the major
historical families and returns to the first unresolved Maynard--Pratt source paragraph after
the compiled contour shift. The selected endpoint is Appendix C, Lemma 23's actual finite
detector, not a density exponent or numerical optimization.

The local Lean implementation proves the actual coefficient divisor bound, exact finite cutoff,
binary-logarithmic block decomposition, exponentially small actual far tail, small head and
retained-residue errors, and logarithmic block-cardinality comparison. It also reconciles the
source's real scale notation with
`Y=sqrt T`, `M=floor(2*T^(1/100))`, and
`K=ceil(sqrt(T)*(log T)^2/2)`, then derives the eventual actual-zero Type-I/Type-II
disjunction. Aggregate certificate:
`classicalDetectorDyadicDichotomy_endpoint`.

The historical audit finds no omitted shortcut from Lemma 23 to RH. The finite mechanism is
complete, but the actual Type-I large-block rarity and Type-II shifted-integral rarity estimates
remain open, as do the zero-density theorem, H2, and RH. Local classification:
`FULL_SUCCESS / SOURCE_DYADIC_DICHOTOMY_FORMALIZED`.
