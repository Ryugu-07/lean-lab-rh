# RH Route Portfolio

Date: 2026-07-15

## Selection Context

The automatic 2025-2026 recent-literature screening campaign is closed by
`AUDIT-20260715-M2-G3-03`. This portfolio starts a different Discovery Protocol V3 campaign. It
does not reopen Wong arXiv `2310.03972v5`, Carvill arXiv `2510.18132`, or any candidate rejected by
the stop audit.

All five routes have the same exact RH endpoint already compiled in the project:

```lean
Mathlib.RiemannHypothesis ↔
  baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure
```

The routes differ only in how they might attack an unconditional edge leading to one side of this
equivalence or to another exact RH criterion.

## Selection Update: R5 Symmetric Gaussian Height Limit

Date: 2026-07-16

After the public closure of the R1 q=2 criterion, a fresh six-candidate audit rejects another
q-weighted equivalence, unconditional exact approximants, Li-matrix operator repackaging, a
self-adjoint compression without a spectral bridge, and the previously deferred generic
`A_delta` height limit. Only one candidate has specific new evidence:

```text
G_a(s) = exp(a * (s - 1/2)^2),  a > 0.
```

This weight is entire, reflection invariant, and contributes `exp(-a*T^2)` uniformly on each
fixed horizontal edge. Combined with the existing multiplicity-bearing reciprocal-square xi-zero
sum, it should permit a polynomial near-zero count, quantitatively separated heights, a
polynomial compensated-log-derivative bound, and hence vanishing horizontal integrals. Campaign
`CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-HEIGHT-LIMIT-01` preregisters the indivisible selected-height
right-vertical integral limit to `pi` times the absolute Gaussian zero `tsum`.

This is an unconditional fixed-test W1c1 theorem, not the generic explicit formula, positivity, or
RH. Success has `hard_gap_delta=1` only for that fixed-test height-limit subedge and 0 for RH.
Proof Attempt A begins with exact Gaussian norm/symmetry, absolute zero summability, and xi
logarithmic-derivative reflection. The campaign may not close on those helpers alone.

### Completion Update

The fixed endpoint now compiles as
`exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral`. Reciprocal-square zero mass alone
supplies the polynomial near/far boundary control, while exact Gaussian decay kills the selected
horizontal integrals. Reflection and the finite rectangle theorem give the checked factor `pi`.
The campaign closes locally as `BRIDGE_REDUCED`: one fixed-test W1c1 height-limit subedge is now
complete, but generic class-E limits, prime/archimedean evaluation, regularization, positivity,
and RH are unchanged. Implementation commit `00410cc2a6919acfa5835b121c47489c5105e0de` and
evidence-backfill commit `2292801d710a1a95857de69a92498c39ae79d0d3` both passed public CI, so the
campaign is publicly closed and this fixed endpoint must not be reopened without new evidence.

## Selection Update: R5 Gaussian Arithmetic Explicit Formula

Date: 2026-07-16

Fresh route selection after the public Gaussian height-limit closure screens six candidates. A
generic `A_delta` limit still lacks vertical decay; the 2026 finite Galerkin dictionary is exact
but uses a different band-limited carrier and finite positivity is not RH progress; the
screw-function operator limit is explicitly conjectural; Gaussian positivity has no unconditional
off-line-zero mechanism; and mere full-line integrability is too narrow. The only adjacent
candidate with a complete mechanism is the fixed Gaussian arithmetic explicit formula.

Campaign `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-EXPLICIT-FORMULA-01` fixes the indivisible endpoint

```text
pi * GaussianZeroSum
  = 2*pi*exp(a/4) + GammaRLineIntegral - GaussianVonMangoldtSum.
```

The mechanism is the exact Fourier transform of a Gaussian, absolute L-series convergence on
`Re(s)=c>1`, logarithmic digamma growth, and a two-pole contour/reflection calculation. It is
unconditional and does not imply RH. Success reduces one fixed-test arithmetic W1c subedge only;
generic test classes, regularization, W2 positivity, and RH remain open.

### Endpoint Update

The exact endpoint now compiles as `gaussianXi_arithmetic_explicit_formula`. The one-term Gaussian
transform simplifies to the `c`-independent von-Mangoldt weight; absolute convergence justifies
the full-line interchange; `logDeriv GammaR` is reduced to digamma and dominated by a linear-times-
Gaussian majorant; and an independent symmetric rectangle encloses the poles at `0` and `1`,
giving `2*pi*exp(a/4)` on the right line. The compiled selected-height zero-side theorem then
identifies the arithmetic limit with the absolute multiplicity-bearing Gaussian zero sum. This is
an unconditional fixed-test explicit formula, not a generic Weil class, positivity theorem, or RH.
Exact TargetChecks, five standard-only axiom prints, all forbidden-token/declaration/resource
scans, `git diff --check`, the standalone module build, and the 8,670-job full build pass. The
campaign is locally complete as `BRIDGE_REDUCED`.
Implementation commit `6c65019d9de2d31127dd3bf8389994207c17dcb5` passed public Lean Action CI
run `29441160498`, build job `87440149741`, in `2m33s`. Evidence-backfill commit
`fa5fdc5aefd4dd3e99966cc1e0fcca62293e9600` passed public CI run `29441452307`, build job
`87441220281`, in `1m28s`. The campaign is publicly closed as `BRIDGE_REDUCED`; a fresh route
selection is required before another campaign.

## Selection Update: R5 Symmetric Gaussian Translate Family

Date: 2026-07-16

Fresh cross-route selection screens six candidates after the centered Gaussian formula closed.
The Gaussian-Perron defect has a useful new error-function smoothing but a different `1/z` carrier
and conditional later localization; Arias de Reyna's tempered prime distribution is exactly
RH-equivalent; de Bruijn--Newman requires a new zero-reality theory; Suzuki's finite-interval
operator limit is conjectural; and R1 has no new unconditional residual upper bound.

Campaign `CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01` selects

```text
G_(a,b)(s) = exp(a*(s-1/2)^2) * cosh(b*(s-1/2)),  a>0, b real.
```

The factor is reflection invariant and uniformly bounded in the vertical direction on fixed
strips. Its two exponential branches translate the prime-side Gaussian to `log(n)-b` and
`log(n)+b`. Lean pre-admission checks pass for reflection, `b` parity, `b=0`, both transform
exponents, and absolute zero summability. The indivisible endpoint is the full two-parameter
zero/pole/GammaR/von-Mangoldt formula plus exact specialization to the publicly closed `b=0`
theorem. This supplies Gaussian translation probes for the Arias de Reyna distributional route;
it does not assume density, temperedness, positivity, or RH.

## Portfolio Update: R5 Symmetric Gaussian Translate Family Locally Complete

Date: 2026-07-16

`CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01` reaches its fixed endpoint locally as
`NEW_RELEVANT_LEAN_THEOREM`. The new module first extracts a generic selected-height rectangle
limit for analytic reflection-symmetric weights whose xi-zero restriction is absolutely summable
and whose selected top edge vanishes. It then proves those hypotheses for
`exp(a(s-1/2)^2)cosh(b(s-1/2))`, evaluates the two exponential prime branches as Gaussian kernels
centered at `log(n)=b` and `log(n)=-b`, transfers GammaR integrability through the bounded
modulation, and computes the pole pair as `2*pi*exp(a/4)*cosh(b/2)`. The endpoint
`symmetricGaussianXi_arithmetic_explicit_formula` and exact `b=0` reduction compile without
placeholders.

Standalone, target, TargetChecks, standard-only axiom, forbidden scan, diff, and 8,671-job full
build gates pass. This closes one unconditional two-parameter probe-family subedge only. It does
not prove Schwartz/Hermite density, temperedness of the prime/archimedean distribution, Weil
positivity, or RH; `hard_gap_delta=0` for G6, G7, and RH. At the local gate, public CI remained
before closure.

Implementation commit `5c4ae54c031a6d999111390694ef738a3da57146` passed public Lean Action CI
run `29444276732`, build job `87450715956`, in `1m50s`. Evidence-backfill commit
`ed92d851f0eb697f2b2aec0e1260fe0002ea5bcf` passed public Lean Action CI run `29444485950`, build
job `87451417716`, in `1m31s`. The campaign is publicly closed as
`NEW_RELEVANT_LEAN_THEOREM`; a fresh independent route selection is required before another
campaign.

## R1: Exact Baez-Duarte Gram And Projection Geometry

- **Exact RH endpoint:** unconditional closure membership for the positive-natural kernel span.
- **First unproved edge:** a non-tautological coefficient or inverse-Gram estimate that controls
  actual projection residuals as the natural cutoff grows.
- **Existing Lean infrastructure:** the exact real/complex carrier and criterion; Fourier-Mellin
  isometry; Burnol continuous/natural spaces; explicit finite Gram and inverse machinery for the
  separate Burnol zero-vector construction; Wong and Carvill counterexamples.
- **Candidate mechanism:** normalize `rho(1/(n*x))` by `sqrt(n)`, expose its translation geometry in
  logarithmic coordinates, reject dense-sampling coercivity, and test whether a sufficiently sparse
  geometric subsequence has an explicit lower frame bound.
- **RH strength audit:** Gram stationarity or a sparse lower frame bound does not imply RH. Target
  membership in the sparse closed span would imply RH and is therefore not an admissible bridge
  lemma unless proved directly.
- **Immediate falsification tests:** maximum-norm growth of the exact Wong projection; false
  ladder-distance frequency bound from Carvill; adjacent normalized kernels; finite Gram spectra;
  diagonal dominance and residual, not just positivity.
- **Closest literature:** Ehm, arXiv `2405.06349`, gives exact NB Gram-kernel formulas and
  quadratic-form decompositions; Alouges-Darses-Hillion, arXiv `2006.02953`, obtains structured Gram
  matrices in a generalized criterion; Bettin-Conrey-Farmer, arXiv `1211.5191`, studies conditional
  optimal coefficients; general dilation-system Riesz criteria appear in arXiv `2110.07659`.
- **Six-loop campaign:** route map; at most five candidates; adversarial numerical and exact tests;
  one explicit sparse-coercivity proof attempt; one repair or pivot; independent audit.
- **Decision:** **SELECTED**. It reuses exact project objects, has immediate falsification leverage,
  and asks for a concrete unconditional structural estimate without pretending that positivity of
  a finite Gram matrix is RH evidence.

## R2: Explicit Approximants Constrained By Burnol

- **Exact RH endpoint:** an explicit positive-natural finite family whose error tends to zero.
- **First unproved edge:** an unconditional upper bound tending to zero for a source-aligned family.
- **Existing Lean infrastructure:** exact distance definitions, finite-natural inclusion, and the
  full RH-conditional Burnol liminf lower bound with zero-sum constant.
- **Candidate mechanism:** regularized Mobius or optimized coefficients with an upper bound of the
  only rate still compatible with Burnol, namely no faster than the `1/sqrt(log N)` norm scale under
  the source hypotheses.
- **RH strength audit:** any unconditional error-to-zero theorem on this exact carrier proves RH.
  Rate compatibility alone does not.
- **Immediate falsification tests:** compare every claimed rate with the compiled Burnol lower
  bound; inspect hidden RH, simplicity, or reciprocal-zeta moment assumptions; test the full-line
  tail and coefficient moment.
- **Closest literature:** Burnol, arXiv `math/0103058`; Bettin-Conrey-Farmer, arXiv `1211.5191`.
- **Six-loop campaign:** coefficient inventory; exact candidate; rate/assumption audit; finite
  tests; proof attempt only if an unconditional new estimate remains; independent audit.
- **Decision:** **DEFER**. The first meaningful positive edge is already RH-hard and no new
  unconditional coefficient estimate is presently available.

## R3: Li And Weil Positivity

- **Exact RH endpoint:** nonnegativity of every correctly defined Li coefficient or Weil quadratic
  form on the complete test-function class.
- **First unproved edge:** a global coefficient/test-function representation aligned with the
  project's entire `riemannXi`, not another calculation of a fixed low coefficient.
- **Existing Lean infrastructure:** entire xi, functional equation, local logarithm, first two local
  Li candidates, Mellin/Fourier infrastructure, and substantial special-function estimates.
- **Candidate mechanism:** a norm or positive-kernel representation for a whole indexed family,
  with the zero-sum and explicit-formula sides kept exact.
- **RH strength audit:** positivity for every index is equivalent to RH. A finite prefix is known
  mathematics and cannot establish the endpoint.
- **Immediate falsification tests:** indexing and logarithm-branch alignment; conditional norm
  identities disguised as unconditional; finite positivity that omits the infinite tail.
- **Closest literature:** Suzuki, arXiv `2301.05779`, represents Li coefficients as norms under an
  RH-equivalent condition and connects them with Weil positivity; Voros, arXiv `math/0506326`, gives
  exact and asymptotic Li-coefficient formulas.
- **Six-loop campaign:** statement alignment; representation candidates; branch/zero tests;
  explicit-formula dependency audit; one global-family proof attempt; independent audit.
- **Decision:** **DEFER**. The project lacks the global Hadamard/Weil bridge, and fixed-index work
  would repeat the old low-coefficient campaign.

## R4: Spectral Or Self-Adjoint Operator Constructions

- **Exact RH endpoint:** a self-adjoint operator whose relevant spectrum is proved to coincide with
  all nontrivial zero ordinates, with multiplicity.
- **First unproved edge:** a concrete densely defined closed symmetric operator together with a
  proved zero-spectrum correspondence; neither property may be postulated.
- **Existing Lean infrastructure:** Hilbert spaces, Fourier-Mellin unitary maps, multiplication
  phases, cutoff projections, and Burnol boundary vectors.
- **Candidate mechanism:** compress a concrete scaling or phase operator to an explicitly defined
  subspace and audit symmetry, closure, deficiency indices, and spectral correspondence in that
  order.
- **RH strength audit:** a complete self-adjoint zero-spectrum bridge essentially proves RH. Mere
  symmetry or a suggestive spectrum is far weaker.
- **Immediate falsification tests:** undefined domains; non-dense domains; symmetric but not
  self-adjoint operators; only one inclusion in the spectral bridge; hidden RH in the subspace.
- **Closest literature:** Burnol, arXiv `math/0103058`, explicitly relates his Hilbert vectors to
  Hilbert-Polya ideas; Connes-Consani, arXiv `1910.14368`, formulates an operator-theoretic problem
  and leaves the Weil positivity step as the decisive condition.
- **Six-loop campaign:** domain map; closability tests; finite deficiency models; spectral-bridge
  audit; one operator proof attempt; independent audit.
- **Decision:** **DEFER**. Its first honest edge is much larger than R1 and the zero-spectrum bridge
  is currently absent.

## R5: Explicit Formula And Test-Function Positivity

- **Exact RH endpoint:** Weil positivity on a source-faithful dense class of admissible test
  functions, connected without extra assumptions to `Mathlib.RiemannHypothesis`.
- **First unproved edge:** a complete Lean explicit formula with prime, archimedean, and zero terms
  plus a test-function class stable under the required convolution/involution.
- **Existing Lean infrastructure:** Fourier-Mellin transforms, contour integration, zeta
  functional equations, zero discreteness, and explicit analytic estimates.
- **Candidate mechanism:** compactly supported multiplicative autocorrelations with an explicit
  tail estimate, allowing finite-dimensional positivity tests without replacing the full criterion.
- **RH strength audit:** positivity on the complete Weil class is RH-equivalent. Positivity on a
  finite test set is only a check.
- **Immediate falsification tests:** missing moment constraints; sign convention in the explicit
  formula; unproved density; truncation errors; positivity only after assuming RH.
- **Closest literature:** Suzuki, arXiv `2301.05779`, records the Li/Weil connection and exact test
  functions; Connes-Consani, arXiv `1910.14368`, states the compact-support Weil-positivity
  operator problem.
- **Six-loop campaign:** source statement; test-space inventory; finite countertests; explicit-formula
  dependency map; one exact subedge attempt; independent audit.
- **Decision (2026-07-15 independent audit):** **SELECTED FOR ONE TEST-ALGEBRA CAMPAIGN** after the
  R3 Li criterion campaign closed. `CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01` targets exactly
  Lagarias Appendix A (A.1)-(A.2), including the conjugate-star critical-line specialization. This
  is necessary infrastructure with `hard_gap_delta=0`; the complete explicit formula remains the
  fixed R5 frontier and finite positivity remains inadmissible as RH progress.

## Selected Campaign: R5 Weil Strip Class Locally Complete

Independent audit admits one exact same-route successor from Lagarias's `A_delta` definition and
the publicly closed W1a convolution theorem. `CAMPAIGN-20260715-R5-WEIL-STRIP-CLASS-01` now closes
locally as `KNOWN_THEOREM_FORMALIZED`. `WeilStripClass.lean` packages a positive-width physical
Mellin class with closed-strip convergence, continuity, and finite uniform bound plus open-strip
analyticity, then proves vector, involution, conjugation/star, convolution, and autocorrelation
closure. The conjugation proof checks the cancellation of the two anti-holomorphic operations;
the convolution proof uses W1a rather than assuming transform closure.

This completes W1b's physical algebra core only. It does not claim metric separation,
quotient/uniqueness/completeness, density, the complete explicit formula, positivity, or RH.
Exact targets, standard-only axiom output, scans, diff check, and the 8,664-job full build pass
locally. `hard_gap_delta=0`. Implementation commit
`335d6dfa175a345555aaa408b5581ed743d2abf7` passed public Lean Action CI run `29412820223`, build
job `87343685661`, in 1m42s. Evidence-backfill commit
`4b1d549504ae1965fb8cd34e314a4c682ca662a2` passed public Lean Action CI run `29413062276`, build
job `87344475624`, in 1m46s. The campaign is publicly closed.

## Selected Campaign: R3/R5 Li-Weil Gram Publicly Closed

Date: 2026-07-15

Fresh independent audit does not admit the complete W1c explicit formula as one bounded successor:
Lagarias Appendix A requires a conditionally convergent zero cutoff, local Euler-factor terms,
unconditional strip width, and cutoff regularization. Instead, Theorem 3.1 supplies a distinct
cross-route source edge. `CAMPAIGN-20260715-R3-R5-LI-WEIL-GRAM-01` is selected to construct the
reflection-averaged, multiplicity-bearing Li-test Gram kernel, prove its exact coefficient matrix,
identify every finite real quadratic combination with a zero-side norm-square sum under RH, and
recover the exact RH equivalence from one-coordinate tests.

The campaign closes as `KNOWN_THEOREM_FORMALIZED`. `LiWeilGram.lean` proves the
reflection average is a summable finite combination of paired Li terms, obtains the exact
successor-indexed coefficient matrix, identifies every finite real quadratic value with a
summable zero-side norm-square series under RH, and recovers RH from one-coordinate positivity.

This campaign is knowingly RH-equivalent with `hard_gap_delta=0`. It does not prove W1c, W2, or
either side of the resulting criterion. Exact targets, 15 standard-only axiom outputs, scans, diff
check, and the 8,665-job full build pass locally. Implementation commit
`2317143e73e1d788d65dcdff9b609a98f8ac60b2` passed public Lean Action CI run `29415448733`, build
job `87352327801`, in 1m48s. Evidence-backfill commit
`89fb947b493c8fd315bbe67a5be8c09fc99cdfa3` passed public Lean Action CI run `29415725269`, build
job `87353260131`, in 1m35s. The campaign is publicly closed; only closure-log CI and clean
synchronization remain before fresh route selection.

## Selected Campaign: R5 Weil Explicit Integrand Publicly Closed

Date: 2026-07-15

Fresh route selection returns to R5/W1c only after an independent five-candidate audit. The
complete class-E explicit formula is too large for one bounded campaign, while isolated prime or
archimedean terms and a single fixed test function do not connect the source sides. Campaign
`CAMPAIGN-20260715-R5-WEIL-EXPLICIT-INTEGRAND-01` therefore fixes the unconditional
`Re(s)>1` logarithmic-derivative identity joining the project xi function to its pole terms,
`GammaR` factor, and Mathlib's von Mangoldt L-series, then splices this with the compiled
genus-one Hadamard zero sum.

This endpoint is strictly weaker than the complete explicit formula and does not imply RH. If it
passes the fixed verification gate, W1c0's analytic integrand subedge closes while test-function
integration, contour cutoffs, zero-sum limits, local regularization, W2, and RH remain open.
Preregistration: `research/r5_weil_explicit_integrand_prereg_20260715.md`.

The fixed endpoint now compiles as `BRIDGE_REDUCED`. `WeilExplicitIntegrand.lean` proves the
right-half-plane xi product, its exact pole/GammaR/von-Mangoldt logarithmic derivative, and equality
with the existing multiplicity-bearing Hadamard zero sum. Exact targets, all six standard-only
axiom outputs, scans, diff check, standalone builds, and the 8,666-job full build pass locally.
Implementation commit `89d4dd12ebedc75c13261a0d43a9254b5931c30d` passed public Lean Action CI
run `29417432562`, build job `87359008630`, in 1m47s. Evidence-backfill commit
`1b405639a4e28c72fc1e2484259c047ad95ed0b2` passed public Lean Action CI run `29417710278`, build
job `87359940112`, in 1m31s. The campaign is publicly closed; closure-log CI and clean
synchronization remain before fresh route selection.

## Portfolio Update: R3 Xi Zero Divisor

Date: 2026-07-15

R1's selected sparse mechanism is now closed: the lower-frame theorem was proved, and an exact
three-interval witness subsequently proved that the target is not in the sparse closed span. Do not
resume target coupling for the `(2^24)^j` family without a genuinely different endpoint.

Route selection therefore moved to the distinct R3 family for
`CAMPAIGN-20260715-XI-DIVISOR-01`. The campaign closes as `BRIDGE_REDUCED`:

- `riemannXiZeroDivisor` is a global locally finite divisor;
- its value is the finite natural analytic zero multiplicity;
- its support is exactly `{s | IsNontrivialZero s}`;
- multiplicity is invariant under `s |-> 1-s`;
- negative-even trivial zeta zeros and infinite local order are Lean-excluded.

This gives `hard_gap_delta=1` for the inventoried divisor/local-multiplicity prerequisite and no
change to the RH assumption frontier. R3 still lacks order-one growth, a global Hadamard product or
substitute, zero-sum convergence, the coefficient-to-zero identity, and all-index positivity.

Next state is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. R3 may continue only if the audit admits
one of those precise global edges; fixed low-index coefficient work remains rejected.

## Portfolio Update: R3 Global Xi Hadamard Bridge

Date: 2026-07-15

Independent audit admitted the precise global successor
`CAMPAIGN-20260715-XI-HADAMARD-01`. The campaign closes as `BRIDGE_REDUCED`:

- the project xi is Lean-proved equal to the audited order-one entire `Complex.riemannXi`;
- its nonzero divisor index uses exactly the preceding campaign's analytic multiplicities;
- index values are exactly the project `IsNontrivialZero` points;
- squared reciprocal zero norms are summable with multiplicity;
- xi has a global genus-one Hadamard product with a degree-at-most-one exponential polynomial;
- away from nontrivial zeros, its log derivative is the convergent compensated zero sum plus the
  polynomial derivative.

The source closure is existing Apache-2.0 formalization from pinned
`PrimeNumberTheoremAnd@d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, not a new mathematical
factorization result. Route-local `hard_gap_delta=3`; the RH assumption frontier is unchanged.

R3 no longer lacks order-one growth, a global canonical product, or genus-one compensated
zero-sum convergence. It still lacks the all-index derivative-defined Li family, the exact
derivative-to-zero identity with justified infinite-sum operations, all-index positivity, and the
Li/RH equivalence. Next state is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`; do not resume
fixed-index coefficient calculations.

## Portfolio Update: R3 All-Index Compensated Li Zero Formula

Date: 2026-07-15

Independent audit admitted
`CAMPAIGN-20260715-LI-ZERO-FORMULA-01` as the exact successor to the xi Hadamard bridge. The
campaign closes as `BRIDGE_REDUCED`:

- the derivative-defined project Li family is expanded for every index, not a fixed prefix;
- the genus-one compensated zero-term formula is differentiated to every order;
- every positive-order derivative series is compact-locally uniformly summable on the xi nonzero
  set from the squared reciprocal zero estimate;
- termwise iterated differentiation at `1` is justified through `iteratedDerivWithin_tsum`;
- one fixed degree-at-most-one Hadamard polynomial works for every derivative order and Li index;
- the final formula retains multiplicity, order-zero compensation, and the polynomial derivative.

This is existing Li/Hadamard mathematics aligned with the project objects, not a new proof idea.
Route-local `hard_gap_delta=1`; the RH assumption frontier is unchanged. R3 no longer lacks the
all-index derivative-to-compensated-zero identity. It still lacks a proved normalization to the raw
classical zero sum, positivity for all coefficients, and the exact Li/RH equivalence.

Next state is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. Continue R3 only with one of those
precise global edges or choose a distinct route family; do not return to fixed-index coefficients.

## Portfolio Update: R3 Symmetry-Paired Li Formula And RH-Forward Positivity

Date: 2026-07-15

Independent audit admitted
`CAMPAIGN-20260715-LI-SYMMETRIC-ZERO-01` as the global successor to the compensated formula. The
campaign closes locally as `BRIDGE_REDUCED`:

- the full multiplicity-bearing xi divisor index has an involution with value `rho |-> 1-rho`;
- the unpaired raw series is not falsely claimed summable, and a compiled harmonic model rejects
  that inference;
- the averaged raw Li term is summable for every index;
- the Hadamard polynomial and reciprocal compensation cancel by the xi functional equation;
- every derivative-defined project coefficient equals the unconditional paired raw zero sum;
- under RH every summand is half a norm square, giving zero imaginary part and nonnegative real
  part for all indices;
- a compiled off-critical pair shows the termwise sign conclusion genuinely requires RH.

This is existing Li/Bombieri-Lagarias mathematics aligned with project objects. Route-local
`hard_gap_delta=2`; the RH assumption frontier is unchanged. R3 no longer lacks raw paired
zero-sum normalization or the RH-forward all-index positivity direction. The reverse implication
from all-index Li nonnegativity to RH remains the exact open R3 edge. Implementation commit
`4168188f70e2cb6f2e47c65334a8326dabd23edc` passed public Lean Action CI run `29401711930`, build
job `87307546611`, in 1m48s.

Evidence-backfill commit `81c53eb62acf3500aee00061e5ee0ff8cc6eb13e` passed public Lean Action
CI run `29401901693`, build job `87308160283`, in 1m55s. The campaign is publicly closed; route
selection must now independently audit the reverse Li criterion or choose another route family.

Next state after public verification is `INDEPENDENT_AUDIT`, then `ROUTE_SELECTION`. A reverse Li
criterion campaign requires a source-audited large-index/unit-disk argument and must not assume
the conclusion as a zero-location premise.

## Portfolio Update: R3 Reverse Li Criterion Selected

Date: 2026-07-15

Independent audit reconstructed both published reverse mechanisms: the Bombieri-Lagarias maximal
transformed-zero power-sum argument and the Pringsheim generating-series argument. Five precise
candidates and their adversarial tests are recorded in
`research/r3_li_reverse_bombieri_lagarias_prereg_20260715.md`.

`CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01` selects the project-specialized power-sum
route. Its indivisible endpoint is

```lean
RiemannHypothesis <->
  forall n : Nat, 0 <= (liCoefficientCandidate n).re
```

The source's conjugate-pair cosine bookkeeping will be replaced by a finite-product compactness
argument that simultaneously returns every maximal unit phase near `1` along an unbounded even
subsequence. This is a proof-mechanism simplification, not a stronger premise. The remaining
source blocks are retained exactly: attained finite maximal orbit radius, strict complement gap,
far/near split, squared-reciprocal tail control, and exponential domination.

R3 remains **SELECTED**. Pringsheim is deferred because pinned Mathlib lacks the boundary
singularity theorem and the route needs a larger analytic-continuation stack. A generic arbitrary
multiset formalization is also deferred as unnecessary abstraction. Partial phase or tail helpers
do not count as campaign progress.

## Portfolio Update: R3 Reverse Li Criterion Publicly Complete

Date: 2026-07-15

`CAMPAIGN-20260715-LI-REVERSE-BOMBIERI-LAGARIAS-01` closes as
`KNOWN_THEOREM_FORMALIZED_WITH_PROJECT_SPECIALIZED_PHASE_ARGUMENT`:

- the Mobius Li transform lies in the unit disk exactly on the correct half-plane;
- reflection exchanges the transform with its inverse, and every off-line orbit has radius above
  one;
- every radius superlevel above one is finite on the full multiplicity-bearing divisor index;
- all dominant unit phases in such a finite set return simultaneously near one at arbitrarily
  large even powers;
- the aligned paired term has an explicit exponentially negative real-part bound;
- the whole complement is bounded by one fixed summable reciprocal-square weight times
  `m^2*c^m`;
- choosing `c=(1+R0)/2` for any off-line orbit avoids the source proof's global-maximum and
  far/near bookkeeping while retaining a strict exponential gap;
- any off-line zero therefore forces a negative project Li coefficient;
- Lean proves both the reverse implication and
  `RiemannHypothesis <-> forall n, 0 <= Re(liCoefficientCandidate n)`.

Route-local `hard_gap_delta=1`: L2/G5 is complete. This is an exact RH-equivalent criterion, not an
unconditional proof of either side, so the global RH assumption frontier remains open and the
persistent Goal stays active. Standalone, exact targets, standard-only axiom audit, scans, diff
check, and the 8,661-job full build pass locally. Implementation commit
`22cedfa17788fec546b91b9dc78452de52d87e64` passed public Lean Action CI run `29406614212`, build
job `87323510543`, in 2m31s.

Evidence-backfill commit `48385f277c83b06a5d72aee83d06d0f4b31623d1` passed public Lean Action
CI run `29406932411`, build job `87324549428`, in 1m21s. The campaign is publicly closed. R3 has
now compiled the complete project Li/RH equivalence, but no unconditional side of that equivalence.
Next state is `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; the persistent RH goal remains active.

## Portfolio Update: R5 Weil Test Algebra Complete

Date: 2026-07-15

After the complete R3 Li criterion closed, route selection moved to the distinct R5 explicit-formula
family. `CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01` closes as `KNOWN_THEOREM_FORMALIZED`:

- Weil's positive-half-line involution `f_tilde(x)=x^(-1)f(x^(-1))` is Lean-defined and
  pointwise involutive exactly where `0<x`;
- a compiled counterexample rejects involutivity at `x=0` for the total extension;
- Mellin convergence is preserved iff under `s |-> 1-s`;
- the transform value obeys Lagarias (A.2), including the exact `0/1` endpoint swap;
- the conjugate-star operation preserves convergence under `s |-> 1-conj(s)` and transforms by
  complex conjugation;
- on `Re(s)=1/2`, the star transform is conjugation at the same spectral point.

This completes only the first test-algebra subedge. It does not state the multiplicative
convolution theorem, the explicit formula, the Weil quadratic form, density, or positivity.
`hard_gap_delta=0`; the RH assumption frontier is unchanged. The next state is
`INDEPENDENT_AUDIT -> ROUTE_SELECTION`, and another R5 campaign requires a genuinely new exact
edge rather than wrappers around the compiled involution. Implementation commit
`24621330af4a24269a1748c5b3a4f924c16a7768` passed public Lean Action CI run `29409014307`, build
job `87331366564`, in 2m27s. Evidence-backfill commit
`1c9e7fe27536bda8e04aa7e7bda2af1d110fe61c` passed public Lean Action CI run `29409249934`, build
job `87332127195`, in 1m33s. The campaign is publicly closed.

## Portfolio Update: R5 Weil Convolution Locally Complete

Date: 2026-07-15

Independent audit admitted the exact same-route successor from Lagarias (A.7) and Mathlib's
additive Bochner-convolution infrastructure. `CAMPAIGN-20260715-R5-WEIL-CONVOLUTION-01` closes
locally as `KNOWN_THEOREM_FORMALIZED`:

- source-faithful multiplicative convolution is defined with the exact Haar element `dy/y`;
- Mellin convergence is equivalent to integrability of an explicit logarithmic lift;
- logarithmic lift converts multiplicative convolution to additive Bochner convolution;
- two pointwise Mellin-convergent inputs produce a Mellin-convergent convolution;
- the Mellin transform of the convolution is the product of the input transforms;
- convolution with `weilStar` has the exact `1-conj(s)` factor;
- on the critical line, self-star autocorrelation is exactly `Complex.normSq`.

This closes W1a only. Lagarias's complete analytic-strip class, the zero/prime/pole/archimedean
explicit formula, distributional convergence, density, and Weil positivity remain open.
`hard_gap_delta=0` for RH, and the global assumption frontier is unchanged. Local standalone,
target, axiom, scan, diff, and 8,663-job full-build gates pass. Implementation commit
`90874a87a89ee371719c2f50f5cc02eaae8a5040` passed public Lean Action CI run `29410786209`, build
job `87337104802`, in 1m46s. Evidence-backfill commit
`30a816118acf74a0ab9bead03b7541d6929dcfe3` passed public Lean Action CI run `29410987990`, build
job `87337750370`, in 1m29s. The campaign is publicly closed.

## Portfolio Update: R5 Finite-Height Zero Cutoff Selected

Date: 2026-07-15

After W1c0 closed, a fresh independent audit selected
`CAMPAIGN-20260715-R5-WEIL-ZERO-CUTOFF-01`. The fixed endpoint is the unconditional finite-height
weighted argument principle for `riemannXi`: the rectangle boundary integral of
`F * logDeriv riemannXi` must equal `2*pi*I` times the multiplicity-bearing `finsum` of `F(rho)`
over strictly interior xi zeros. Existing compact far-zero estimates in `LiZeroFormula.lean`
provide specific evidence for the required `k=0` local-uniform extension. Single-pole,
unweighted, and assumed finite-kernel statements are helpers or rejected endpoints, not campaign
success. If complete, this closes only the finite-height subedge of W1c1; height limits,
regularization, W2, and RH remain open.

## Portfolio Update: R5 Finite-Height Zero Cutoff Locally Complete

Date: 2026-07-15

`CAMPAIGN-20260715-R5-WEIL-ZERO-CUTOFF-01` reaches its exact fixed endpoint locally as
`BRIDGE_REDUCED`. `WeilZeroCutoff.lean` proves the compensated `k=0` zero series is locally
uniformly summable away from xi zeros, commutes that series with all four weighted boundary
integrals, evaluates each multiplicity-bearing zero by the strict-inside residue dichotomy,
collapses the result to a finite `finsum`, and splices the actual xi logarithmic derivative while
removing the entire Hadamard polynomial term. Exact targets, seven standard-only axiom prints,
empty forbidden scans, `git diff --check`, the 8,635-job module build, and the 8,667-job full build
pass. The next W1c frontier is the height-limit/contour-decay passage and W1c2 regularization; W2
and RH remain open. Public CI is pending.

Implementation commit `7e140a86b6fbe1ed410917b8ee46089bb5dff6fb` passed public Lean Action CI
run `29423254678`, build job `87378909471`, in 3m1s. Immutable evidence backfill is pending.

Evidence-backfill commit `626fef55bb951d1cb59a76f8ff22250c4bc3a0e2` passed public Lean Action CI
run `29423572352`, build job `87380039889`, in 1m47s. The campaign is publicly closed as
`BRIDGE_REDUCED`; begin a fresh independent route audit before choosing the next campaign.

## Portfolio Update: R1 q=2 Baez-Duarte Criterion Selected

Date: 2026-07-15

The independent audit does not admit an immediate continuation of R5. Lagarias's `A_delta`
definition supplies analyticity, closed-strip continuity, and a uniform transform bound, but no
vertical-decay field that would by itself remove the horizontal edges in the finite-height theorem.
The source treats the zero functional by a height cutoff and requires additional regularization for
larger classes. A complete contour/distributional passage is not one bounded successor campaign.

Five R1 candidates were then adversarially screened. Exact natural Gram evaluation and generic
projection identities do not control target residuals; Ehm's modified Levinson-Selberg route leaves
the decisive Mertens/Landau estimates explicitly open; and the previous geometric sparse family is
Lean-excluded by an exact orthogonal witness. The surviving candidate is Ehm's `q=2` variation of
the Baez-Duarte criterion, which is genuinely distinct from sparse target coupling.

`CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01` fixes the exact endpoint

```lean
RiemannHypothesis <->
  baezDuarteQTwoComplexTargetL2 in baezDuarteQTwoComplexKernelClosure
```

where the target is the multiplicative convolution of the unit-interval indicator with itself and
each generator is its convolution with the existing positive-natural kernel. The transform values
are fixed as `1 / s^2` and `n^(-s) * (-zeta(s) / s^2)`. The bounded critical-line multiplier proves
only the RH-forward direction; the reverse must independently reconstruct the zero obstruction,
because multiplication by `1/s` has no bounded inverse. This is a known RH-equivalent criterion,
so the expected RH `hard_gap_delta` is zero even on success.

## Portfolio Update: R1 q=2 Baez-Duarte Criterion Locally Complete

Date: 2026-07-15

`CAMPAIGN-20260715-R1-BAEZ-DUARTE-QTWO-01` reaches the exact fixed endpoint locally as
`KNOWN_THEOREM_FORMALIZED`. The new module constructs the twice-weighted target and natural
generators by multiplicative convolution, proves their exact Mellin transforms and reciprocal
tail, and transports the bounded critical multiplier by `1/s` through the Fourier-Mellin
isometry. This yields the RH-forward closure direction. The reverse direction independently
excludes off-critical zeta zeros through finite-sum Mellin vanishing, local Cauchy-Schwarz, and
tail-moment control; no inverse multiplier is assumed. The final theorem is
`riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure`.

The warning-free module, exact TargetChecks, eight standard-only axiom prints, five empty forbidden
scans, `git diff --check`, the 8,608-job module build, and the 8,668-job full build pass locally.
This is an exact known RH equivalence with `hard_gap_delta=0`, not an unconditional proof of RH.
Implementation commit `90313d83210bdfe0aca8b62153240d51e0c924b1` passed public Lean Action CI
run `29430307834`, build job `87403316754`, in `2m20s`. Evidence-backfill commit
`b5b8f0f3688cfef8d310ecc503d7f829dbc8e646` passed public Lean Action CI run `29430594438`, build
job `87404277090`, in `1m26s`. The campaign is publicly closed as `KNOWN_THEOREM_FORMALIZED`;
return to a fresh independent route audit.

## Portfolio Update: R5 Finite Gaussian Test Core Locally Complete

Date: 2026-07-16

Fresh route selection compared a direct Schwartz-density campaign with the algebraic test core
that must precede any closure argument. Arias de Reyna's explicit-formula proof confirms the
finite-core-then-continuity architecture. Fixed-width Gaussian-cosine density survived
mathematical falsification, but Mathlib currently lacks the packaged Hermite completeness or
compactly supported smooth Schwartz-density infrastructure needed to close it as one bounded
campaign. L2 density was rejected as too weak, and prime-distribution temperedness was rejected as
RH-equivalent.

`CAMPAIGN-20260716-R5-WEIL-FINITE-GAUSSIAN-TEST-CORE-01` reaches its preregistered endpoint
locally. `WeilFiniteGaussianTestCore.lean` defines arbitrary finite complex packets and proves the
complete explicit formula with the directly synthesized zero `tsum`, pole factor, GammaR
integral, and von-Mangoldt `tsum`. Both series are absolutely summable, the real-place integrand is
integrable, every finite interchange is explicit, and singleton and empty packets reduce exactly.
Exact TargetChecks, six standard-only axiom prints, empty forbidden/declaration/resource scans,
`git diff --check`, and the 8,672-job full build pass. Classification is `BRIDGE_REDUCED`: one G6
algebraic-core subedge closes locally, while Schwartz density, continuity, tempered extension,
regularization, Weil positivity, and RH remain open. Public commit and CI are pending.

Implementation commit `736901e03f08ccb399e4ec5f84980a641cb4e344` passed public Lean Action CI
run `29445905312`, build job `87456185038`, in `2m33s`. Immutable evidence backfill and its own
public CI remain before campaign closure.

Evidence-backfill commit `6d7433b694b60150c19ca67f85087ba0e0c6255b` passed public Lean Action CI
run `29446148141`, build job `87456989353`, in `1m26s`. The campaign is publicly closed as
`BRIDGE_REDUCED`; the persistent RH Goal remains active and must return to fresh route selection.

## Selection Update: R5 Gaussian-Weil Quadratic Positivity

Date: 2026-07-16

Fresh route selection first audited the proposed fixed-width Gaussian density continuation.
Mathlib supplies Schwartz seminorms, Fourier automorphisms, translations, and locally convex
separation, but it does not package the Gaussian/Hermite Schwartz-density or Wiener machinery
needed for the full endpoint. More importantly, extending the separated prime and zero
functionals by assumed continuity would hide the RH-equivalent temperedness issue identified by
Arias de Reyna. L2 density was rejected as too weak.

Campaign `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-QUADRATIC-POSITIVITY-01` therefore selects a narrower
and explicit conditional W2 bridge. For a common `a>0`, real shifts `b_i`, and real coefficients
`w_i`, it instantiates the finite packet formula on ordered pairs with shift `b_i-b_j` and
coefficient `w_i*w_j`. Under RH, every divisor zero contributes

```text
exp(-a*gamma^2) *
  ((sum_i w_i*cos(b_i*gamma))^2 + (sum_i w_i*sin(b_i*gamma))^2).
```

Lean closes the pointwise critical-line evaluation, finite Gram identity, summability of the real
square family, exact zero `tsum`, direct arithmetic formula, and real-part nonnegativity. The
formal module compiles without warnings with singleton and zero-coefficient boundary checks,
exact Targets/TargetChecks, seven standard-only axiom prints, empty forbidden scans,
`git diff --check`, and the 8,673-job full build. This is RH-forward only: unconditional arithmetic
sign, a converse criterion, Schwartz closure, separated temperedness, G7, and RH remain open.
Classification is locally `BRIDGE_REDUCED`, with zero unconditional RH hard-gap delta; public
evidence closure remains.

Implementation commit `cf271684f786efcb2e83a57d76c51e215205d1d1` passed public Lean Action CI
run `29447980403`, build job `87463120301`, in `1m49s`. At that gate, immutable evidence backfill
and its own public CI remained before campaign closure.

Evidence-backfill commit `dafcd758a5257718ed2c9f6c8813213a2821708e` passed public Lean Action CI
run `29448199280`, build job `87463856783`, in `1m32s`. The campaign is publicly closed as
`BRIDGE_REDUCED`. The conditional Gaussian kernel theorem is now public, but unconditional W2,
G7, and RH are unchanged; the persistent Goal remains active and returns to fresh route selection.

## Selection Update: R5 Gaussian-Weil Reverse Criterion

Date: 2026-07-16

Fresh route selection admits
`CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-REVERSE-CRITERION-01`. Its fixed endpoint is the exact
equivalence between RH and nonnegativity of the existing direct arithmetic quadratic for every
positive-width finite real Gaussian shift packet. The proposed reverse does not pass through
Schwartz density or separated temperedness. It selects a minimal off-line value of
`q=-Re((rho-1/2)^2)`, annihilates the finite lower/same unwanted layer by a real exponential
polynomial, locks the surviving target-square phase negative, and sends the strictly higher-layer
`tsum` to zero under a fixed width-one summable majorant.

Lean scratch already checks every high-risk component separately, including the real-axis
degeneracy handled by `P^2*(X-1)`. The campaign is therefore admitted to Proof Attempt A, but it
cannot close on helpers: the finite divisor layer, complete scaled zero-sum negativity, arithmetic
contradiction, and exact iff are indivisible. Completion would be an RH-equivalent criterion with
`hard_gap_delta=0`; unconditional W2, G7, and RH remain open.

Proof Attempt A reaches the exact endpoint locally in
`WeilGaussianPositivityCriterion.lean`. The final argument is stronger than the preregistered
selection step: it starts from an arbitrary off-line divisor zero, because the finite separator
can annihilate every unwanted lower or same-decay square class. The protected target contribution
is made strictly negative either by phase-locked widths or by the direct real-axis product, while
the scaled higher-decay `tsum` tends to zero under a fixed summable majorant. The existing explicit
formula then produces a finite arithmetic quadratic with negative real part and yields the reverse
implication to RH.

The 1,476-line module, exact Targets and TargetChecks, six standard-only transitive axiom prints,
empty forbidden scans, `git diff --check`, and the full 8,674-job build pass. Classification is
conservatively `KNOWN_THEOREM_FORMALIZED` pending independent novelty review, with no first-proof
claim. This closes the restricted-family reverse edge but has `hard_gap_delta=0` for unconditional
positivity, W2, G7, and RH. Implementation publication and public CI remain.

Implementation commit `b2d2ce18ff1491f684098b04c7a5be73e0ebdc98` passed public Lean Action CI
run `29453270303`, build job `87480595744`, in `2m14s`. The exact restricted Gaussian criterion is
now independently public-built. Immutable evidence backfill and its own public CI remain before
campaign closure; the persistent RH Goal stays active.

Evidence-backfill commit `68e96525f3f89562ae47e1da9e074911701a6c2e` passed public Lean Action CI
run `29453470463`, build job `87481233198`, in `1m24s`. Together with the implementation CI, this
publicly closes `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-REVERSE-CRITERION-01` conservatively as
`KNOWN_THEOREM_FORMALIZED`. Do not reopen the fixed restricted criterion without new evidence.
Return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; unconditional Gaussian positivity and RH
remain open, and the persistent Goal stays active.

## Selection Update: R5 Polson GGC Continuation Audit

Date: 2026-07-16

Fresh route selection moves to `FALSIFICATION` and admits
`AUDIT-20260716-R5-POLSON-GGC-CONTINUATION-01`. Polson's 2018 GGC source first derives a
Levy-Frullani integral for positive real spectral displacement, then evaluates the same integral
after a large imaginary substitution. The 2026 SSRN abstracts use a more conservative structure:
right-half-plane density positivity is unconditional, while the critical-line Thorin sign is an
RH-equivalent residual condition.

Five candidate mechanisms were screened. Unconditional centre positivity, pointwise-to-complete
monotonicity, discreteness of arbitrary Bernstein measures, and unrestricted preservation of an
integral under analytic continuation fail admission. The selected exact endpoint isolates one
exponential mixing component: at `s=i*y` its real integrand is

```text
(exp((y^2/2-gamma^2)*t)-exp(-gamma^2*t))/t.
```

When `gamma>0` and `y^2>2*gamma^2`, this tail should be nonintegrable. A Lean proof would eliminate
only the 2018 integral-retention mechanism; it would not disprove analytic continuation, the 2026
RH-equivalent Thorin framework, or RH. G6/W1 and G7/W2 remain open, G3/M2 was historically unselected (open under V4.1), and the
expected `hard_gap_delta` is zero.

The fixed endpoint is now locally complete in `PolsonGGCContinuationAudit.lean`. Lean identifies
the exact complex component at `s=i*y` with the real displayed integrand and proves that neither
is integrable on `(1,infinity)` under `gamma>0` and `y^2>2*gamma^2`. Exact Targets and
TargetChecks, three standard-only transitive axiom prints, empty forbidden and scratch-name scans,
`git diff --check`, and the full 8,675-job build pass. The classification is
`BRANCH_ELIMINATED`: only retention of the 2018 defining integral in this imaginary regime is
rejected. Analytic continuation, the revised 2026 RH-equivalent Thorin program, G6/W1, G7/W2,
G3/M2, and RH are unchanged. At that local gate, implementation publication and public CI
remained.

Implementation commit `0c174e82713c18be16ae9ea3afd5197b77ab4347` passed public Lean Action CI
run `29455171888`, build job `87486632024`, in `1m50s`. The source-specific branch elimination is
now independently public-built. Immutable evidence backfill and its own public CI remain before
audit closure; the persistent RH Goal stays active.

Evidence commit `d277252fa21de89e228a2d1db6addd727d975d99` passed public Lean Action CI
run `29455360041`, build job `87487225276`, in `2m2s`. Together with implementation run
`29455171888`, this publicly closes `AUDIT-20260716-R5-POLSON-GGC-CONTINUATION-01` as
`BRANCH_ELIMINATED`. Do not reopen the exact tested 2018 integral-retention mechanism without new
source evidence. Return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; the unconditional RH
frontier is unchanged and the persistent Goal remains active.

## Selection Update: R4 Freedman Green-Lift Contraction Audit

Date: 2026-07-16

After compaction, fresh route selection re-audited the fixed DAG rather than extending the previous
source branch. G6/W1, G7/W2, and G3/M2 are open. The selected new input is Freedman's arXiv
`2606.29555`, a Weyl/Volterra reduction paper
that explicitly leaves the final KLM/de Branges/RH bridge open but describes its normalized
Green-lift contraction as closed.

Five source mechanisms were screened. The theta differential identity is exact but mechanical;
the finite trace-frame constant and uniform-parameter passage are not stated with enough rigorous
data for a faithful endpoint; and the final KLM pullback is explicitly open. Audit
`AUDIT-20260716-R4-FREEDMAN-GREEN-LIFT-CONTRACTION-01` selects the displayed inference from
`G_-=C K E G_+`, pointwise contraction of `K`, and trace-fiber Euler--Lagrange orthogonality to
contraction of `C K E`.

A fixed two-dimensional real model has a nontrivial trace kernel, satisfies all those listed
premises exactly, but makes `C K E` multiplication by two and the signed Green form equal to `-3`
at the unit trace. Lean must check the complete premise bundle and also record the repaired
three-map contraction condition. Completion eliminates only the source's listed-premise closure
argument; it does not disprove a stronger concrete Volterra estimate, KLM positivity, or RH.
Expected `hard_gap_delta=0`.

The fixed endpoint is now locally complete in `FreedmanGreenLiftAudit.lean`. Lean checks a
nontrivial trace kernel, exact Green representative, trace-fiber Euler--Lagrange orthogonality,
contractive middle multiplier, and `G_-=C K E G_+`, while `C K E` expands the unit input from one
to two and the signed Green form is exactly `-3`. The same batch proves that separate contraction
bounds for all three maps would repair the abstract inference.

Exact Targets and TargetChecks, two standard-only transitive axiom prints, empty forbidden and
scratch-name scans, `git diff --check`, the 2,966-job module build, and the full 8,676-job build
pass. Classification is `BRANCH_ELIMINATED` only for the listed-premise closure argument. A
stronger concrete Volterra energy estimate, KLM positivity, the final de Branges/RH bridge, G6/W1,
G7/W2, G3/M2, and RH remain open. At that local gate, implementation publication and public CI
remained.

Implementation commit `b360163ccdad0d0076408c2a65eee99d2d4df7b5` passed public Lean Action CI
run `29456581043`, build job `87490980870`, in `2m7s`. The listed-premise countermodel is now
independently public-built. Immutable evidence backfill and its own public CI remain before audit
closure; the persistent RH Goal stays active.

Evidence commit `779a8092992e85b8e8a4b3a57a872456dd7fc1d9` passed public Lean Action CI
run `29456771395`, build job `87491571306`, in `1m47s`. Together with implementation run
`29456581043`, this publicly closes
`AUDIT-20260716-R4-FREEDMAN-GREEN-LIFT-CONTRACTION-01` as `BRANCH_ELIMINATED`. Do not reuse the
listed-premise contraction inference without a concrete surrounding-map norm theorem or exact
energy identity. The broader R4 route and the persistent RH Goal remain active; return to fresh
`INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Portfolio Update: R5 Fixed-Width Gaussian Criterion Publicly Closed

Date: 2026-07-16

Fresh DISCOVERY route selection asked whether the all-width Gaussian-Weil criterion could be
compressed to one arbitrary positive width without assuming a Bochner representation or a
tempered extension. Campaign `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-FIXED-WIDTH-01` uses the finite
Rademacher multiplier `cosh(sqrt(c/n)*z)^n`; its paired multiplier converges to `exp(c*z^2)`, is
uniformly bounded on centered xi zeros, and remains inside the finite real shift algebra.
Dominated convergence transfers every larger-width zero and arithmetic quadratic back to the
fixed base width. The threshold-strengthened W2g1 separator then gives the exact fixed-width iff.

The exact theorem, target witnesses, standard-only axiom audit, forbidden scans, diff check, and
8,677-job full build pass. Implementation `f56b70478ab552802cac719b8e9af0f56fc44b1d`, evidence
`f93e73cbdd71785a28cc2b05f8ef2b0390b358cf`, and closure
`8b45a091aa4f16e348a2cd8b73e949480f446508` each passed public CI runs `29458594435`,
`29458788171`, and `29458987040`. The campaign is publicly closed as
`NEW_RELEVANT_LEAN_THEOREM` pending independent novelty review. It has `hard_gap_delta=0` for
unconditional W2, G7, and RH; return to a fresh route and do not reopen width compression without
a strictly stronger endpoint.

## Selection Update: R5 Compact Laplace Xi-Divisor Separator

Date: 2026-07-16

Fresh LITERATURE route selection compares five source-aligned candidates after W2g2 closure. The
full Connes--Consani archimedean operator theorem is deferred because its decisive spectrum bound
depends on prolate functions and a large computer-assisted approximation. Generic strip-class
integration still lacks vertical decay; immediate Hermite density would hide an unproved
tempered-extension step; and another Gaussian width reformulation violates anti-cycling.

Campaign `CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01` selects the compact-support
interpolation mechanism underlying Connes--Consani Appendix C and Yoshida's compact-support Weil
criterion. Its exact endpoint is a smooth compactly supported function on the logarithmic line
whose bilateral Laplace transform equals one at a chosen multiplicity-bearing xi zero and has
arbitrarily small absolute `tsum` over all different xi-zero values. The construction uses a
target-modulated positive bump, twofold integration by parts, a finite exponential polynomial on
one fixed transform superlevel, and compact convolution powers.

This is an unconditional W1 reverse-separation component, not the generic explicit formula,
unconditional Weil positivity, or RH. G6/W1 and G7/W2 remain open and expected hard-gap delta is
zero. The exact statement, adversarial tests, source boundary, and rejection conditions are fixed
in `research/r5_compact_laplace_separator_prereg_20260716.md` before Lean proof edits.

## Local Completion Update: R5 Compact Laplace Xi-Divisor Separator

Date: 2026-07-16

The exact endpoint now compiles in `LeanLab/Riemann/WeilCompactLaplaceSeparator.lean`. A fixed
unit-integral bump is modulated at the protected xi zero; two integrations by parts give a
strip-uniform reciprocal-square bound and absolute summability over the complete analytic
divisor. The `norm(F)>=1/2` non-target value set is finite, a positive real exponential shift and
normalized polynomial annihilate it once, and compact convolution powers suppress every remaining
term by a geometric factor. Equal-value multiplicity copies are excluded from the tail exactly as
preregistered.

Targets, exact statement witnesses, selected standard-only axiom prints, repository scans, and the
full 8,678-job build pass locally. Classify
as `KNOWN_MECHANISM_RECONSTRUCTED`, with `hard_gap_delta=0`: this supplies an unconditional W1
reverse-separation component but not the generic explicit formula, unconditional Weil positivity,
G7/W2, or RH. Publication and public CI remain before campaign closure.

Implementation commit `6d12bad98b80c34217757df01943509965a64781` passed public Lean Action CI
run `29461298466`, build job `87505125618`, in `1m47s`. The exact separator theorem is now
independently public-built. Immutable evidence backfill and its own public CI remain before local
campaign closure; all RH hard gaps are unchanged.

## Public Closure Update: R5 Compact Laplace Xi-Divisor Separator

Date: 2026-07-16

Evidence commit `941756c2e7e0b4da8f765dc7187e4be703af36c8` passed public Lean Action CI
run `29461494669`, build job `87505716647`, in `2m22s`. Together with implementation commit
`6d12bad98b80c34217757df01943509965a64781` and run `29461298466`, campaign
`CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01` is publicly closed at its exact endpoint.
Return the persistent RH Goal to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; generic W1c1,
unconditional Weil positivity, G7/W2, and RH remain open, with `hard_gap_delta=0`.

## Selection Update: R5 Gaussian Prime-Kernel Sign Audit

Date: 2026-07-16

Fresh DISCOVERY route selection rejects an immediate compact-separator RH criterion because it
would repeat the already compiled Gaussian reverse-separation mechanism. It also rejects full
fixed-width arithmetic positivity as an auxiliary target because the project has proved that
statement equivalent to RH.

Five local arithmetic-kernel mechanisms were screened. The surviving falsification target is the
actual `n=2` symmetric Gaussian von-Mangoldt translation kernel at width `(log 2)^2/16`: its
two-point matrix at shifts `0, log 2` is conjectured to have both a negative quadratic direction
and a positive diagonal direction. Audit
`AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01` preregisters exact two-sided indefiniteness.
Success eliminates termwise semidefinite local-prime assembly as a G7 mechanism but leaves
complete pole/archimedean/prime cancellation, W1c1, W2/G7, and RH open; expected
`hard_gap_delta=0`.

## Local Completion Update: R5 Gaussian Prime-Kernel Sign Audit

Date: 2026-07-16

The exact endpoint now compiles in `LeanLab/Riemann/WeilGaussianPrimeKernelSignAudit.lean`. Lean
checks the actual complex square-root prefactor, `vonMangoldt 2 = log 2`, the positive witness
width, exact diagonal/off-diagonal formulas, strict exponential comparison, and both matrix-sign
counterwitnesses. Thus one local prime-power kernel is genuinely indefinite.

This closes the audited branch as `BRANCH_ELIMINATED`: unconditional Weil positivity cannot be
obtained by assigning one common semidefinite sign to each Gaussian prime-power translation
kernel. Global cancellation and operator mechanisms are untouched. Exact targets, typed witness,
four standard-only axiom prints, scans, and the full 8,679-job build pass locally. W1c1, W2/G7,
and RH remain open, with `hard_gap_delta=0`; publication and public CI remain.

Implementation commit `01ea63517670a81b8c640de1135dec62d44436b9` passed public Lean Action CI
run `29462677629`, build job `87509304721`, in `1m54s`. The exact arithmetic-kernel obstruction is
now independently public-built. Immutable evidence backfill and its own public CI remain before
audit closure; all RH hard gaps are unchanged.

## Public Closure Update: R5 Gaussian Prime-Kernel Sign Audit

Date: 2026-07-16

Evidence commit `af7848aea84287329ce50900d5e425538165baaa` passed public Lean Action CI run
`29462828680`, build job `87509738532`, in `1m58s`. Together with implementation commit
`01ea63517670a81b8c640de1135dec62d44436b9` and run `29462677629`, audit
`AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01` is publicly closed as
`BRANCH_ELIMINATED`. Do not reuse termwise same-sign local-prime assembly without a genuinely
global cancellation mechanism. W1c1, W2/G7, and RH remain open, with `hard_gap_delta=0`; return
the persistent Goal to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`.

## Selection Update: R5 Compact Weil Zero Cutoff

Date: 2026-07-16

Fresh LITERATURE route selection audits the classical smooth compact-support Weil formula rather
than extending the closed local-prime sign branch. The existing generic selected-height rectangle
theorem reduces the zero-side problem to four exact premises, but the current compact Laplace
module supplies only reciprocal-square decay on the xi strip. That decay is insufficient against
the selected top edge's compiled fourth-power logarithmic-derivative bound.

Five source-aligned endpoints were screened. A full compact arithmetic formula is deferred as the
natural successor because it adds Fourier inversion and physical finite-prime support; prime
inversion alone and pole/Gamma estimates are incomplete endpoints; and another compact reverse
criterion repeats the Gaussian separator route. Campaign
`CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01` selects the generic zero-side passage for the
reflection symmetrization of every smooth compactly supported log-line function.

The proposed mechanism proves transform entire-ness, divisor summability, and sixfold integration-
by-parts decay on the full fixed rectangle strip. The resulting `O(R^(-6))` weight absorbs the
compiled `O(R^4)` xi bound and makes the top integral `O(R^(-2))`. Success reduces the fixed W1c1
compact zero-side subedge but does not evaluate the arithmetic side, prove W2/G7, or prove RH. The
exact endpoint and rejection conditions are fixed in
`research/r5_compact_weil_zero_cutoff_prereg_20260716.md` before Lean proof edits.

## Local Completion Update: R5 Compact Weil Zero Cutoff

Date: 2026-07-16

The exact endpoint now compiles in `LeanLab/Riemann/WeilCompactLaplaceZeroCutoff.lean`. Dominated
complex differentiation makes the compact Laplace transform entire; two-term reflection
symmetrization is exact; xi-divisor reflection preserves analytic multiplicity and gives absolute
summability; and arbitrary compact-support integration by parts supplies sixfold decay on the full
fixed rectangle strip. This absorbs the compiled fourth-power xi logarithmic-derivative bound and
makes the selected top integral `O(R^(-2))`.

The 373-line module, exact Targets and TargetChecks, five standard-only axiom prints, empty
forbidden scans, aggregate import, `git diff --check`, and the full 8,680-job build pass locally.
Classify as `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the fixed W1c1 compact zero-side
subedge. The compact arithmetic explicit formula, W2/G7, and RH remain open. Preregistration
commit `e70201cb71b0909ae3f7b798336931e0bd9f32ee` passed public CI run `29463597042`;
implementation publication and public CI were the next required evidence gate.

Implementation commit `0e6451944ee1edb2d76d67f4fe097de2aa19ad17` passed public Lean Action CI
run `29464308480`, build job `87514106839`, in `2m10s`. The exact compact-smooth zero-side
endpoint is independently public-built. Immutable evidence backfill and its own public CI remain
before campaign closure at that stage; the open arithmetic and positivity frontiers are unchanged.

## Public Closure Update: R5 Compact Weil Zero Cutoff

Date: 2026-07-16

Evidence commit `6c2f3ab912097e4e5b325e9d0c27d43438a29d99` passed public Lean Action CI
run `29464469804`, build job `87514591845`, in `1m43s`. Together with preregistration run
`29463597042` and implementation commit `0e6451944ee1edb2d76d67f4fe097de2aa19ad17`, run
`29464308480`, campaign `CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01` is publicly closed as
`BRIDGE_REDUCED`. Return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; the compact arithmetic
explicit formula, W2/G7, G3/M2, and RH remain open.

## Selection Update: R5 Compact Weil Arithmetic Formula

Date: 2026-07-16

After public closure of the compact zero-side cutoff, fresh DISCOVERY route selection audits the
remaining W1c1 arithmetic subedge. Mathlib already turns smooth compact-support functions into
Schwartz maps and supplies Fourier inversion; the project supplies sixth-order compact decay, the
generic two-pole residue skeleton, digamma growth, the von-Mangoldt L-series, and the selected xi
zero-side limit.

Five candidates were screened. Prime inversion alone, generic pole/Gamma helpers alone, and finite
physical support alone are incomplete endpoints. A new compact RH positivity criterion would
repeat the compiled Gaussian reverse separator without an unconditional sign mechanism. Campaign
`CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01` therefore selects the complete
compact-smooth formula with an explicit finite von-Mangoldt side.

The fixed endpoint must recover the exact physical weight
`pi*vonMangoldt(n)*(f(log n)+f(-log n)/n)`, prove its finite natural support, evaluate the pole pair
as `2*pi*F(1)`, prove GammaR integrability, and assemble these with the complete multiplicity-
bearing zero sum. Success reduces the fixed W1c1 compact arithmetic subedge but does not prove
quotient/completeness, regularization, W2/G7, G3/M2, or RH. Exact rejection conditions are fixed in
`research/r5_compact_weil_arithmetic_formula_prereg_20260716.md` before Lean proof edits.

## Local Completion Update: R5 Compact Weil Arithmetic Formula

Date: 2026-07-16

The exact fixed endpoint now compiles in
`LeanLab/Riemann/WeilCompactLaplaceArithmeticFormula.lean`. Mathlib Schwartz inversion gives the
two exact physical branches with `2*pi` scaling; after reflection symmetrization the von-Mangoldt
weight is `pi*Lambda(n)*(f(log n)+f(-log n)/n)`. Lean separately proves this natural-index weight
has finite support from compactness of `tsupport f`.

The compiled generic pole rectangle plus inverse-sixth selected-edge decay gives the exact
`2*pi*F(1)` pole term. A first-absolute-moment Schwartz estimate absorbs the digamma growth and
proves GammaR integrability. Finite-edge splitting and three full-line limits then match the
publicly closed zero-side limit and prove the complete formula with multiplicity.

Standalone compilation, exact Targets and TargetChecks, five standard-only axiom prints, empty
forbidden scans, aggregate import, `git diff --check`, and the full 8,681-job build pass locally.
Classify as `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at W1c1c1. Quotient/completeness,
distributional regularization, W2/G7, G3/M2, and RH remain open. Preregistration commit
`ccebc64b1f3419636461e6fbf968fc55c4f24b8c` passed public CI run `29465070647`; implementation
publication and public CI remain.

## Public Implementation Update: R5 Compact Weil Arithmetic Formula

Date: 2026-07-16

Implementation commit `55a6406f235a7548bf7f7d53ae5d30014795e9ce` passed public Lean Action CI
run `29466850965`, build job `87521708037`, in `1m51s`. The exact compact-smooth arithmetic
formula and its finite physical prime side are independently public-built. Immutable evidence
backfill and its own public CI remain before campaign closure; all broader hard gaps are unchanged.

## Public Closure Update: R5 Compact Weil Arithmetic Formula

Date: 2026-07-16

Evidence commit `ed5d03f65bd234f95afb55389b2766d611a3eeab` passed public Lean Action CI run
`29467021669`, build job `87522220122`, in `1m43s`. Together with preregistration run
`29465070647` and implementation run `29466850965`, campaign
`CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01` is publicly closed as
`BRIDGE_REDUCED`. W1c1c1 is complete for the compact-smooth reflection class; the persistent RH
Goal returns to fresh route selection with quotient/completeness, regularization, W2/G7, G3/M2,
and RH still open.

## Selection Update: R5 Compact C6 Explicit Formula

Date: 2026-07-16

Fresh FALSIFICATION route selection first re-audits the remaining W1/W2 interfaces and the open
Baez-Duarte/Burnol route. Wong's maximum-norm contraction and Carvill's ladder-frequency estimate
remain Lean-falsified; the sparse `(2^24)^j` family has a checked lower frame bound but also a
checked orthogonal target witness. Ehm's exact Gram identities do not supply the missing natural
target residual estimate.

The new Pyvovarov preprint arXiv `2607.12084v1` supplies exponential-damping identities, but it
explicitly leaves continuity of the approximant norm at zero as the difficulty. That step is the
RH-equivalent target-coupling frontier. The raw Lagarias strip class is also not an immediate
successor: it is nonseparated on the physical carrier and its bounded transform has no vertical
decay field. Unconditional compact positivity would repeat the closed Gaussian reverse route.

Campaign `CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01` therefore selects the exact
finite-regularity successor. The current compact formula requires `C-infinity` only because its
Fourier inversion and first moment use a Schwartz wrapper; the contour estimate itself uses six
derivatives. The fixed endpoint proves the unchanged multiplicity-bearing zero/pole/GammaR/finite-
prime identity from `ContDiff R 6 f` and compact support, while preserving the old smooth theorem
as a corollary. Success reduces only the W1 compact finite-regularity subedge; quotient/completion,
full-class regularization, W2/G7, G3/M2, and RH remain open. Exact adversarial and rejection
conditions are preregistered in
`research/r5_compact_c6_explicit_formula_prereg_20260716.md` before Lean proof edits.

## Local Completion Update: R5 Compact C6 Explicit Formula

Date: 2026-07-16

The exact preregistered endpoint now compiles as
`symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff`. The compact zero-cutoff
module derives the required transform identities and selected top-edge limit from exactly six
continuous derivatives. The arithmetic module no longer passes through a Schwartz wrapper:
continuity plus inverse-square Fourier decay proves ordinary Fourier inversion, while inverse-sixth
decay proves the first absolute Fourier moment needed for the GammaR term.

The old `C-infinity` theorem remains as a compatibility corollary. Independent compilation of both
analytic modules, exact Targets and TargetChecks, five standard-only axiom prints, empty forbidden
scans, `git diff --check`, and the full 8,681-job build pass locally. Preregistration commit
`540b0ddcbf90a219084f8fdcb80a02ddaad5e277` passed public CI run `29467845311`, build job
`87524663724`.

Classify as `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at `W1c1c2`, the compact finite-
regularity subedge. Quotient/completeness, full-class regularization, W2/G7, G3/M2, and RH remain
open. Implementation publication and independent public CI are the next evidence gate.

## Public Implementation Update: R5 Compact C6 Explicit Formula

Date: 2026-07-16

Implementation commit `3e3c677495c592096d7843aa4845e861bc393937` passed public Lean Action CI
run `29468797210`, build job `87527584998`, in `2m0s`. The exact compact C6 arithmetic formula,
finite-order Fourier inversion, selected top-edge limit, and old smooth compatibility theorem are
independently public-built. Immutable evidence backfill and its own public CI remain before
campaign closure; all broader hard gaps are unchanged.

## Public Closure Update: R5 Compact C6 Explicit Formula

Date: 2026-07-16

Evidence-backfill commit `94b6be8fc934b3d4909d066b168491389df9afd8` passed public Lean Action CI
run `29468980147`, build job `87528144506`, in `1m56s`. Together with preregistration run
`29467845311` and implementation commit `3e3c677495c592096d7843aa4845e861bc393937`, run
`29468797210`, campaign `CAMPAIGN-20260716-R5-COMPACT-C6-EXPLICIT-FORMULA-01` is publicly closed
as `BRIDGE_REDUCED`.

`W1c1c2` is complete for compactly supported additive-log functions with six continuous
derivatives. The persistent RH Goal returns to fresh route selection with quotient/completeness,
full-class regularization, W2/G7, G3/M2, and RH still open.

## Selection Update: R5 Compact Weil Criterion

Date: 2026-07-16

Fresh LITERATURE route selection uses the newly public compact C6 formula and complete-divisor
compact separator as specific new evidence. Five candidates were screened. Delsarte rapid-strip
extension needs a new infinite prime/distribution topology; raw strip completion is nonseparated
and has no decay; Arias de Reyna temperedness is RH-equivalent; and the semi-local operator route
requires prolate and computer-assisted infrastructure. Only Connes--Consani Appendix C,
Proposition C.1 has a complete adjacent mechanism.

Campaign `CAMPAIGN-20260716-R5-COMPACT-WEIL-CRITERION-01` therefore fixes the arbitrary-finite-set
compact-support criterion. For every finite `F` containing `0,1` and disjoint from the nontrivial
zeros, it must prove RH equivalent to nonnegativity of the exact compact arithmetic Weil quadratic
for every smooth compactly supported additive-log function whose Laplace transform vanishes on
`F`.

The proof must construct the source conjugate-reflection convolution square, strengthen the
separator with exact finite-set vanishing, and build a strictly negative complete zero quadratic
from any off-line zero. The public compact explicit formula then transfers the zero criterion to
the finite-prime/GammaR arithmetic side and the endpoint moments remove the pole term. Success
changes only the source-level W1/G6 compact-criterion edge; unconditional W2/G7 positivity and RH
remain open. The exact endpoint and rejection conditions are fixed in
`research/r5_compact_weil_criterion_prereg_20260716.md` before Lean source edits.

## Local Completion Update: R5 Compact Weil Criterion

Date: 2026-07-16

The exact arbitrary-finite-`F` endpoint now compiles as
`riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg`. The additive-log conjugate
involution has transform `conj(G(1-conj(s)))`; its autocorrelation gives norm squares under RH.
The public compact explicit formula identifies the finite-prime/GammaR arithmetic quadratic with
`pi` times the complete divisor quadratic once `G(0)=G(1)=0`.

The converse strengthens the compact separator with exact finite-set vanishing. From an off-line
zero `rho`, two separators produce transform values `1` at `rho` and `-1` at
`1-conj(rho)`. The complete tail estimate uses existence of an index for each conjugate-reflected
zero rather than an unproved multiplicity-preserving conjugation permutation. Equal-value
multiplicity copies contribute additional negative terms.

Exact module, Target, and TargetCheck compilation, six standard-only transitive axiom prints,
empty forbidden scans, `git diff --check`, and the full 8,682-job build pass locally. Classification
is `KNOWN_THEOREM_FORMALIZED` with `hard_gap_delta=1` at the source-level W1/G6 compact criterion
edge once implementation publication and independent public CI pass. Unconditional W2/G7
positivity, RH, and the optional Delsarte/distributional extension remain open.

## Public Implementation Update: R5 Compact Weil Criterion

Date: 2026-07-16

Implementation commit `d590ee42e37366388800bafda04020a84eee8452` passed public Lean Action CI
run `29487332091`, build job `87584836879`, in `1m53s`. The exact arbitrary-finite-`F` RH
equivalence, constrained compact separator, conjugate-reflection autocorrelation, and complete
off-line negative arithmetic witness are independently public-built. Immutable evidence backfill
and its own public CI remain before campaign closure; W2/G7 and RH remain open.

## Public Closure Update: R5 Compact Weil Criterion

Date: 2026-07-16

Evidence-backfill commit `03e1661b077ab8d3e2f8c9b93b19aa63c3c1eebc` passed public Lean Action CI
run `29487596817`, build job `87585683179`, in `2m6s`. Together with preregistration run
`29484731600` and implementation commit `d590ee42e37366388800bafda04020a84eee8452`, run
`29487332091`, campaign `CAMPAIGN-20260716-R5-COMPACT-WEIL-CRITERION-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

The source-level compact-support RH-equivalent Weil criterion is complete for arbitrary finite
zero-free `F` containing `0,1`. This changes one W1/G6 compact-criterion edge only. It does not
prove the arithmetic quadratic nonnegative unconditionally, so W2/G7 and RH remain open; the
full-class quotient/completeness and distributional extension also remain open. The persistent RH
Goal returns to fresh independent route selection.

## Exposure Sprint Update: public review surface

Date: 2026-07-16

The post-campaign independent audit starts an exposure sprint as the first priority while proof
campaigns remain open in parallel. The placeholder public README is replaced by exact statements
for the Baez-Duarte, Li, Li-Weil Gram, and compact Weil criterion spines, together with a trust-base
and open-gap declaration. PNT+ provenance is fixed at upstream commit
`d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, with repository snapshot dates recorded.

A bounded novelty audit found no exact counterpart in the pinned mathlib tree, the inspected PNT+
surface, the official AFP catalog queries, or selected external Lean repositories. This result is
deliberately weaker than a global novelty claim and does not license "first formalization"
language. P3 is complete only within the published fixed scope.

The older clean-context Sol review remains evidence only for the Baez-Duarte/contour surface. The
new Sol max review of the Li/Weil spine completed P1b with no P0-P2 issue and two P3 wording
corrections. Two browser attempts failed before Lean Zulip loaded, so no message was sent and P2
remains pending as a human-authored publication action. These are output-readiness states, not
proof-admission gates. Current authority is `research/rh_governance_current.md`; RH, W2/G7, and
M2/G3 are open for direct preregistered attacks.

Local closure verification compiles Targets, exact TargetChecks, and the complete AxiomsAudit;
all printed dependencies remain standard-only. Forbidden scans and `git diff --check` are clean,
and the full 8,682-job build succeeds. Exposure engineering is complete apart from the human-owned
P2 publication action; route selection may proceed in parallel under V4.1.

## Local Completion Update: H6 Time-Zero Xi Bridge

Date: 2026-07-17

Campaign `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01` reaches its exact indivisible endpoint as
`deBruijnNewmanH_zero_eq_riemannXi`. The new source module explicitly defines the Polymath theta
kernel and heat family, proves the required super-exponential convergence and integration by
parts, converts the self-dual theta Mellin integral by `x=exp(4*u)`, and derives
`H_0(z)=(1/8)*riemannXi((1+i*z)/2)` without a tautological definition.

The exact module, Targets, TargetChecks, four standard-only axiom prints, empty forbidden scans,
and the full 8,683-job build pass locally. Classification is `KNOWN_THEOREM_FORMALIZED`, with
`hard_gap_delta=0` and `route_infrastructure_delta=1`. H6-H/H6-E, including the heat-flow zero
framework and `Lambda <= 0`, remain open together with W2/G7, M2/G3, and RH. Implementation
commit and public CI evidence are pending.

## Public Implementation Update: H6 Time-Zero Xi Bridge

Date: 2026-07-17

Implementation commit `b7824a3b3f3d206617f0a23b124959b6edad937d` passed public Lean Action CI run
`29500096845`, build job `87626587502`, in `2m37s`. The independent build verifies the explicit
theta kernel, completed-zeta Mellin conversion, global integration-by-parts chain, exact Target
witnesses, and standard-only axiom audit. Immutable evidence backfill and its own public CI remain
before campaign closure; H6-H/H6-E and RH are unchanged.

## Public Closure Update: H6 Time-Zero Xi Bridge

Date: 2026-07-17

Evidence commit `8b9bd1c10000a518ff2f689a69f6431fba412281` passed public Lean Action CI run
`29500378390`, build job `87627536976`, in `1m28s`. Together with preregistration run
`29493974202` and implementation commit `b7824a3b3f3d206617f0a23b124959b6edad937d`, run
`29500096845`, campaign `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

The reusable gain is an exact, source-defined H6 time-zero family connected to project xi, plus
the theta-Mellin and integration-by-parts lemmas needed to justify that connection. No zero
location theorem was proved: `hard_gap_delta=0`, while `route_infrastructure_delta=1`. H6-H/H6-E,
W2/G7, M2/G3, and RH remain open. The persistent Goal returns to fresh independent route
selection; no successor campaign is selected by this closure record.

## Selection Update: H6 Entire Heat Equation

Date: 2026-07-17

Fresh LITERATURE selection compares H6-H with H6-X, direct H6-E/H6-Q, H1-B, H2-B, H10 census
work, W2/G7, and M2/G3. Campaign `CAMPAIGN-20260717-H6-HEAT-EQUATION-01` selects the exact source
analytic interface: for every real `t`, the compiled `H_t` must be entire in complex `z`,
differentiable in real time, and satisfy `partial_t H_t=-partial_z^2 H_t`, with both derivatives
identified by the same `u^2`-weighted integral.

The source normalization and H0-xi bridge are already public. The remaining fixed obstacle is
uniform domination of the source double-exponential series after arbitrary fixed quadratic and
linear exponential weights. H6-X depends on this interface; H1-B/H2-B have lower immediate
leverage; H10 remains the next census card; and no materially new W2 or M2 attack angle was found
in this selection. The exact success and falsification criteria are preregistered before Lean proof
edits in `research/h6_de_bruijn_newman_heat_equation_prereg_20260717.md`.

## Local Completion Update: H6 Entire Heat Equation

Date: 2026-07-17

Campaign `CAMPAIGN-20260717-H6-HEAT-EQUATION-01` reaches its exact endpoint. The reusable majorant
`integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi` absorbs arbitrary fixed nonnegative
quadratic and real linear exponential weights together with the `u^2` moment. Dominated parameter
integration proves `H_t` entire in complex space for every real `t`, identifies the real-time and
second spatial derivatives with the same source moment, and compiles
`deBruijnNewmanH_backward_heat_equation` on all `R x C`.

The new module is diagnostic-free. Targets, five exact TargetChecks, five standard-only axiom
prints, all forbidden scans, `git diff --check`, and the full 8,684-job build pass locally.
Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. H6-H2's all-real-zero/threshold theory, H6-E/G8, W2/G7, M2/G3,
and RH remain open. Implementation commit `cc62a398160c5865861de0d667b3683ac57694b1` passed public
Lean Action CI run `29504396806`, build job `87641274871`, in `2m9s`. Immutable evidence backfill
and its own public CI are still required.

## Public Closure Update: H6 Entire Heat Equation

Date: 2026-07-17

Evidence commit `535554372f1e04a3f3c409ae93e0b3e9d7cac04a` passed public Lean Action CI run
`29504634992`, build job `87642099186`, in `1m32s`. Together with preregistration run
`29501372019` and implementation commit `cc62a398160c5865861de0d667b3683ac57694b1`, run
`29504396806`, campaign `CAMPAIGN-20260717-H6-HEAT-EQUATION-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

The reusable gain is the exact all-real-time entire heat evolution and its source moment
derivatives. No zero-location or threshold theorem was proved: `hard_gap_delta=0`, while
`route_infrastructure_delta=1`. H6-H2, H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent
Goal returns to fresh independent route selection; no successor campaign is selected here.

## Selection Update: H10 Finite Spectral Rigidity

Date: 2026-07-17

Fresh selection compares direct H6-E/H6-Q, H6-H2, H6-X, W2/G7, M2/G3, H1-B, H2-B, and the
required H10 census. No materially new unconditional mechanism appears in the three hard-gap
routes. Continuing H6 would presently add another equivalence layer. H10 instead supplies a new
structural route with a primary-source exact endpoint and a reusable compiled phase tool.

Campaign `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01` selects the final spectral step of the
Bombieri-Stepanov function-field proof: an aggregate power-sum bound at radius `R` must control
each member of a finite complex spectrum despite cancellation, and functional-equation reciprocal
pairing at `R=sqrt(q)` must force the exact critical circle. The card records that finite Frobenius
spectrum, all-extension point counts, and uniform tail absence are precisely what do not transfer
to the number-field zero divisor. Exact success/falsification criteria are preregistered before
Lean proof edits in `research/h10_finite_spectral_rigidity_prereg_20260717.md`.

## Local Completion Update: H10 Finite Spectral Rigidity

Date: 2026-07-17

Campaign `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01` reaches both exact clauses locally.
`norm_le_of_forall_norm_finiteComplexPowerSum_le` proves that an all-natural-power aggregate bound
controls each member of an arbitrary finite complex family. Its proof aligns all nonzero unit
phases near `1` at one arbitrarily large power, so every real part is nonnegative and a value with
norm above `R` cannot be hidden by cancellation. Zeros, duplicates, exact opposite phases, and
arbitrary finite index types are included. `norm_eq_sqrt_of_powerSum_bound_and_reciprocal` then
uses reciprocal product pairing to force every norm to equal `sqrt(q)`.

The standalone module is diagnostic-free. Both exact TargetChecks, both standard-only axiom
prints, forbidden-token/declaration/resource scans, `git diff --check`, and the 8,685-job full
build pass locally. Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. The unresolved work is the actual curve point-count theorem and,
for number-field RH, a finite trace spectrum or uniform infinite-tail mechanism that does not
exist in the current route. Preregistration commit
`af15b161049aedd65d46fd1f2af1f27e8dc69d44` passed public CI run `29505635350`, job
`87645529929`, in `1m56s`; implementation publication and public CI remain pending.

## Public Implementation Update: H10 Finite Spectral Rigidity

Date: 2026-07-17

Implementation commit `2fc3a7e8efff9636735dcdab0055957a7fdf911f` passed public Lean Action CI run
`29506928654`, build job `87649987984`, in `1m51s`. The independent build verifies both exact
finite-spectrum clauses, registered witnesses, and the standard-only axiom audit. This remains
`KNOWN_THEOREM_FORMALIZED` with `hard_gap_delta=0`: no curve point-count bound or number-field
finite-spectrum/tail bridge has been added. Immutable evidence backfill and its own public CI
remain before campaign closure.

## Public Closure Update: H10 Finite Spectral Rigidity

Date: 2026-07-17

Evidence commit `54388fae4aea20dc768dd6eeaaee8abcb75316fa` passed public Lean Action CI run
`29507245904`, build job `87651088794`, in `2m19s`. Together with preregistration run
`29505635350` and implementation commit `2fc3a7e8efff9636735dcdab0055957a7fdf911f`, run
`29506928654`, campaign `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

The reusable gain is the exact no-cancellation theorem for a finite complex trace spectrum and its
reciprocal-pairing circle corollary. No curve point-count theorem or number-field finite-spectrum
and uniform-tail bridge was proved: `hard_gap_delta=0`, while `route_infrastructure_delta=1`.
H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent Goal returns to fresh independent route
selection; no successor campaign is selected here.

## Selection Update: H6 Reverse-Heat Li Transfer Falsification

Date: 2026-07-17

Fresh selection compares direct W2 global cancellation, M2 target coupling, H6-Q, generic H6
backward propagation, H1/H2 count bridges, and another criterion formalization. Existing W2 and
M2 obstruction records leave no concrete new identity or approximant to test in this loop; H6-Q
requires a global certified zero computation; the count bridges and another equivalence have
lower immediate value.

Audit `AUDIT-20260717-H6-REVERSE-HEAT-LI-01` therefore selects an exact finite countermodel test.
The polynomial `F_t(s)=(s-1/2)^2-1/16+t/2` should satisfy the forward heat PDE, reflection
symmetry, entire-ness, and nonvanishing at `s=1` for every real `t>=0`. Every zero at time one
should lie on the critical line, but time zero has the explicit off-line zero `3/4`; the exact
generalized second Li values should be `448/121` and `-64/9`. Success eliminates only the generic
backward-transfer mechanism and creates an H6 obstruction node with `hard_gap_delta=0`.

## Local Completion Update: H6 Reverse-Heat Li Transfer Falsification

Date: 2026-07-17

The exact countermodel compiles in `H6ReverseHeatLiAudit.lean`. Lean proves both-variable
entire-ness, reflection, the forward heat PDE, and nonvanishing at `s=1` for all real `t>=0`. A
real/imaginary-part argument proves every time-one zero has real part `1/2`, while `3/4` is an
explicit time-zero off-line zero. Under the project's `logDeriv` convention, the generalized
second Li value is exactly `-64/9` at time zero and `448/121` at time one.

The module is diagnostic-free. The exact aggregate TargetCheck, four standard-only axiom prints,
empty forbidden scans, and the 8,686-job full build pass locally. Classification is
`BRANCH_FALSIFIED`; `OBS-H6-REVERSE-HEAT-LI-01` records that generic heat, symmetry,
base-point nonvanishing, and later real-rootedness cannot transfer Li positivity backward.
`hard_gap_delta=0`: actual theta-kernel zero dynamics, H6-E/G8, W2/G7, M2/G3, and RH remain open.
Preregistration commit `215ebcf661a421350d30920ec5aee43518d89559` passed public CI run
`29508598381`, job `87655833650`, in `1m30s`; implementation publication remains pending.

## Public Implementation Update: H6 Reverse-Heat Li Transfer Falsification

Date: 2026-07-17

Implementation commit `819f3de472c43220895772788911a25e114cc7bd` passed public Lean Action CI run
`29509859982`, build job `87660158241`, in `2m38s`. The independent build verifies every fixed
countermodel clause, the exact aggregate witness, and the standard-only axiom audit.

Classification remains `BRANCH_FALSIFIED` with `hard_gap_delta=0`. This eliminates only the
generic inference from heat, reflection, base-point nonvanishing, and later critical-line zeros to
earlier Li positivity. The actual theta-kernel family, fixed-time H6-X, H6-E/G8, W2/G7, M2/G3,
and RH remain open. Immutable evidence backfill and its own public CI remain before campaign
closure.

## Public Closure Update: H6 Reverse-Heat Li Transfer Falsification

Date: 2026-07-17

Evidence commit `b9ebb0d36f4c9d957b26ba089c374172f502907e` passed public Lean Action CI run
`29510451484`, build job `87662213942`, in `2m14s`. Together with preregistration run
`29508598381` and implementation commit `819f3de472c43220895772788911a25e114cc7bd`, run
`29509859982`, campaign `AUDIT-20260717-H6-REVERSE-HEAT-LI-01` is publicly closed as
`BRANCH_FALSIFIED`.

The durable result is `OBS-H6-REVERSE-HEAT-LI-01`: generic heat, reflection, base-point
nonvanishing, and later critical-line zeros cannot by themselves transfer Li positivity backward.
No statement about the actual theta-kernel zeros was falsified or proved. `hard_gap_delta=0`;
H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent Goal returns to fresh value-ranked route
selection; no successor campaign is selected here.

## Selection Update: H6 Zero-Coordinate Framework

Date: 2026-07-17

Fresh selection compares H1/H2 finite-count partitions, direct M2/G3 and W2/G7 re-entry, H6-Q,
H6-X, and H6-H2. The count partitions do not shorten a hard gap; the previous M2 projection and
W2 termwise-prime mechanisms have compiled obstruction records; H6-Q requires a global certified
zero computation; and H6-X cannot be source-faithful before the exact zero coordinate is fixed.

Campaign `CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01` therefore selects the complete
time-zero coordinate layer: `H_0(z)=0` iff `(1+i*z)/2` is a nontrivial zeta zero, the exact inverse
`z=-i*(2*s-1)`, the strict strip `-1<Im(z)<1`, and the equivalence between RH and all `H_0` zeros
being real. This is known-theorem H6-H2 infrastructure with expected `hard_gap_delta=0` and
`route_infrastructure_delta=1`; forward preservation, threshold existence/closedness, H6-E/G8,
and RH remain open. Public preregistration CI is required before Lean proof edits.

Preregistration commit `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e` passed public Lean Action CI run
`29512089828`, build job `87667820977`, in `2m17s`. The four fixed clauses are public before
proof-source edits; implementation may now begin without changing the endpoint.

## Local Completion Update: H6 Zero-Coordinate Framework

Date: 2026-07-17

The exact framework compiles in `DeBruijnNewmanZeros.lean`. Lean verifies the source coordinate
and inverse, both directions between `H_0` zeros and nontrivial zeta zeros, the strict strip
`-1<Im(z)<1`, the boundary exclusions at `i` and `-i`, and the exact equivalence
`RiemannHypothesis <-> deBruijnNewmanAllZerosReal 0`.

The standalone module is diagnostic-free. The aggregate TargetCheck, both boundary witnesses,
five standard-only axiom prints, empty forbidden scan, `git diff --check`, and the 8,687-job full
build pass locally. Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Forward preservation, threshold existence/closedness, H6-E/G8,
W2/G7, M2/G3, and RH remain open; implementation publication and public CI are pending.

## Public Implementation Update: H6 Zero-Coordinate Framework

Date: 2026-07-17

Implementation commit `0283db6a11ef452a7241e17c535744677272a7d1` passed public Lean Action CI run
`29513380203`, build job `87672181193`, in `1m59s`. The independent build verifies the exact
coordinate and inverse, both zero correspondences, strict strip and boundary witnesses, the
RH/all-real-zero equivalence, aggregate TargetCheck, and standard-only axiom audit.

Classification remains `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Forward preservation, threshold existence/closedness, H6-E/G8,
W2/G7, M2/G3, and RH remain open. Immutable evidence backfill and its own public CI remain before
campaign closure.

## Public Closure Update: H6 Zero-Coordinate Framework

Date: 2026-07-17

Evidence commit `0848fcaf5050d6cc842d53a4154172d7511619f6` passed public Lean Action CI run
`29513928275` on attempt 2, build job `87674259193`, in `2m5s`. Attempt 1 failed during Elan
download with an SSL connection reset before project build; the same commit then completed the
full Lean Action without source changes.

Together with preregistration run `29512089828` and implementation commit
`0283db6a11ef452a7241e17c535744677272a7d1`, run `29513380203`, campaign
`CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`. The reusable gain is the exact H6 time-zero zero coordinate, strict
strip, and RH/all-real-zero equivalence. `hard_gap_delta=0`; forward preservation, threshold
existence/closedness, H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent Goal returns to
fresh value-ranked route selection; no successor campaign is selected here.

## Public Closure Update: H6 Threshold Closedness

Date: 2026-07-17

Evidence-backfill commit `c5b9405befd3029f04b1301f55a8a9c45074dce4` passed public Lean Action CI
run `29518417233`, build job `87689151089`, in `1m36s`.

Together with preregistration commit `02758ff243c3f8cd434eb3c007a2a5f6b094fea7`, run
`29515723482`, and implementation commit `6322bbd59d25f919befc91cd5a057251bcf94cb4`, run
`29518062294`, campaign `CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01` is publicly closed as
`KNOWN_THEOREM_FORMALIZED`. The reusable gain is exact closedness of the source-normalized
all-real-zero time set, with arbitrary zero multiplicity, through joint continuity,
nonvanishing, isolated zeros, and Jensen persistence. `hard_gap_delta=0` and
`route_infrastructure_delta=1`; forward preservation, threshold nonemptiness/upper-ray structure,
H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent Goal returns to fresh value-ranked
route selection after closure CI; no successor campaign is selected here.

## Local Completion Update: H6 de Bruijn Upper-Half Bound

Date: 2026-07-17

Campaign `CAMPAIGN-20260717-H6-UPPER-HALF-01` reaches both fixed endpoints locally.
`DeBruijnNewmanUpperHalf.lean` proves every zero of `H_t` satisfies
`Im(z)^2<=1-2*t` for `0<=t<=1/2`, and proves unconditionally that every zero of `H_(1/2)` is real.

The mechanism preserves analytic zero multiplicity under conjugation, pairs genus-one factors on
the multiplicity-bearing divisor, contracts squared strip width by `a^2` under one vertical
average, iterates to the exact finite width, and transfers zeros through compact-uniform
convergence using an isolating ball and Jensen's logarithmic circle mean. The exact module,
Targets, TargetChecks, eight standard-only axiom prints, empty forbidden/resource scans,
`git diff --check`, and the 8,690-job full build pass.

Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. This closes threshold nonemptiness and supplies the classical
bound `Lambda<=1/2`; it does not prove H6-E/G8 (`Lambda<=0`) or RH. Public implementation CI and
evidence-backfill CI remain before campaign closure.

## Public Implementation Update: H6 de Bruijn Upper-Half Bound

Date: 2026-07-17

Implementation commit `8669c2db7577eaa718684e9e9ec052062b5488fa` passed public Lean Action CI
run `29531232787`, build job `87731748374`, in `2m6s`. The independent runner rebuilt the exact
quadratic strip contraction, unconditional half-time witness, registered intermediate witnesses,
Targets, TargetChecks, and standard-only axiom audit.

Classification remains `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. H6-E/G8, W2/G7, M2/G3, and RH remain open. Immutable evidence
backfill and its own public CI remain before campaign closure.

## Public Closure Update: H6 de Bruijn Upper-Half Bound

Date: 2026-07-17

Evidence-backfill commit `ac128f4db100fdac0d47c670e0dcbd832ddb6005` passed public Lean Action CI
run `29531495280`, build job `87732612433`, in `1m47s`. Together with preregistration run
`29528426983` and implementation run `29531232787`, campaign
`CAMPAIGN-20260717-H6-UPPER-HALF-01` is publicly closed as `KNOWN_THEOREM_FORMALIZED`.

The reusable gain is exact threshold nonemptiness for the source-normalized heat family and the
classical upper bound `Lambda<=1/2`, proved through multiplicity-aware conjugate factor pairing,
finite strip contraction, and Jensen limit persistence. `hard_gap_delta=0` and
`route_infrastructure_delta=1`; H6-E/G8, W2/G7, M2/G3, and RH remain open. The persistent RH Goal
returns to fresh value-ranked route selection; no successor campaign is selected here.

## Local First-Spine Update: H6 Zero Dynamics

Date: 2026-07-17

Campaign `PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01` remains active against the exact time-zero
all-real-zero endpoint. Its first fixed formalization loop succeeds locally.

`DeBruijnNewmanDynamics.lean` proves genuine summability of the divisor-regularized genus-one
force, the exact simple-zero identity `H_t''/(2*H_t')=force`, a strict joint real Frechet derivative
of the source heat family, and `x'(t)=2*force` along every differentiable simple-zero path. The
proof handles analytic multiplicity and the complete removed divisor fiber; it does not use a
principal-value ordering.

The exact module, Targets, five TargetChecks, five standard-only axiom prints, empty forbidden
scans, `git diff --check`, and the full 8,691-job build pass. Classification is a locally completed
known first spine with `hard_gap_delta=0` and `route_infrastructure_delta=1`. H6-E/G8, collision
exclusion, W2/G7, M2/G3, and RH remain open. Next within the same campaign is construction and
ordering of local real simple-zero trajectories; public implementation CI is pending.

## Public Implementation Update: H6 Zero Dynamics First Spine

Date: 2026-07-17

Implementation commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed public Lean Action CI
run `29534356022`, build job `87741989620`, in `2m36s`. The independent runner rebuilt the
summable divisor force, exact simple-zero derivative ratio, joint Frechet chain rule, path
velocity, Targets, TargetChecks, and standard-only axiom audit.

The first spine is now public with `hard_gap_delta=0` and `route_infrastructure_delta=1`. Campaign
`PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01` remains active at local real trajectory construction;
collision exclusion, H6-E/G8, and RH remain open.

## Public Loop-2 Update: H6 Zero Trajectories And Pair Remainder

Date: 2026-07-17

The active H6-E campaign now compiles locally unique differentiable real zero trajectories from
every simple real zero and locally ordered trajectories from every distinct simple pair. This uses
the product-domain real implicit-function theorem, joint strict Frechet differentiation, and
conjugation uniqueness.

The same module extracts the mutual interaction from the infinite force. After deleting both
complete simple-zero divisor fibers, the residual pair force is absolutely summable and

`force(t,s)-force(t,r)=2/(s-r)+pairRemainder(t,r,s)`.

Consequently `(gap^2)'=8+4*gap*Re(pairRemainder)` for real anchored local paths. Exact Targets,
eleven campaign TargetChecks, twelve standard-only campaign axiom prints, empty forbidden scans,
`git diff --check`, and the full 8,691-job build pass. This remains route infrastructure with
`hard_gap_delta=0` and campaign-level `route_infrastructure_delta=1`.

Implementation commit `03ce2ac2ee68b7d9a6d48d56aed37ab40836c30d` passed public Lean Action CI
run `29536815968`, build job `87750004173`, in `1m54s`.

The next proof loop must attack global height-aware continuation and a theta-specific integrated
bound on the pair remainder through time zero. Local IFT does not handle the first repeated zero,
and a fixed positive height-uniform gap is not an admissible replacement. The campaign remains
active; H6-E/G8 and RH remain open.

## Local Loop-3 Update: Adjacent Gap Bound Is Generically Sharp

Date: 2026-07-17

The active H6-E campaign proves that, at an all-real time, every zero outside an adjacent pair
contributes nonpositively to the pair remainder. The exact compiled consequence is
`(gap^2)'<=8`, and its interval form is
`gap(a)^2>=gap(b)^2-8*(b-a)`. A separate theorem verifies that a nonadjacent middle zero contributes
positively, so adjacency is not cosmetic.

`H6GapVelocityAudit.lean` then supplies a quadratic family satisfying the same backward heat
equation. Two terminal simple real zeros of gap `epsilon` collide into a double zero after
`epsilon^2/8`, and the bundled Lean theorem produces such a collision within every positive
proposed uniform interval. This records `OBS-H6-ADJACENT-GAP-EIGHT-01`: generic adjacent-pair
geometry is insufficient for height-uniform continuation.

The exact modules, Targets, seven new TargetChecks, seven selected standard-only axiom prints,
empty forbidden scans, `git diff --check`, and the full 8,692-job build pass locally.
`hard_gap_delta=0`; H6-E/G8 and RH remain open. Public CI is pending, after which the persistent
Goal returns to value-ranked route selection for a theta-specific mechanism or a different route.
