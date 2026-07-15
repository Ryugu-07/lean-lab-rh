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
campaign is locally complete as `BRIDGE_REDUCED`; public CI and evidence backfill remain.

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
