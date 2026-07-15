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
- **Decision:** **DEFER**. This is a serious future route, but its first missing infrastructure edge
  is larger than the selected exact-Gram campaign.

## Selected Campaign

`CAMPAIGN-20260715-GRAM-01` selects R1. It may produce a relevant unconditional Gram theorem or
eliminate a coercivity mechanism, but it leaves `M2/G3` parked unless an independent novelty audit
confirms that a fixed unconditional bridge edge has actually been reduced.
