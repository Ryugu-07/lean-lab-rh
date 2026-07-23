# Ranked Historical Door Atlas for RH

Date: 2026-07-22

Campaign: `LITERATURE-20260722-HISTORICAL-DOOR-SURVEY-01`

Status: `ATLAS_COMPLETE / D9_SUZUKI_AUDIT_CLOSED / H10_INFINITE_TRACE_AUDIT_LOCAL_COMPLETE`

## Claim boundary

This atlas is an omission-seeking audit, not a claim to have exhausted every paper about the
Riemann hypothesis. Its source boundary is the H0-H14 census, the project's compiled route
history, the canonical sources named below, and primary-source developments found through
2026-07-22. A route earns a high rank only when the audit can name both its last proved node and
its next missing mathematical object.

No item in this document proves RH or changes the unconditional RH frontier. `OPENING` means a
source-exact probe could materially distinguish a viable mechanism from another restatement. It
does not mean that the mechanism is correct, new, or easier than RH.

Evidence labels used below:

- `PROVED`: a cited theorem or a no-sorry project theorem.
- `CONDITIONAL`: a theorem whose displayed assumptions are not known unconditionally.
- `NUMERICAL`: reproducible navigation evidence, never a premise.
- `OBSTRUCTION`: a theorem or checked counterexample that defeats a stated mechanism.
- `OPEN`: no proof or counterexample was found within the source boundary.
- `SOURCE-SUGGESTED`: an author explicitly proposes the step, but it remains open.

## Coverage reconciliation

| census ids | door | pre-survey project coverage | survey result |
| --- | --- | --- | --- |
| H0/H3/H4/H5 | xi, closure, Li, explicit-formula positivity | `DEEP_FORMALIZATION` | Complete combined criteria/positivity card; exact unconditional sign/closure edge retained. |
| H6 | de Bruijn-Newman heat flow | old census says `SOURCE_ALIGNED`; current project is deeper | Reclassified `DEEP_FORMALIZATION`; direct `Lambda <= 0` remains open and the numerical successor is parked. |
| H1 | critical-line proportions and mollifiers | `SOURCE_ALIGNED` | Card updated through the 2025 short-mollifier derivative optimization. |
| H2 | density, moments, mean values, subconvexity | `SOURCE_ALIGNED` | Card retains the Guth-Maynard density frontier and the exceptional-zero barrier. |
| H11 | zero statistics and random matrices | `MENTION_ONLY` | Complete card; unconditional pair-correlation work is separated from real-part control. |
| H7 | Hilbert-Polya, trace, NCG, prolate operators | `PARTIAL` | Complete card through the 2025-2026 finite-prime Weil ground-state program. |
| H10 | function fields and cohomological weights | `SOURCE_ALIGNED` | Complete transfer-gap card; finite spectral rigidity is already compiled. |
| H8 | Laguerre-Polya and Jensen polynomials | `MENTION_ONLY` | Split from de Branges and completed with the eventual-hyperbolicity limitation. |
| H7/H8 | de Branges and canonical systems | mixed mention | Separate card; original positivity condition is not valid for the required zeta input. |
| H9/H12 | arithmetic criteria, Speiser, value distribution | `UNMAPPED` | Complete card with divisor-sum, character-sum, and derivative-zero subdoors separated. |
| H13 | generalized/automorphic L-functions and Iwasawa analogies | `UNMAPPED` | Complete card; analogy and family statistics are not promoted to a zeta-zero theorem. |
| H14 | certified finite computation | `UNMAPPED` | Added as a distinct operational door because it can close analytic certificates when paired with a global tail theorem. |
| obstruction map | countermodels and failed mechanisms | route-local records | Consolidated control card spanning Mertens, Davenport-Heilbronn, Beurling systems, and project countermodels. |

The AI-generated five-family summary was therefore directionally useful but too coarse. It
merged four logically different kinds of criteria, omitted de Branges, arithmetic/Speiser,
generalized L-functions, certified computation, and countermodels, and understated the project's
actual H6 and H10 depth.

## Ranking rule

The order below is qualitative. It prioritizes:

1. an exact RH-relevant missing object rather than a new equivalent slogan;
2. evidence that the historical obstruction is technical or untested, not already false;
3. a proved mechanism on both sides of the missing edge;
4. a plausible cross-route interface and mature machinery not yet applied to that exact edge;
5. useful falsification information if the probe fails.

Formalization fit is recorded but is not the objective. A high machine-fit score cannot rescue a
mathematically weak route.

## Ranked comparison

| rank | door | exact missing object | obstacle status | omission evidence | recommendation |
| --- | --- | --- | --- | --- | --- |
| 1 | D6 spectral/trace plus finite-prime Weil ground states | Prove simple even ground states and compact-uniform convergence of their Fourier-Mellin transforms to the Riemann xi transform as the prime cutoff grows. | `OPEN`; explicitly isolated in 2025-2026 sources. | Strong: a new theorem supplies on-line zeros for every admissible approximant, while convergence is recent and sharply stated. | `PROOF-ATTEMPT` after a definition-alignment campaign. |
| 2 | D3 critical-line proportions/mollifiers | Prove arbitrary-length mollified moment bounds strong enough for the Bettin--Gonek individual-zero exclusion, or separately repair the sparse-exception gap of proportion-only methods. | Mixed: long mean values are open; sparse-zero insufficiency applies to density-only conclusions, while the full `theta=infinity` conjecture has a published direct implication to RH. | Stronger than first recorded: Bettin--Gonek turn each off-line zero into a power-growth obstruction, and 2025 work identifies derivative-combination optimization as relatively underused. | `LITERATURE -> PROOF-ATTEMPT`; runner-up. |
| 3 | D10 arithmetic/Speiser/character sums | Prove a uniform arithmetic inequality strong enough for the RH implication, or a derivative-zero exclusion theorem on the left half-strip. | `OPEN`, but most classical criteria merely restate RH. | Moderate for Conrey's 2024 character-sum reduction; low for Robin/Lagarias alone. | `FALSIFICATION` of the exact character-sum strengthening before proof work. |
| 4 | D1 closure/Li/Weil positivity | Produce unconditional global positivity or target closure, with prime and archimedean terms controlled together. | `OPEN`; local same-sign prime decomposition is formally obstructed. | Moderate only through the D6 global operator interface. | Merge consumers into D6; do not add another equivalent criterion. |
| 5 | D4 density/moments/subconvexity | Convert vertically sensitive zero detection or large-value control into exclusion of even one exceptional off-line orbit. | `OPEN`; density bounds allow sparse exceptions, and Maynard--Pratt identify bow configurations as the obstruction to removing finite-real-part rigidity. | Moderate: the half-isolated detector was omitted from the first atlas and gives a precise geometric stress test, though not a known exceptional-zero killer. | `FALSIFICATION` of symmetry-only half-isolation, then retain the actual bow-exclusion edge. |
| 6 | D7 function-field/cohomology | Construct a number-field trace/cohomology object with positivity/weights and a uniform infinite-spectrum tail. | `OPEN`; characteristic-p and finite-spectrum inputs do not transfer. | Moderate structural value, low evidence of a missed direct transfer. | `LITERATURE` only where it feeds D6 or D1. |
| 7 | D2 heat flow/zero dynamics | Prove `Lambda <= 0`, for example through an actual-theta all-index invariant or collision-compatible continuation. | `OPEN`; several generic mechanisms are formally obstructed. | Low after deep project exploration, though exact direct endpoint remains legitimate. | Keep open; H6 numerical upper-bound successor remains parked. |
| 8 | D9 de Branges/canonical systems | Prove a regular, source-valid limit from finite self-adjoint characteristic functions to an xi-bearing target without introducing nonremovable reciprocal-log-derivative poles. | Original positivity fails; Suzuki 2026 proves finite real-zero functions but leaves the global limit conjectural and its displayed normalization regularity unstated. | Moderate: the finite operator is explicit, but the proposed target/topology now has a sharp audit point. | `FALSIFICATION` of the normalization and target regularity before any limit attack. |
| 9 | D8 Laguerre-Polya/Jensen | Prove all degrees and all shifts hyperbolic, including the finite exceptional region. | `OPEN`, but eventual fixed-degree hyperbolicity is asymptotically universal and does not control the exceptions. | Low; Duran 2024 adds Brenke equivalences without a uniform-index bridge. | Generic eventual-to-global promotion falsified; retain actual-xi all-index edge. |
| 10 | D5 zero statistics/random matrices | Upgrade the 2026 horizontal-multiplicity density-one theorem to exclusion of every sparse off-line orbit. | PCC now conditionally gives density one on the line, but its normalized error permits finite or density-zero exceptions. | Moderate post-survey omission evidence: the source explicitly corrects the older no-horizontal-information claim. | Finite hinge and sparse-exception model formalized; H11-D/H11-E remain open. |
| 11 | D11 generalized/automorphic/Iwasawa | Find a theorem that transfers a proved family or p-adic mechanism to the individual archimedean zeta zero set. | `OPEN`; no direct p-adic RH analogue, and family laws do not decide one member. | Low. | `MONITOR`; use for mechanism stress tests. |
| 12 | D12 certified computation | Pair finite verification with a proved uniform global tail that excludes all higher off-line zeros. | Tail is the whole unresolved global edge. | Low as a standalone route; high as a certificate component. | `SUPPORTING`; no finite-to-global promotion. |
| control | D13 countermodels/failed mechanisms | Not a proof endpoint. | Several mechanisms are decisively false. | High negative value: prevents repeated false routes. | Maintain as mandatory regression suite. |

## D1. Equivalent criteria and global positivity

### Endpoint and last proved node

Nyman-Beurling-Baez-Duarte target closure, all-index Li positivity, and Weil explicit-formula
positivity are each equivalent to RH after exact definitions and admissibility conditions are
fixed. The project compiles the Baez-Duarte closure equivalence, the full Li iff, finite and full
Burnol lower bounds, Gaussian and compact Weil infrastructure, and several reverse criteria.
These are `PROVED` equivalences or known-theorem formalizations, not unconditional RH progress.

Primary anchors are Baez-Duarte's [positive-natural closure criterion](https://arxiv.org/abs/math/0202141),
Bombieri-Lagarias' [transformed-zero form of Li's criterion](https://math.lsa.umich.edu/~lagarias/doc/bombieri.ps),
and Burnol's [zero-sensitive approximation lower bound](https://arxiv.org/abs/math/0103058).

### Exact missing object

- H3: an unconditional sequence of positive-natural Baez-Duarte approximants converging to the
  target in the exact project `L2` space.
- H4: an unconditional all-index sign mechanism. Computing or proving finitely many Li signs is
  insufficient.
- H5: positivity of the complete Weil quadratic form on the full admissible class, with the pole,
  archimedean, and prime terms assembled globally.

### Obstacle validity

The obstacle is not a theorem that these criteria are useless. It is that each missing statement
is already RH-strength. Burnol's lower bound constrains the best possible Nyman-Beurling rate but
does not forbid convergence. Two more specific implementation obstacles are current and checked:

- projection-norm and ladder-frequency claims used in two recent H3 proof attempts were formally
  falsified;
- the actual two-point Gaussian prime kernel is indefinite, so Weil positivity cannot be proved
  by assigning the same semidefinite sign to every prime term separately.

Thus a viable Weil proof must use genuinely global cancellation or an operator identity. This is
exactly the interface supplied, but not completed, by D6.

### Unused machinery and omission audit

Finite-dimensional convex duality, Toeplitz/prolate spectral theory, and certified extremal
eigenvector convergence have not been exhausted against the exact complete Weil edge. This is a
real opening only when formulated through D6. Another finite family, fixed Gaussian width, or new
equivalent coefficient sequence is not an opening.

Formalization fit: `5/5`. Machine-task fit: `4/5` for finite extremal certificates, `2/5` for the
global convergence theorem.

### Discriminating probes

1. Prove the exact equivalence between the project's compact Weil form and the finite-prime
   quadratic form used by Connes, including both moment constraints.
2. Search for a finite-cutoff spectral-gap lower bound stable under Galerkin refinement; falsify
   uniformity before attempting the infinite limit.
3. Derive a project theorem showing exactly which ground-state convergence topology implies W2,
   with no positivity assumption hidden in the convergence premise.

## D2. de Bruijn-Newman heat flow and zero dynamics

### Endpoint and last proved node

In the audited normalization RH is equivalent to `Lambda <= 0`; Rodgers-Tao prove
`Lambda >= 0`, so the endpoint is `Lambda = 0`. The unconditional published interval is
`0 <= Lambda <= 0.2`, using Rodgers-Tao, the Polymath heat-flow estimates, and
Platt-Trudgian's finite verification.

The project now goes well beyond the old `SOURCE_ALIGNED` label. Lean compiles the source theta
kernel, time-zero xi bridge, entire backward heat equation, zero-coordinate iff, closedness of the
all-real-zero time set, de Bruijn forward preservation and strip contraction, zero trajectories,
the first three heat-Li signs, theta-kernel TP2, actual-kernel PF5 failure, and the Boyd-Nemes
scaled-Gamma dispersion identity. These are substantial `PROVED` route results, but no theorem
places every zero of `H_0` on the real axis.

Sources: [Rodgers-Tao](https://arxiv.org/abs/1801.05914),
[Polymath](https://arxiv.org/abs/1904.12438), and
[Platt-Trudgian](https://arxiv.org/abs/2004.09765).

### Exact missing object

One must prove `deBruijnNewmanAllZerosReal 0`. The sharp project-local candidates are an
actual-theta all-index heat-Li invariant or a height-uniform continuation through the first
possible repeated-zero collision. Improving a positive upper bound for `Lambda` is not logically
enough.

### Obstacle validity

The following generic shortcuts are checked obstructions:

- backward propagation of real-rootedness has the wrong direction;
- the generic adjacent-gap differential inequality is sharp on a quadratic countermodel;
- positive even-transform and Hankel moment structure does not force the third and higher Li
  signs in generic models;
- the physical xi kernel is not Polya-frequency order five, so PF-infinity cannot be the missing
  mechanism;
- heat-Li monotonicity survived finite numerical screening but its exact derivative becomes an
  unsigned cross-index convolution.

These obstructions do not refute an actual-theta-specific invariant. They do make a claimed
omission less likely after the project's deep exploration.

Formalization fit: `5/5`. Machine-task fit: `4/5` for finite and local dynamics, `2/5` for the
all-height invariant.

### Discriminating probes

1. Search for an integral or covariance representation of the full heat-Li derivative whose sign
   uses the exact theta kernel rather than generic moment positivity.
2. Build a finite multiplicity-aware collision model and test every proposed continuation
   invariant before admitting it as a conjecture.
3. Keep the Table 1/effective-`R2` numerical successor parked unless new evidence links it to
   `Lambda = 0` rather than another positive constant.

## D3. Critical-line proportions and mollifiers

### Endpoint and last proved node

Hardy proved infinitely many critical-line zeros; Selberg proved a positive proportion; Levinson,
Conrey, and later mollifier work increased the proportion. The audited zeta frontier remains the
published result that more than `5/12` of zeros are on the line in
[Pratt-Robles-Zaharescu-Zeindler](https://arxiv.org/abs/1802.10521).

A distinct 2025 development,
[Short mollifiers of the Riemann zeta-function](https://arxiv.org/abs/2508.11108), optimizes
linear combinations of zeta derivatives by calculus of variations and obtains positive
proportions even with arbitrarily short mollifiers. The authors explicitly identify this
linear-combination optimization as relatively underused. It does not claim a new `>5/12` zeta
record or proportion one.

### Exact missing object

Two endpoints must be distinguished. A Levinson-style argument that outputs only asymptotic
critical-line proportion one still needs a second theorem excluding every finite or density-zero
off-line orbit. Farmer's stronger `theta=infinity` moment conjecture has a different endpoint:
Bettin--Gonek prove that a uniform bound through length `T^theta` excludes every zero in
`Re(s) > 1/2 + 1/(2*theta)`, so arbitrary `theta` implies RH directly. Its missing object is the
arbitrary-length mollified moment bound itself, together with formal reconstruction of the
Mellin/residue transfer to an individual zero.

### Obstacle validity

The long-mollifier barrier is a missing analytic estimate, not an impossibility theorem. The
sparse-exception barrier remains fully current for asymptotic density-one conclusions, but it must
not be attached to the full Farmer--Bettin--Gonek mechanism: that mechanism localizes each
individual off-line zero through a power-growth contradiction. The project's finite xi-divisor
model still rejects density-one-to-Li positivity; it does not obstruct `theta=infinity`.

### Unused machinery and omission audit

The 2025 derivative-combination optimization is concrete evidence that a mature route still had
an underexplored degree of freedom. This makes D3 the runner-up. The evidence is bounded: the new
optimization reuses the same arithmetic inputs and does not yet supply either proportion one or
an exceptional-zero eliminator. A promising cross-route repair would combine a near-total
mollifier result with D10 Speiser control or a D1 localizer that turns one off-line orbit into a
uniform detectable defect.

Formalization fit: `2/5`. Machine-task fit: `3/5` for variational optimization and finite symbolic
identities, `1/5` for the required long mean values.

### Discriminating probes

1. Reconstruct the 2025 variational problem exactly and test whether its optimum saturates below
   one under currently proved mean-value inputs.
2. State and falsify candidate inequalities that would convert a density-one critical-line result
   into exclusion of one off-line xi orbit.
3. Reconstruct Bettin--Gonek equations `(2.1)`--`(2.5)`, including the integer-to-real cutoff
   passage and every uniform quantifier, before deciding whether derivative-combination
   optimization can feed the same arbitrary-length moment.

## D4. Zero density, moments, mean values, and subconvexity

### Endpoint and last proved node

This door controls how often zeta is large and how many zeros can lie to the right of a vertical
line. Bourgain's [decoupling paper](https://arxiv.org/abs/1408.5794) gives the audited
critical-line subconvexity exponent, while
[Guth-Maynard](https://arxiv.org/abs/2405.20552) proves the new large-value estimates and the
zero-density exponent `30/13` in the project's H2 card.

These are unconditional advances in analytic number theory. They are not zero-location theorems
for every nontrivial zero.

A distinct vertically sensitive branch is Maynard--Pratt's
[half-isolated-zero method](https://arxiv.org/abs/2206.11729). It gives short detectors and the
density hypothesis for half-isolated zeros, and improves density estimates under the hypothesis
that all real parts lie on finitely many fixed vertical lines. Its stated unconditional obstacle
is a slowly bending bow of zeros, not merely a suboptimal numerical exponent.

### Exact missing object

The route lacks a localizer that turns large-value or density information into the exclusion of
a single exceptional off-line orbit. For the half-isolated branch, it also lacks a theorem
excluding bow-like actual-zeta configurations or forcing an off-line half-isolated extremum
without the finite-vertical-line hypothesis. The density hypothesis itself remains compatible
with finitely many exceptions and therefore is weaker than RH.

### Obstacle validity

The exceptional-zero objection is current and theorem-level as a logical model statement. Better
density exponents can improve prime-distribution applications without closing it. Maynard--Pratt's
finite-real-part rigidity is a genuine additional premise: functional-equation reflection does
not visibly discretize nearby real parts. Lindelof-type bounds on the critical line are also RH
consequences but do not by themselves state that zeta is nonzero off the line.

### Unused machinery and omission audit

The first atlas omitted the half-isolated branch. Campaign
`FALSIFICATION-20260723-H2-HALF-ISOLATED-BOW-01` now tests its exact geometric hinge: discrete
vertical-line gaps should force a rightmost-bottom half-isolated point, while a finite
reflection-symmetric bow may show why zeta symmetry alone does not. The larger omission candidate
remains cross-route: amplify one off-line bow faster than the density error. No source-backed
functional with the required uniform tail was found.

Formalization fit: `1/5`. Machine-task fit: `2/5` for exponent bookkeeping and finite Dirichlet
polynomials, `1/5` for the core estimates.

### Discriminating probes

1. Formalize the finite divisor symmetry/count layer so any proposed density-to-RH theorem must
   expose where it excludes a single orbit.
2. Test the exact half-isolation disjunction on a finite critical-reflection-symmetric bow and
   identify the precise vertical-gap premise that fails.
3. Monitor improvements only when they change the exceptional-zero logic, not merely an exponent.

## D5. Zero statistics and random matrices

### Endpoint and last proved node

Montgomery's pair-correlation theorem and conjecture concern normalized ordinate differences;
the headline form of the original analysis assumes RH. Random-matrix models predict GUE spacing,
moments, and symmetry types and have extraordinary numerical and function-field support.

The 2024 published
[unconditional Montgomery theorem](https://arxiv.org/abs/2306.04799) is especially useful for
scope control: its authors state that the method neither requires nor provides information on
whether the zeros are on the critical line. Its simplicity conclusion still uses a thin-box or
strong density hypothesis.

Post-survey correction, 2026-07-23: the authors later explicitly withdrew that scope statement.
[Goldston-Lee-Schettler-Suriajaya v4](https://arxiv.org/abs/2503.15449v4) prove that PCC, without
assuming RH, implies asymptotically 100 percent of the zeros are simple and on the critical line.
The mechanism counts same-ordinate reflected pairs through horizontal multiplicity. This is a
conditional horizontal-location theorem, not an RH theorem.

### Exact missing object

A theorem must upgrade the horizontal-multiplicity excess from `o(N(T))` to zero, or otherwise
exclude every exceptional off-line orbit. The revised PCC mechanism detects off-line reflected
pairs at density scale, but not the last finite or sparse exceptions.

### Obstacle validity

The older statement that the method gives no line-location information is superseded. The current
obstacle is narrower and still exact: density one does not imply universal line location. A finite
or sufficiently sparse reflected orbit has asymptotically negligible horizontal excess.

### Unused machinery and omission audit

The horizontal-multiplicity diagonal is a genuine overlooked mechanism in the first atlas. A
viable upgrade now needs a last-exception localizer, an absolute-error form of the statistic, or an
arithmetic theorem amplifying one off-line orbit to nonzero horizontal density. The H11 campaign
tests the exact finite count logic and a persistent-exception countermodel before any such
amplification conjecture is admitted.

Formalization fit: `2/5`. Machine-task fit: `4/5` for finite ensembles and countermodels, `1/5`
for the analytic limit.

### Discriminating probes

1. Construct finite zero multisets with GUE-like ordinate spacing plus one off-line symmetric
   orbit and test every proposed statistical implication.
2. Require any new statistic to change under that insertion by a nonvanishing amount.
3. Use the route to falsify all-index moment conjectures, not as a proof premise.

## D6. Hilbert-Polya, trace formulae, NCG, and finite-prime Weil ground states

### Endpoint and last proved node

A self-adjoint operator whose spectrum corresponds exactly, with multiplicity and no spurious
points, to the imaginary parts of all nontrivial zeros would prove RH. Connes' 1998
[trace-formula program](https://arxiv.org/abs/math/9811068) gives a spectral realization as an
absorption spectrum and interprets the explicit formula on the adele class space. Connes-Consani
later isolate an operator-theoretic source for
[archimedean Weil positivity](https://arxiv.org/abs/2006.13771), while the full semilocal
positivity edge remains open.

The route materially changed in 2025-2026:

- Connes and van Suijlekom prove that a lower-bounded distributional quadratic form with a simple
  isolated even ground state has a ground-state Fourier transform whose zeros are all real in
  [Quadratic Forms Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257).
- Connes' 2026 [historical survey and new program](https://arxiv.org/abs/2602.04022) applies this
  to finite-prime restrictions of the Weil quadratic form. The resulting approximating zeros are
  on the critical line under the ground-state hypothesis and numerically approximate zeta zeros.
  The paper does not prove their convergence to zeta zeros.
- Connes-Consani-Moscovici's
  [semilocal prolate operators](https://arxiv.org/abs/2310.18423) supply a proved structural link
  among Sonin spaces, prolate operators, semilocal places, and the low/ultraviolet spectral
  regimes. Matching ultraviolet asymptotics is not exact spectrum equality.

### Exact missing object

For increasing prime cutoff `c`, let `Q_c` be the exact constrained finite-prime Weil form and
`xi_c` its normalized lowest even eigenfunction. Prove:

1. the lowest relevant eigenvalue is simple and isolated with an even eigenfunction for every
   sufficiently large cutoff;
2. after the source normalization, `Fourier(xi_c)` converges uniformly on compact subsets to the
   Riemann xi transform;
3. no normalization, subsequence, or spectral pollution changes the multiplicity-bearing limit.

Hurwitz would then transfer the on-line zero property to the nonzero limit. The second clause is
the decisive RH-strength edge.

### Obstacle validity

This is not the old vague instruction to "find a self-adjoint operator." The 2025 theorem proves
the real-zero mechanism for a broad exact class, and the 2026 paper names the remaining ground-
state approximation problem. The obstacle is still fully operative: numerical agreement, even at
very high precision, does not prove compact-uniform convergence; ultraviolet asymptotics do not
prove exact low spectrum; and simplicity cannot be inferred from a finite discretization.

The project's audit of a separate 2026 Volterra proposal also proves that factorization through a
contractive middle map does not force contraction of the compressed composite. That obstruction
does not apply to the Connes ground-state theorem, whose assumptions and operator are different.

Post-survey H7 audit on 2026-07-22 sharpened the first clause. Four June 2026 S3 Zenodo preprints
by Breno Wilson de Andrade Silva claim pole-free Perron structure, exact parity-sector Loewner
identities, and an equivalence between full even-simplicity and pole localization together with
the odd-sector Herglotz inequality
`<S,(B_odd-lambda_even)^(-1)S><1/2`. The claimed inequality is exponentially tight in the reported
finite data and remains unproved uniformly. The project has now compiled the finite matrix,
parity split, and a strict two-block Rayleigh certificate, but not the arithmetic inequality.
A high-precision navigation probe also rejects universal checkerboard positivity of the inverse,
so that naive Perron shortcut is not a surviving omission candidate.

### Unused machinery and omission audit

This is the strongest omission candidate in the survey because the key theorem and the precise
application are recent, the approximants have a proved real-zero mechanism, and both the Weil and
Fourier sides already overlap project infrastructure. Mature unused tools include variational
convergence of quadratic forms, compact-resolvent spectral convergence, Toeplitz/prolate
eigenvalue bounds, and Lean-checkable finite Galerkin inequalities.

The claim must remain bounded: no source proves the needed convergence, and no audit establishes
novelty beyond the cited 2025-2026 program.

Formalization fit: `3/5`. Machine-task fit: `5/5` for finite matrix structure and exact theorem
interfaces, `2/5` for infinite-dimensional spectral convergence.

### Discriminating probes

1. `M0`-align the finite-prime Weil form with the project's compact explicit formula, including
   support and two vanishing-moment constraints; reject the route if the forms differ materially.
2. Prove or falsify a uniform spectral-gap statement for the exact finite Galerkin matrices as
   both matrix size and prime cutoff grow.
3. Isolate a Mosco/norm-resolvent convergence theorem whose hypotheses reduce the source's
   `xi_c -> xi` claim to explicit kernel and coercivity bounds; do not assume Weil positivity.

## D7. Function fields, Frobenius, cohomology, and weights

### Endpoint and last proved node

For a curve over `F_q`, the zeta numerator has a finite Frobenius spectrum. Weil, Stepanov,
Bombieri, Grothendieck, and Deligne supply successful proofs that its reciprocal roots have norm
`sqrt(q)`. Deligne's [Weil I](https://publications.ias.edu/book/export/html/368) supplies the
cohomological weight theorem in the broader setting.

The project card reconstructs the Bombieri-Stepanov mechanism and Lean proves the last finite
spectral step: uniform power-sum bounds plus reciprocal pairing force every eigenvalue onto the
circle. This is `PROVED` and records exactly where finiteness enters.

### Exact missing object

Number-field RH needs an analogue of finite Frobenius/cohomology whose trace is the prime side of
the explicit formula, whose pairing is positive, and whose infinite spectral tail is uniformly
controlled. No such object is supplied by translating the finite-field notation.

### Obstacle validity

Characteristic-p high powers, finite-dimensional Riemann-Roch spaces, rational point counts over
all finite extensions, and a finite spectrum are genuine proof inputs. For zeta, the zero divisor
is infinite and the archimedean term is unavoidable. The transfer gap is current, not merely a
missing Lean library.

### Unused machinery and omission audit

The useful cross-route question is narrower than "formalize algebraic geometry": can the finite
spectral rigidity theorem consume semilocal traces from D6 after a uniform truncation/tail theorem?
Without that consumer, a large curve-cohomology formalization would reproduce known mathematics
without shortening the number-field gap.

Formalization fit: `2/5` for geometry, `5/5` for finite spectral rigidity. Machine-task fit:
`2/5`.

### Discriminating probes

1. State the weakest infinite-spectrum extension of finite power-sum rigidity and attack it with
   an artificial sparse off-line orbit.
2. Test whether semilocal D6 trace truncations satisfy the extension's uniform-tail hypotheses.
3. Formalize further function-field geometry only after a number-field consumer is named.

### Post-survey H10 infinite-trace audit

The first discriminating probe is now selected as
`FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01`. It tests the literal transfer of a
finite Frobenius power trace to a countably infinite ordinary `Summable` trace while retaining a
nonzero constant reciprocal pairing. Summability of one positive power and its permutation
reindexing should force both factors to zero, contradicting the constant paired product.

This proposed obstruction is generic. It does not apply to a regularized or distributional trace,
does not represent actual zeta zeros, and does not rule out Hilbert-Polya or Connes-type spectral
constructions. Its purpose is to prove that ordinary unregularized power sums cannot be silently
carried across the finite-to-infinite boundary.

The local Lean implementation now proves the exact contradiction for every positive power and
supplies a one-point finite reciprocal witness. The literal ordinary-trace transfer is therefore
closed locally; the regularized number-field trace and actual spectral construction remain open.

## D8. Laguerre-Polya class and Jensen polynomials

### Endpoint and last proved node

For the appropriate xi Taylor sequence, RH is equivalent to hyperbolicity of every Jensen
polynomial in every required degree and shift. Griffin-Ono-Rolen-Zagier prove
[eventual fixed-degree hyperbolicity](https://arxiv.org/abs/1902.07321), a density-one result in
their normalization, and explicit small-degree cases through degree eight.

### Exact missing object

Prove hyperbolicity for all degrees and all shifts, especially the finite exceptional initial
region left by every fixed-degree asymptotic theorem. Equivalently, produce a nonasymptotic
structure theorem controlling those exceptions uniformly in degree.

### Obstacle validity

Farmer's primary-source critique,
[Jensen polynomials are not a plausible route](https://arxiv.org/abs/2008.07206), explains that
Hermite attraction is an asymptotic universal law shared far beyond RH functions. It therefore
does not provide evidence about the finite exceptional polynomials that carry the RH content.
This is a strong route assessment, not an impossibility theorem for all Jensen arguments.

The project adds a physical-kernel warning: strict TP2 holds, but PF5 fails by an exact full-series
Lean certificate. Thus a naive path from stronger total positivity to all Jensen hyperbolicity is
closed at order five.

### Unused machinery and omission audit

Computer algebra and exact root certificates can clear finite regions, but a cutoff growing with
degree recreates the global problem. No source-backed overlooked uniform mechanism was found.

Formalization fit: `4/5`. Machine-task fit: `5/5` for finite polynomials, `2/5` for uniform degree.

### Discriminating probes

1. Require every proposed asymptotic inequality to give an explicit shift bound uniform enough
   to cover all degrees; reject fixed-degree limits.
2. Test the inequality on entire functions with the same Hermite asymptotics but known nonreal
   zeros.
3. Do not extend PF-order calculations unless the surviving order has a proved implication to
   all required Jensen polynomials.

### Post-survey H8 campaign

Fresh source audit adds Duran 2024: Brenke-polynomial real-rootedness supplies further RH
equivalences but no theorem controlling every degree and shift. Campaign
`FALSIFICATION-20260723-H8-JENSEN-EVENTUAL-HYPERBOLICITY-01` preregisters an exact coefficient
model that satisfies fixed-degree eventual hyperbolicity and arbitrary finite-wedge checks while
failing one explicit degree-two window. The model tests only the quantifier promotion and is not
claimed to be the xi coefficient sequence.

The campaign is publicly closed at final-ledger commit
`c80b9e6a4114d7d591f4db72e6326810d0fe9d1c`, Lean Action run `29951256366`, build job
`89029220136`, in `1m53s`. It closes only the generic promotion; the actual-xi all-index theorem
and RH remain open.

## D9. de Branges spaces and canonical systems

### Endpoint and last proved node

de Branges developed Hilbert spaces of entire functions and conditional positivity structures
that can force real zeros. His 1986
[Hilbert-space program](https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society-new-series/volume-15/issue-1/The-Riemann-hypothesis-for-Hilbert-spaces-of-entire-functions/bams/1183553352.short)
is a serious structural route, not a proved zeta RH theorem.

Conrey and Li's
[positivity audit](https://arxiv.org/abs/math/9812166) examines the proposed zeta/L-function
conditions and shows the key positivity requirement is not satisfied in the needed form. The
accepted de Branges theorems survive; the proposed zeta input does not.

### Exact missing object

Construct a source-defined Hermite-Biehler/canonical-system object attached to zeta for which:

- the Hilbert-space axioms and positivity actually hold;
- the spectrum is exactly the complete xi zero divisor with multiplicity;
- the implication to RH does not assume the desired zero location in constructing the space.

### Obstacle validity

The Conrey-Li objection is current for the audited positivity condition. It does not prove that no
different canonical system can work. However, replacing the failed form by an unspecified
"renormalized positivity" is not a concrete opening.

### Unused machinery and omission audit

D6 may supply a natural ground-state entire function and operator from which a canonical system
could be derived without guessing the failed positivity. That cross-route construction is the
only bounded opening found. The project's separate Freedman audit eliminates one abstract
contraction inference but leaves any concrete energy estimate open.

Formalization fit: `2/5`. Machine-task fit: `3/5` for finite canonical systems and countermodels,
`1/5` for the full zeta correspondence.

### Discriminating probes

1. Formalize the exact Conrey-Li failed inequality and its counterexample as a permanent route
   boundary.
2. Ask whether the D6 finite-prime ground states generate a canonical system with a provable
   monotonic Hamiltonian; falsify at finite cutoffs first.
3. Reject any system whose definition uses the xi zeros as input without an independent
   arithmetic/trace construction.

### Post-survey D9 source correction

Suzuki 2026, arXiv:2606.09096v1, gives an unconditional finite-interval theorem absent from the
original atlas: characteristic functions of self-adjoint extensions have only real zeros. Its
Corollary 6 proposes compact-uniform convergence on every compact subset of `C` after a
finite-valued exponential normalization to `z^2*xi/xi'`.

The displayed statement does not specify regularity of the normalizing exponent. Without such
regularity, zero-location persistence is not justified by uniform convergence alone. With the
natural entire-function repair, the target must admit an entire extension, while reciprocal
logarithmic derivatives can have nonremovable poles at nonzero critical points. Campaign
`FALSIFICATION-20260723-D9-SUZUKI-RECIPROCAL-LIMIT-01` audits both interpretations with generic
Lean countermodels before any attempt at the actual operator limit. This does not refute the
source's unconditional finite theorem or a possible meromorphic reformulation.

The local Lean implementation proves the literal countermodel with the standard
`TendstoUniformlyOn` predicate on every set and proves the finite-extension obstruction with an
exact symmetric quartic derivative calculation. These results close only the two generic
interpretation tests. The actual canonical-system limit remains open, and any meromorphic repair
must specify convergence away from poles plus a valid zero-transfer theorem.

## D10. Arithmetic criteria, character sums, and Speiser derivatives

### Endpoint and last proved node

Robin/Lagarias divisor-sum inequalities and several prime-counting error terms are exact
equivalents of RH. Lagarias' [elementary inequality](https://arxiv.org/abs/math/0008177) is fully
explicit but does not supply a proof mechanism by itself.

Speiser's
[geometric derivative criterion](https://eudml.org/doc/159737) proves that RH is equivalent to
the absence of zeros of `zeta'` in the left half of the critical strip, with conventions handled
carefully. It relocates the zero problem to critical points of the zeta map.

Conrey's 2024
[Character Sums and the Riemann Hypothesis](https://arxiv.org/abs/2404.19647) proves that a
specific arithmetic inequality implies RH and proposes a route through Legendre-symbol sums.
Within this survey boundary it is an open proof program, not a proved inequality.

### Exact missing object

- Arithmetic inequality subdoor: a uniform divisor/character-sum estimate at the RH-strength
  exponent and for every required modulus or integer.
- Speiser subdoor: an unconditional theorem excluding every zero of `zeta'` from
  `0 < Re(s) < 1/2`, including multiplicity and boundary cases.

### Obstacle validity

Elementary appearance is not reduced strength: the divisor inequalities are equivalent to RH.
Finite verification cannot close the all-integer quantifier. Speiser is also an equivalence, and
known information on the distribution of derivative zeros does not exclude all of them from the
left half-strip.

The Conrey character-sum reduction is sufficiently recent and exact to merit a falsification
campaign. Its proposed estimate must be checked against Pólya-Vinogradov/Burgess-scale barriers
and extreme residue patterns before being ranked as more than a restatement.

### Unused machinery and omission audit

This door has moderate omission evidence because the character-sum mechanism is concrete and
separate from merely checking Robin's inequality. Speiser could also provide D3/D4 with the
exceptional-zero localizer they lack, but no source-backed estimate currently does so.

Formalization fit: `4/5` for finite arithmetic and Speiser statement alignment, `2/5` for complex
value distribution. Machine-task fit: `5/5` for finite falsification, `1/5` for uniform bounds.

### Discriminating probes

1. Extract Conrey's exact inequality and RH implication, then search finite moduli and extremal
   character patterns for failure of the proposed strengthening.
2. Compile the exact Speiser equivalence against the project's xi/zeta divisor, including the
   pole and trivial-zero exclusions.
3. Test whether a D3 density-one hypothesis plus a quantitatively stated Speiser estimate truly
   excludes one off-line orbit; use a finite symmetric divisor countermodel first.

## D11. Generalized L-functions, automorphic forms, and Iwasawa analogies

### Endpoint and last proved node

GRH for a class containing zeta implies RH, but this is a stronger target rather than a shortcut.
Automorphic L-functions bring Euler products, functional equations, trace formulae, converse
theorems, and family statistics. Katz-Sarnak's
[zeros and symmetry program](https://doi.org/10.1090/S0273-0979-99-00766-1) gives a powerful
classification of family behavior and a proved function-field model.

Iwasawa main conjectures identify p-adic L-functions with characteristic ideals of arithmetic
modules. This is a major successful arithmetic bridge, but it concerns p-adic interpolation and
Selmer/class-group structure. No direct p-adic analogue of archimedean RH is known in the surveyed
sources.

### Exact missing object

Produce a theorem transferring a proved family, automorphic, trace, or p-adic structure to the
real parts of every zero of the individual Riemann zeta function. Family density and local Euler-
factor bounds do not provide that transfer.

### Obstacle validity

The Davenport-Heilbronn example in D13 shows that functional equation and symmetry without the
right Euler-product/arithmetic structure allow off-line zeros. Adding an Euler product defines a
more rigid class, but GRH for that class remains open. Iwasawa theory controls a different
topology and cannot be substituted for an archimedean zero theorem.

### Unused machinery and omission audit

The route is best used as a robustness test: a proposed zeta mechanism should either extend to
the expected self-dual L-functions or explain which zeta-specific input it uses. No overlooked
direct transfer theorem was found.

The follow-up campaign `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01` therefore tests
the strongest literal inclusion already available in Mathlib: the modulus-one Dirichlet
L-function is Riemann zeta. It also tests the one-way product transfer and the obstruction from an
extra factor that inserts an off-line critical-strip zero. This is a transfer-logic audit, not a
generalized RH result.

Formalization fit: `1/5`. Machine-task fit: `2/5` for finite local factors and symmetry models.

### Discriminating probes

1. Apply each shortlisted D6 or D10 mechanism to a Davenport-Heilbronn-type function and a genuine
   automorphic L-function; identify exactly where the Euler product enters.
2. Reject any p-adic analogy that does not state a map from characteristic-ideal zeros to complex
   zeta zeros.
3. Use modular L-functions to test whether the 2025 D3 derivative optimization is zeta-specific or
   structural; do not infer individual GRH from a family proportion.

## D12. Certified finite computation

### Endpoint and last proved node

Turing-style zero counting and interval arithmetic can certify that every zero below a finite
height lies on the critical line. Platt-Trudgian prove the statement through height
`3 * 10^12` and, combined with the Polymath barrier table, obtain `Lambda <= 0.2`.

This is genuine unconditional information. It is finite-height information.

### Exact missing object

A global analytic theorem must show that no off-line zero exists above the certified height. Any
such theorem strong enough for all heights is the unresolved RH edge unless it obtains leverage
from another route.

### Obstacle validity

No amount of finite verification alone proves a universal height statement. Computation becomes
mathematically decisive only when an analytic theorem reduces the global problem to a finite
certificate, as it does for positive de Bruijn-Newman upper bounds.

### Unused machinery and omission audit

Lean and interval arithmetic are excellent for proof-producing finite matrices, zero counts, and
spectral gaps in D6/D10. The user has parked additional H6 numerical upper-bound optimization, so
this door should support the selected analytic campaign rather than choose its own constant.

Formalization fit: `5/5`. Machine-task fit: `5/5` finite, `0/5` standalone global.

### Discriminating probes

1. Use certified computation only after a theorem states the finite certificate that would close
   an analytic edge.
2. For D6, certify spectral gaps and parity at fixed cutoff and matrix size, while keeping all
   continuum limits explicit.
3. Maintain a hard prohibition on finite-height-to-global promotion.

The follow-up campaign `FALSIFICATION-20260723-H14-FINITE-HEIGHT-PROMOTION-01` isolates that last
prohibition from the already compiled H11 density-one and H8 eventual-index obstructions. It tests
an arbitrary finite height using a finite open-strip orbit closed under conjugation and
`s |-> 1-s`, while retaining an off-line point above the checked height. The witness is generic and
does not challenge actual certified zero computations.

## D13. Countermodels and falsified mechanisms

### Last proved nodes and what they forbid

- Odlyzko and te Riele's
  [disproof of the Mertens conjecture](https://doi.org/10.1515/crll.1985.357.138) shows that a
  historically plausible strengthening implying RH can simply be false.
- Davenport and Heilbronn's
  [Dirichlet-series construction](https://doi.org/10.1112/jlms/s1-11.4.307) has a Riemann-type
  functional equation but off-line zeros. Functional equation and reflection symmetry are not
  enough; the Euler product matters.
- Diamond-Montgomery-Vorhauer's
  [Beurling-prime construction](https://deepblue.lib.umich.edu/bitstream/handle/2027.42/46253/208_2005_Article_638.pdf)
  shows that prime-number-theorem-like regularity can coexist with severe generalized-zeta zero
  behavior. Arguments using only coarse prime-counting axioms may not be zeta-specific enough.
- The project has kernel-checked failures of recent Nyman projection/ladder steps, generic reverse
  heat-Li transfer, generic adjacent-gap propagation, PF5 for the actual xi kernel, prime-by-prime
  Gaussian Weil semidefiniteness, and an abstract Volterra contraction inference.

### Current use

These results do not lower the chance of RH itself. They define a regression suite for every new
claim. A candidate that also "proves RH" for Davenport-Heilbronn, survives after inserting one
sparse off-line orbit, or uses only the formally insufficient contraction premises is rejected
before Lean proof work.

Formalization fit: `5/5`. Machine-task fit: `5/5`.

### Discriminating probes

1. Run every structural conjecture on a functional-equation counterexample and a Beurling system.
2. Insert one symmetric off-line orbit into every asymptotic zero model.
3. Preserve all project counterexamples as theorem-level CI regressions.

## Cross-route interfaces

### I1. Weil positivity -> finite-prime ground states -> spectral convergence

This is the recommended interface. D1 supplies the exact RH-equivalent quadratic form, D6 supplies
a new real-zero theorem for its finite-cutoff ground states, D12 can certify finite spectral
facts, and D7 explains why a uniform spectral limit is the number-field substitute for finite
Frobenius rigidity. The unresolved edge is convergence, not zero computation.

### I2. Mollifiers/density -> exceptional-zero localizer

D3 and D4 can make off-line zeros sparse but do not eliminate the last one. D10 Speiser or D1 Li
could detect one orbit, but the implication must be quantitative and uniform. Existing finite
divisor countermodels defeat any argument using density alone.

### I3. Entire functions/canonical systems -> ground-state operator

D8's asymptotic Jensen results are too universal and D9's original positivity condition fails.
D6 may provide a non-guessed canonical system whose real-zero property is proved before taking the
zeta limit. This interface is secondary to proving the limit itself.

### I4. Function-field rigidity -> semilocal truncations

D7 proves that finite traces plus reciprocal pairing can force a circle. D6 has semilocal trace
objects but an infinite limiting spectrum. The missing uniform-tail theorem is the precise point
where the analogy currently stops.

## Recommendation

Select the D6/D1 finite-prime Weil ground-state convergence edge for the next bounded campaign,
subject first to M0 definition alignment. The immediate target should not be RH itself phrased as
"the approximating zeros converge." It should be the strongest source-exact prerequisite that
can fail independently:

`ALIGN-20260722-CONNES-WEIL-FINITE-PRIME-01`: prove that the finite-prime quadratic form and
constraint space in the 2025-2026 sources are exactly the project's compact Weil form at the
corresponding support cutoff, and state a no-hidden-RH theorem showing which spectral convergence
hypotheses imply compact-uniform convergence of the transforms.

If alignment succeeds, preregister a `PROOF-ATTEMPT` on uniform simplicity/spectral gap or a
`FALSIFICATION` campaign on Galerkin/cutoff uniformity. If alignment fails, record the mismatch and
move to the runner-up rather than repairing definitions informally.

The runner-up is D3: reconstruct the 2025 derivative-combination variational problem and determine
whether its underused freedom changes the attainable critical-line proportion under proved
arithmetic inputs. Any follow-on must separately confront the sparse exceptional-zero barrier.

## Ranking-reversal evidence

The recommendation changes if any of the following is established:

- **D6 falls:** a finite-cutoff ground state is not simple/even, the source forms do not align, or
  a proved lower bound shows the candidate eigenfunctions cannot converge to the Riemann kernel.
- **D3 rises:** the 2025 optimization plus a proved mean-value theorem yields proportion one and a
  separate quantitative theorem excludes density-zero exceptions.
- **D10 rises:** Conrey's character-sum route produces a noncircular estimate beyond known
  character-sum barriers, or Speiser control supplies the missing exceptional-zero localizer.
- **D2 rises:** an exact theta-specific all-index heat-Li sign representation is discovered and
  survives the project's generic and PF5 countermodels.
- **D7 rises:** a number-field cohomology/trace object with positive pairing and uniform infinite
  spectral tail is constructed.

Absent such evidence, further optimization of the H6 numerical upper-bound constants remains
parked, and finite/asymptotic results are not promoted to RH progress.

## Survey outcome

- `classification`: `ROUTE_ATLAS_COMPLETED / NEW_OPEN_EDGE_IDENTIFIED`.
- `rh_frontier_delta`: `0`.
- `hard_gap_delta`: `0`.
- `route_map_delta`: `1` (all admitted doors now have a common omission-seeking card).
- `new_opening`: the 2025-2026 finite-prime Weil ground-state convergence program, classified
  `SOURCE-SUGGESTED / UNPROVED`.
- `runner_up`: the 2025 short-mollifier derivative-combination optimization, bounded by the long
  mean-value and sparse-exception gaps.
- `Lean_verification`: not applicable to the literature classifications in this file. Existing
  project theorem claims retain their recorded TargetChecks and axiom audits; no new mathematical
  declaration is introduced by this survey.
- `compaction_state`: two inherited compactions; canonical governance and frontier files were
  reread before substantive work and again before evidence publication resumed.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: active.
- `public_implementation`: commit `62c813f51020b2c012a4770c204ea97b3893d87e` passed Lean
  Action run `29921175166`, build job `88926780992`, in `1m49s`.
- `public_closure`: evidence commit `f8cce8ae32f716cc34087cee5319b23656c8733a` passed Lean
  Action run `29921582753`, build job `88928153258`, in `1m48s`.

## Post-atlas D3 mechanism update: 2026-07-23

The D3 theta-infinity consumer is now publicly closed at final-ledger commit
`d4196d0f47d42f1c95d29b48dd341b9a469c514b`, Lean Action run `29968166845`, build job
`89084084918`, in `1m54s`. It proves the real-cutoff interpolation and exact individual-zero
power consumers; it does not prove the analytic bridge or Farmer's moment conjecture.

The next D3 submechanism is `H1-BETTIN-GONEK-AUXILIARY-REGULARIZATION-01`: a source-exact audit of
the removable singularities and selected-zero pole coefficient in equations `(2.2)`--`(2.3)`.
This continues the historical mechanism audit and does not mark D3, H1, or mollifiers exhausted.

That submechanism now reaches its local registered endpoint. Lean's divided-difference
regularization proves the source quotient holomorphic, and the selected-pole coefficient is exact
and nonzero. No local normalization gap was found. The remaining D3 bridge is the genuinely
analytic Mellin/decay/contour/convolution chain. The 8,752-job full build passes locally, and
frozen implementation commit `2dd7fcb2284b9fe9afd3e01792a6a6c199a770f9` passed public Lean
Action run `29969572291`, build job `89088421970`, in `2m4s`; immutable evidence and final ledger
were separated. Immutable-evidence commit `fdd688ba7e2157ec616b8f58a366b86c94c7f0e9` passed run
`29969746284`, build job `89088970037`, in `2m0s`; only the final ledger remains.

After the auxiliary final-ledger CI, route selection returned to D6. The next source-instantiation
node is `H7-WEIL-POLE-RANK-TWO-INSTANTIATION-01`: compile the actual closed pole
divided-difference matrix and its exact even-positive minus odd-positive rank-two decomposition.
This does not assert a sign for the total Weil matrix and does not replace the open Herglotz,
simple-even, or source-limit edges.

That source block now reaches its local registered endpoint. Lean proves the literal pole
coefficient positive, the closed divided-difference formula, and the exact even-positive minus
odd-positive rank-two sign law. No normalization mismatch was found. The result also makes the
remaining mechanism sharper: the odd pole term has the adverse sign, so actual prime and
archimedean blocks must establish the total parity ordering. The 8,753-job full build passes;
public implementation gates remain.
