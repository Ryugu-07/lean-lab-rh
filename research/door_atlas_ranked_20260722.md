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

The 2026-07-26 route recheck also finds a historically prior omission in the formal repository:
Hardy's theorem is cited, but the actual project-xi real critical-line coordinate and its
sign-change-to-zero consumer are absent. This does not change the published proportion frontier.
It opens `H1-HARDY-CRITICAL-LINE-REAL-SIGN-BRIDGE-01` so that a later reconstruction of Hardy's
transform must produce literal signs feeding an exact nontrivial-zero witness.

That fixed node now compiles locally: the project-xi coordinate is real, even, and continuous,
and both weak endpoint-sign orientations produce an actual interval critical-line zero. The
remaining omission-bearing edge is the source transform or estimate that produces arbitrarily
high separated sign brackets; no such signs are asserted by the compiled consumer.

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

### Post-survey H9 Pólya--Turán correction

The initial atlas named Pólya-type sign claims only inside the failed-mechanism control card.  That
was too compressed.  Pólya's unweighted Liouville sum, Turán's harmonic-weighted Liouville sum,
and Turán's finite zeta Dirichlet polynomials are distinct historical mechanisms with distinct
failure evidence.

Campaign `LITERATURE-20260726-H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01` locally compiles the source
boundary and exact finite Abel transform between the first two sums.  It proves that Pólya-prefix
nonpositivity from index two supplies only the upper bound `T(N)<=1/2`, then gives a generic exact
witness showing that prefix nonpositivity alone does not force weighted positivity.  The witness
is not Liouville, neither false global sign claim is assumed, and no repaired RH equivalence is
promoted to unconditional progress.

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
frozen implementation commit `4b22712b531df010901e9813710b8ad145e60392` passed public Lean
Action run `29971043533`, build job `89092937602`, in `2m30s`. Immutable evidence and final-ledger
gates remain. Immutable-evidence commit `58665041b17686cf6ac02abd2b89a295406838f4`
passed run `29971296016`, build job `89093681779`, in `1m34s`; only final-ledger CI remains.

The pole-block final ledger then passed as commit `48e57d28b7e8ec98042cb7f21b836f6eb1c98adc`,
Lean Action run `29971448611`, build job `89094128646`, in `1m47s`. The next D6 source node is
`H7-WEIL-FINITE-PRIME-SOURCE-INSTANTIATION-01`: compile the literal finite von Mangoldt sine
source and test its parity signs before attempting the complete Herglotz scalar inequality. The
registered `C=16,q=8` constituent has frequency `1/4` and is predicted to have opposite strict
signs on explicit level-one even and odd vectors. This is a source-exact falsification test of
termwise semidefinite compensation, not a sign claim for the aggregate prime block and not a
numerical bound campaign.

That prime-source node now reaches its local registered endpoint. Lean certifies the literal
von Mangoldt source and derivative diagonal, the exact finite atom sum, and reflection-sector
preservation. The `C=16,q=8` atom has the predicted opposite strict signs. This sharpens D6:
neither the adverse odd pole term nor individual prime atoms admit a termwise common-sign proof;
aggregate arithmetic and archimedean balance are essential. The 8,754-job full build passes;
frozen implementation commit `cc264cde977a8b04e596d267aa6656cd8cbf4058` passed public Lean
Action run `29973199798`, build job `89099433656`, in `2m8s`. Immutable evidence and final-ledger
gates remain. Immutable-evidence commit `6a697d92caa485fe1f274ffb5495e8cd3379b297` passed run
`29973451920`, build job `89100185836`, in `2m20s`; only final-ledger CI remains. No aggregate
prime sign, Herglotz bound, or source limit is claimed.

The finite-prime campaign then publicly closed at final-ledger commit
`26a6f93ccc4b7532f21b50acc2ffbb1debfd338c`, Lean Action run `29973710220`, build job
`89100966535`, in `1m33s`. Cross-route ranking returned to D3 at
`H1-BETTIN-GONEK-H-MELLIN-IDENTITY-01`, the literal equation `(2.1)` bridge from the actual
real-cutoff mollifier to reciprocal zeta.

That endpoint now compiles locally. Lean proves the finite and pointwise supported Mobius
expansions, the scaled logarithmic kernel, absolute integrated-norm summability on
`Re(w)>3/2`, Bochner Fubini, Mellin convergence, and the exact source `H_t(w)` formula. No cutoff,
boundary, branch, exponent, or normalization mismatch was found. The remaining D3 mechanism is
now concentrated at inverse Mellin support/boundedness, vertical decay, convolution, contour
movement, selected-residue lower bounds, the moment-to-power bridge, and Farmer's moment
conjecture. D3 is not exhausted; D6's archimedean source block and the wider historical atlas stay
active competitors for the next campaign.

The frozen implementation commit `1ca590891a51da76712e8a2dd177287de56d0b43` passed public Lean
Action run `29976558428`, build job `89109449098`, in `2m6s`. Proof source is frozen; immutable
evidence commit `17a1c46f2cb62c1aa351d2d918e872f1cbc9340e` passed run `29976815386`,
build job `89110232514`, in `1m53s`. Only final-ledger publication remains before successor
selection.

The H1 Mellin final ledger then passed as commit `98bc69b87c66212e92dc2efc814bbffc4cf847dd`,
Lean Action run `29977016712`, build job `89110861524`, in `1m55s`. Cross-route ranking selects
the D6 node `H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01`, because pole and prime source blocks already
share the finite divided-difference carrier and the archimedean source is the last missing actual
block before total assembly can be tested.

The fixed probe starts from the literal sine-cosine interval source and treats its derivative at
integer nodes as a falsification guard. It targets the exact rank-two Cauchy density, reflection,
quadratic sum of squares, and conditional semidefiniteness of the integrated increment. It does
not assume the source's Arb-assisted `h_+(T)>0` threshold, and does not claim strict tail order,
total positivity, a tail limit, the total Weil sign, Herglotz, simple-even structure, source
convergence, H7, or RH. D3 and the rest of the historical atlas remain active after this bounded
D6 campaign.

That D6 source node now reaches its local registered endpoint. The literal interval source and
its true derivative diagonal agree exactly with the published Cauchy formulas. Lean proves the
rank-two density, parity preservation, all-vector two-square identity, digamma-density
continuity, and conditional PSD of the entrywise interval increment. No source mismatch was
found.

This completes the individual finite pole, prime, and archimedean source instantiations, not the
total Weil argument. Aggregate prime cancellation, the adverse odd pole term, unconditional
`h_+` positivity, total parity ordering, Herglotz, simple-even uniformity, source limits, H7, and
RH remain open. Frozen implementation `9546806d8c3d0afeef9f6c7ee674982e8710576a` passed public
Lean Action run `29979643215`, build job `89118608592`, in `2m32s`; immutable evidence
`213af9d7a26a23a828b12e5b7523d520c424b1b4` passed run `29979851450`, build job `89119211639`,
in `1m56s`. Only final-ledger CI remains before cross-family reranking.

H7 final-ledger commit `64782a564a19a8e9c25a0d520bcbbcb2397b807a` then passed Lean Action
run `29980056767`, build job `89119806051`, in `1m36s`. Cross-family ranking re-enters D3/H1 at
the exact Bettin--Gonek `J_t` contour equation `(2.5)`. The actual mollifier Mellin transform,
regularized auxiliary factor, and selected-pole coefficient are already compiled on the two sides
of this edge. Campaign `LITERATURE-20260723-H1-BETTIN-GONEK-J-CONTOUR-01` preregisters the literal
product cancellation, finite-to-infinite one-pole shift, `x`-uniform boundary bound, exact residue
norm, and selected-zero lower inequality. Inverse Mellin support, convolution `(2.4)`, the full
moment transfer, Farmer's conjecture, H1, and RH remain open.

The campaign now reaches its local compiled endpoint. Lean verifies the literal product
cancellation, both full vertical integrals, the exact selected-pole rectangle, horizontal
`O(|u|^-4)` decay, and the normalized infinite contour identity. The zero line has the explicit
uniform bound `2`, and the selected residue has a strictly positive scale times
`x^(Re(rho)+1/2)`. No source normalization mismatch was found.

This raises the historical H1/Bettin--Gonek route because equations `(2.1)`, `(2.3)`, and `(2.5)`
now use actual source objects. It does not exhaust H1: inverse Mellin support/boundedness,
standalone `G_t` decay, convolution `(2.4)`, the moment-transfer inequalities, Farmer's
conjecture, H1, and RH remain open. Public freeze/evidence gates precede the next atlas rerank.

The local freeze gates pass: the new source is 947 lines, the exact aggregate TargetCheck and
selected standard-only axiom audit compile, the forbidden scan is empty, `git diff --check`
passes, and the full 8,757-job build succeeds.

Frozen implementation `66f5260c6ae71dbb8c09d31000fd6c13f9bf7ec1` passed public Lean
Action run `29982986397`, build job `89128701960`, in `2m14s`. Proof source remains frozen;
immutable-evidence commit `6fccd535aa41d8e953b16bd28537d9984d00be34` passed run
`29983227759`, build job `89129435959`, in `1m54s`. Final-ledger CI precedes successor
reranking.

H1 J-contour final-ledger commit `c4287392fe4ba0e9d588aca1b13121ae13a27654` passed public Lean
Action run `29983416809`, build job `89129994376`, in `1m34s`. Fresh cross-family ranking
selects D6/H7's finite Guinand--Weil dictionary source calculus. The pole, prime, and
archimedean source matrices are now actual objects, but the project still lacks the closed-form
transport from a finite even vector to the band-limited test weight whose explicit formula is
claimed to equal the matrix quadratic.

Campaign `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-01` fixes the literal trigonometric
polynomial, Volterra kernel, single-frequency divided-difference identity including the diagonal,
finite atom superposition, actual von Mangoldt prime block, and Fourier cutoff coordinate. It
does not claim the full zero-sum dictionary, test-class admissibility, inverse/density, source
limits, H7, or RH. Public preregistration CI gates production Lean.

The fixed source-calculus probe now succeeds locally. Reflection-even coefficients make the
literal `T_u` and `K_u` real, both pair-integral branches match the published sine-source matrix,
and finite superposition reaches the actual project prime matrix. The exact cutoff substitution
rewrites that matrix quadratic as the induced finite Fourier prime side. No factor, sign,
diagonal, or coordinate mismatch was found.

This is evidence that the finite H7 matrix is not merely formal bookkeeping: its prime quadratic
is an exact source test value. The route is still blocked before the zero side by admissibility
and boundary regularity of the piecewise Fourier weight, plus the pole and archimedean
transports. All local gates, including the full `8758/8758` build, pass; frozen implementation
commit `e5f011dbbf9f7c40a802ab88f9a91aa6aea3f370` passed public Lean Action run
`30072543069`, build job `89416248542`, in `2m6s`. Docs-only immutable-evidence commit
`59adecc50ac343912eca3ef1989a5b4a642103e7` passed run `30072806474`, build job
`89417024378`, in `1m36s`. Only final-ledger CI precedes the next atlas ranking. H7 and RH
remain open.

The H7 Volterra source-calculus campaign then publicly closed at final-ledger commit
`46befa6a2e935e73b077140e5e9df24df3623db6`, Lean Action run `30073083407`, build job
`89417854356`, in `1m39s`.

Source rereading corrects the next D6 edge. Groskin Lemma 2.2 claims that every finite even-sector
vector, not only a moment-neutral vector, induces an admissible Guinand--Weil test. The compact
Fourier weight is continuous and endpoint-vanishing but only piecewise smooth; its zero-extended
derivative has bounded variation, and the source's inverse-square strip decay uses a Stieltjes
second integration by parts.

Campaign `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01` therefore targets the
literal boundary regularity, entire/even test, exact affine rotation into the project's Laplace
and xi-divisor coordinates, horizontal-strip decay, and absolute multiplicity-bearing zero
summability. The project compact explicit formula requires global `C^6`, so the weaker-class
arithmetic formula and total matrix-to-zero identity remain separate open edges. After this
campaign, D3/H1, H12 Speiser, H2 localization, and any exact D6 zero-side transport are reranked;
D6 is not selected automatically.

The fixed admissibility probe now succeeds locally. Lean proves the exact boundary continuity,
compact support, entire/even structure, `log(C)` exponential type, affine zero coordinate, and
horizontal-strip inverse-square decay. Two ordinary integrations by parts on each smooth
half-band retain the derivative jumps, so the anticipated missing Stieltjes API is not a blocker.
The resulting values and norms are summable over the actual multiplicity-bearing xi divisor by
the existing Hadamard reciprocal-square majorant.

This promotes the next exact D6 omission candidate from admissibility to the weaker-regularity
arithmetic explicit formula and total matrix-to-zero transport. It does not prove that edge, H7,
or RH. The exact checks, standard-only axiom audit, empty forbidden scan and patch check, and
full `8759/8759` build pass. Public freeze/evidence gates and a fresh H1/H12/H2/H7 comparison
remain mandatory.

Frozen implementation `257b80dcda7d4a68a9c6a4b9860b1a97fa42c0ca` passed public Lean Action
run `30140659408`, build job `89633127915`, in `2m37s`. The proof source is frozen; docs-only
immutable evidence `317a610f22637fd91ae84f125b3086f552081813` passed run `30140782861`,
build job `89633473809`, in `1m32s`. Only final-ledger CI precedes the fresh route comparison.

The H7 admissibility campaign then publicly closed at final-ledger commit
`f7c137b128406dd55b09d81411c2d7e38d81f731`, Lean Action run `30140898700`, build job
`89633790335`, in `1m36s`.

The mandatory D3/D6/H12/H2 rerank selects D3/H1's inverse-Mellin and convolution bridge.
Bettin--Gonek equations `(2.2)`--`(2.4)` pass from the standalone auxiliary-factor decay to a
supported bounded inverse Mellin kernel and then to the actual mollifier convolution. The
project has the literal `G_t`, `H_t`, mollifier, `J_t`, and selected-zero contour residue, but not
these intermediate inferences.

This is a materially new H1 re-entry: the prior contour campaign canceled zeta before estimating
the integrand, whereas the new endpoint must control `G_t` itself, move the inversion line to
zero and arbitrarily far right, and justify the source Fubini exchange. H7 weak-regularity
arithmetic transport remains the strongest reserve; H12 counts and H2 localization remain open.
No family is marked exhausted, and original conjecture/falsification lanes remain open.

### Post-H9 rerank: H7 finite dictionary explicit formula

The H1 inverse-Mellin/convolution bridge subsequently compiled and publicly closed, including
the literal inverse kernel, support, boundedness, actual mollifier convolution, and source
interval bound. The remaining H1 edge begins at Cauchy--Schwarz and critical-line moments.

The intervening H9 Polya--Turan audit publicly closed after compiling the exact Abel relation and
the generic sign-shortcut obstruction. That campaign repaired a historical coverage omission but
did not advance the RH frontier.

The fresh H1/H2/H7/H10/H11/H12 comparison now selects
`H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`. This does not optimize the numerical
archimedean tail budget. It attacks Theorem 2.5 of arXiv:2607.02828v1, the exact claim that every
literal finite dictionary value is a multiplicity-bearing zeta-zero sum.

The vector-to-test map, admissibility, xi-coordinate summability, and finite prime source already
compile. The missing theorem is the weak-regularity Guinand--Weil arithmetic formula and the
complete zero/pole/prime/archimedean transport. The direct selected-height route currently stops
at a sharp analytic mismatch: inverse-square dictionary decay does not absorb the project's
fourth-power xi logarithmic-derivative top-edge bound. A direct sharper contour estimate and a
source-faithful smooth-approximation proof are preregistered as separate attacks. H7 and RH remain
open.

### H7 finite dictionary explicit formula local result

The direct contour attack succeeds. Jensen's formula and order-one growth of `riemannXi` give
cofinal norm-ball zero counts of order `R^(5/4)`, which supply long zero-free selected heights.
At those heights the usable logarithmic-derivative bound is `O(R^(7/4))`, so the dictionary's
inverse-square decay makes the top horizontal integral vanish.

Lean now proves the multiplicity-bearing zero sum equals the exact finite prime, pole, and
archimedean source expression, including equality of the prime term with the existing finite
matrix quadratic and equality of the Gamma term with the literal middle-line `h_+` integral.
The compact `C^6` approximation fallback was not needed.

This closes Theorem 2.5's finite explicit-formula edge locally. Positivity, inverse/density,
cutoff limits, simple-even ground states, H7, and RH remain open. The result records
`source_analytic_bridge_delta=1` and `rh_frontier_delta=0`; public implementation evidence and
fresh cross-route ranking follow.

Frozen implementation commit `f0d76ee081c22381f6ffc208b024268b090fc35c` passed public Lean
Action run `30187598839`, build job `89754974406`, in `2m48s`. Docs-only immutable-evidence
commit `0a15b1d951c978ece49da9b477686cc1e61d6939` passed run `30187720024`, build job
`89755296426`, in `1m33s`. Final-ledger commit
`31362f4044e99651d7567f91dc4fd8a701974f38` passed run `30187802034`, build job
`89755512303`, in `1m29s`; the fixed H7 edge is publicly closed.

### Post-H7 rerank: H1 Bettin--Gonek moment-to-power bridge

The cross-route comparison returns to D3/H1, but not to the already closed inverse-Mellin
endpoint. Equations `(2.1)`--`(2.5)` now compile for the actual mollifier and selected zero. The
remaining source theorem is the full moment-to-power assembly that turns a uniform
`I_N(0,T)` bound into an individual-zero exclusion.

The source `[0,T]` normalization exposes a useful simplification: fixed positive zeta mass on
one low-height compact interval is enough for the lower side. It can be combined with uniform
residue bounds and a unit-interval partition of the real cutoff, reducing the upper side to the
integer moments already named by `FarmerLongMollifierBound`.

This is selected as a complete known-theorem formalization. On success, Farmer's arbitrary-length
mollifier conjecture remains the sole open premise in this H1 implication to RH. H12 analytic
counts, H2 actual bow exclusion, H10 transfer, and H7 positivity/density remain open reserves.

### H1 Bettin--Gonek moment-to-power bridge local result

The fixed-low-height attack succeeds. Lean proves positive critical-line zeta squared mass on
`[0,1]`, a selected-residue lower bound uniform there, and translation invariance of the
inverse-Mellin majorant. Unit-interval cutoff interpolation and finite Cauchy reduce the source
real-cutoff integral to Farmer's exact integer moments; `floor(T^theta)` and logarithmic
absorption preserve the source exponent.

The resulting theorems prove `BettinGonekMomentToPowerBridge theta` for every positive `theta`
and the direct implication `FarmerThetaInfinityConjecture -> RiemannHypothesis`. This closes the
known conditional analytic bridge and shows that a full critical-line second-moment asymptotic
was stronger than necessary for this endpoint. Farmer's arbitrary-length moment conjecture
remains open, so D3/H1 and RH are not marked solved or exhausted.

Frozen implementation commit `d07fecd2f00748cf0dc2a4c19d15d89bb740a2e1` passed public Lean
Action run `30189533073`, build job `89760104494`, in `2m31s`; the proof source is frozen while
the docs-only evidence sequence proceeds. Immutable-evidence commit
`6970f6b41ad5b1459504dab99a963482630a4b89` passed run `30189646824`, build job
`89760437385`, in `2m2s`; only final-ledger CI remains.

Final-ledger commit `281ba918582707bcfed21920fb3616120d5cd292` passed run
`30189742343`, build job `89760720303`, in `2m2s`; the fixed H1 bridge is publicly closed.

### Post-H1 rerank: H12 Levinson--Montgomery paired mass

The next omission-seeking comparison selects equations `(2.2)`--`(2.3)` in
Levinson--Montgomery's proof of Theorem 1. This does not merely restate Speiser's criterion. It
attacks the actual functional-equation-paired xi zero mass that produces the theorem's
linear-density alternative.

The first H12 campaign compiled the count objects and logical consumer before the project had
its current compensated Hadamard sum, reciprocal-square divisor mass, multiplicity-preserving
zero permutations, and H7 finite/infinite cutoff machinery. The re-entry will use those later
inputs to prove that negative paired mass at height `t` forces a left zero within `1/2`, then
turn the integer-height witnesses into the existing `N^-(T)>T/2` branch.

The Gamma remainder, low-height verification, indented contour, logarithmic count bound, full
count dichotomy, Speiser equivalence, H12, and RH remain open.

This fixed edge now compiles. The implementation uses a global half-pair average over the actual
multiplicity-bearing xi divisor, proves its compensated summability and exact rational identity,
localizes a left zero from negative mass, and derives the existing eventual `N^-(T)>T/2` count
branch from integer-height negativity. Frozen commit
`0b5b6d5c44cddb680be721c54a6fc9d261e01ba5` passed public run `30190754950`, job
`89763478543`, in `2m6s`. The atlas frontier advances to equation `(2.1)`, Gamma control, and
the low-height sign certificate; H12 and RH remain open.

Immutable-evidence commit `38071d8a6c085b74bd1f8d258cb6e83cec55d592` passed run
`30190894736`, job `89763862993`, in `1m33s`; only final-ledger CI remains for this fixed edge.

Final-ledger commit `69774e9d4d7b96590d48acd8ad5f6f9b152f0dc2` passed run
`30190977973`, job `89764077666`, in `1m47s`; the paired-mass edge is publicly closed.

### Post-paired-mass rerank: equation (2.1) and explicit Gamma control

The historical comparison selects the adjacent Levinson--Montgomery log-derivative bridge.
H1 now reaches Farmer's open moment conjecture; H7/H10 need an unconditional positivity or
number-field spectral construction; H2/H11 need an actual sparse-exception amplifier. H12 still
has a source-proved segment whose objects now exist in Lean.

The fixed campaign identifies the compiled paired reciprocal sum with `Re(xi'/xi)`, proves source
equation `(2.1)`, differentiates the compiled Stieltjes Gamma representation to obtain an
explicit digamma remainder, proves its radial norm bound, and derives
`Re(zeta'/zeta)>=0 -> I1<0` for `0<sigma<1/2, t>=10`. This feeds the compiled dense branch from
eventual integer-height witnesses.

The low-height zeta certificate, boundary signs, witness-existence alternative, indented contour,
`O(log T)` count difference, full dichotomy, Speiser equivalence, and RH remain open. This
selection does not downgrade historical breadth: every family is reranked again after the fixed
published edge closes or records an exact obstruction.

### H12 equation (2.1) and Gamma bridge local result

The fixed published edge compiles locally. Lean proves that the actual multiplicity-bearing
paired reciprocal sum equals `Re(xi'/xi)` without a residual Hadamard constant. It differentiates
the project's existing Stieltjes scaled-Gamma identity to obtain the exact digamma Stirling
formula and the explicit bound `27/(64*norm(z)^2)`, reconstructs Levinson--Montgomery equation
`(2.1)`, and proves strict negativity of its archimedean term for
`0<=sigma<=1/2, t>=10`.

Consequently, a nonnegative real zeta logarithmic derivative at a zero-free point in the open
left half-strip forces negative paired mass, and eventual integer-height witnesses feed the
already compiled `N^-(T)>T/2` branch. This result makes further optimization of the Gamma
constant a low-value task: the proved bound already closes the source sign inequality. The open
historical edge is now the low/critical boundary and interior-witness part of the indented
contour argument, followed by the `O(log T)` count comparison.

Preregistration commit `8a3c54d5092c13b8489e2c92c49d586f79176e95` passed public Lean
Action run `30191371867`, build job `89765103953`, in `1m49s`. The warning-free 615-line module,
exact TargetChecks, standard-only selected axiom prints, empty forbidden scans, and full
`8765/8765` build pass locally. Frozen implementation commit
`076b4e2023114c33fdf80cce123bc91c07d5c5a0` passed public run `30192061892`, build job
`89766933675`, in `2m14s`; the proof source is frozen. Immutable-evidence commit
`3b730f836bb61dde7cc15062015dc2fe7b33986b` passed run `30192188923`, build job
`89767296489`, in `1m53s`; only final-ledger CI remains before fixed-edge closure and fresh
cross-family ranking.

### Post-equation-(2.1) rerank: H12 vertical boundary signs

Final-ledger commit `7e745ffb509fd425a965a6eed99e49c6a070464e` passed public run
`30192288017`, build job `89767603710`, in `1m30s`; the actual paired-sum, digamma remainder,
equation `(2.1)`, archimedean sign, and mass bridge are closed.

The next omission-seeking selection is the adjacent source paragraph proving negativity on
`sigma=0` and on zero-free points of `sigma=1/2`, plus the exact logical alternative that produces
interior nonnegative-log-derivative witnesses when strict negativity is not cofinal. Mathlib's
generic Gamma differentiability away from negative integers and the project's actual paired
kernel make both vertical signs concrete Lean targets.

This is not a numerical-bound campaign. The low-height `t=10` zero certificate, critical-zero
semicircle indentation, contour admissibility, exact count equality, `O(log T)` difference,
Speiser equivalence, and RH remain open. Public preregistration CI is required before production
proof editing.

### H12 vertical boundary signs local result

The fixed endpoint compiles. GammaR calculus and equation `(2.1)` now reach both vertical
boundaries. The actual paired sum is nonpositive at `sigma=0` and zero at `sigma=1/2`, so
`Re(zeta'/zeta)<0` holds on the imaginary boundary and at every zero-free critical-boundary
point for `t>=10`.

The exact integer-height logical alternative also compiles and protects nonvanishing explicitly:
failure of cofinal strict negativity produces the eventual interior witnesses already known to
force `N^-(T)>T/2`.

Local critical-zero factorization and the strict left-pointing principal pole are now available,
but whole-semicircle indentation remains open because endpoint neighborhoods require a separate
critical-line continuity argument. The bottom `t=10` certificate, admissible top contours, exact
count equality, `O(log T)`, Speiser equivalence, and RH remain the atlas frontier. Frozen
implementation commit `d45e87b3c6ab9d41217f671b0dc96ec979167b45` passed public Lean
Action run `30193246131`, build job `89770129416`, in `2m7s`. Docs-only immutable evidence
`4c0ad75da06648c564fa58d9d29c762d46bff823` passed run `30193425500`, build job
`89770603420`, in `1m34s`; proof source remained frozen and only final-ledger CI remains.

Final-ledger commit `53f781929605243e05dcec36bb188afb1b0c50a5` passed run
`30193513376`, build job `89770844367`, in `1m51s`; the vertical-boundary and exact logical
dichotomy edge is publicly closed.

### Post-boundary-sign rerank: H12 critical-zero indentation

The next source paragraph is retained after a fresh H1/H2/H7/H10/H11/D9 comparison. Its exact
claim is strict negativity of `Re(zeta'/zeta)` on small left semicircles around critical-line
zeros. The source invokes dominance of the principal reciprocal term, but its real part vanishes
at the two endpoints, so a formal proof must expose the endpoint mechanism.

The project now has a materially new route: local xi factorization with multiplicity and
continuous residual. Functional symmetry should make the xi residual purely imaginary at the
center; after subtracting the completed-zeta factor, the zeta residual should have the strictly
negative archimedean real part already proved in Lean. If so, the entire punctured left
half-neighborhood is negative, which is stronger than the source semicircle and avoids a separate
endpoint gluing argument.

D9's actual Conrey--Li counterexample becomes the leading breadth reserve, but it first needs
certified high-height xi evaluation or universality infrastructure. The H12 bottom certificate,
top-contour admissibility, count theorem, Speiser equivalence, and RH remain open. Production
editing requires public preregistration CI.

### H12 critical-zero indentation local result

The endpoint mechanism is now kernel-checked. Xi reflection forces the local analytic zero
factor's residual logarithmic derivative to have zero real part at the critical-line center.
After exact division by the completed-zeta unit, the zeta residual is strictly negative there
and remains so nearby. Since the multiplicity pole has nonpositive real part on the closed left
side, the whole punctured left half-neighborhood and every sufficiently small closed left
semicircle are negative, endpoints included.

This closes `H12-LM-CRITICAL-INDENTATION-01` locally as
`FULL_CRITICAL_INDENTATION_SUCCESS`. Frozen implementation commit
`49d43eda415c00c10939c2df529b6231c973aa5b` passed public run `30195029807`, build job
`89774903553`, in `2m44s`; docs-only immutable-evidence commit
`482835012cba3c51839d428a41127fe40e513e2e` passed run `30195156406`, build job
`89775241280`, in `1m28s`, with proof source frozen. The next H12 source gap is global rather
than another endpoint estimate: certify the bottom contour, produce cofinal admissible tops,
and formalize the indented argument-principle count and `O(log T)` comparison. Cross-family
route selection resumes after final-ledger public closure of the fixed campaign.

### Post-H12 rerank: D9 Conrey--Li phase obstruction

The H12 local indentation is publicly closed, while its successor is now a global contour-count
package. Fresh comparison selects the older canonical de Branges obstruction before returning to
another deep open estimate.

Conrey--Li's final Sarnak remark avoids the paper's numerical witnesses. Its exact logical core is
that dense logarithmic values plus a bounded correction make a continuous phase unbounded in both
directions on a connected domain, so it crosses a phase with negative exponential real part.
The coordinate `z=i*(s-1)` then turns the xi ratio into the reciprocal shifted ratio whose
nonnegativity is necessary for the proposed positivity.

Campaign `LITERATURE-20260726-D9-CONREY-LI-PHASE-OBSTRUCTION-01` will formalize this core and an
actual-xi conditional endpoint. Actual log-zeta density, source-valid logarithm branches, the
bounded correction, and the RKHS theorem remain outside the fixed endpoint and must stay visible.

### D9 Conrey--Li phase-obstruction local result

The topology in the Sarnak sketch is valid under its explicit hypotheses. Dense complex values
give imaginary coordinates unbounded above and below; a uniformly bounded correction preserves
both tails; continuity on a preconnected domain forces the corrected phase through `pi`. The
source coordinate and reciprocal-sign step also compile exactly, including an actual
`riemannXi` conditional aggregate.

Thus the historical obstruction no longer depends logically on the paper's numerical
`t=282` witness. The precise remaining formalization package is actual log-zeta value
distribution, source-valid logarithm branches and bounded correction, followed by the RKHS
Theorem 2 bridge. This is a source-logic success, not an unconditional actual-zeta obstruction or
RH progress. Public implementation evidence remains required.

Frozen implementation commit `74787a77a20218bb967d18279b29bd7ab9a5ab97` passed public Lean
Action run `30195816933`, build job `89777044355`, in `2m6s`. Proof source is frozen; docs-only
immutable evidence and final-ledger CI remain before returning to route selection.

Docs-only immutable-evidence commit `0f8cd8437a8495bc57be0c556b74d95bc7bef623`
passed run `30195949149`, build job `89777408452`, in `1m32s`; proof source remained frozen.
Only final-ledger CI remains.

### Post-D9 rerank: H10 Bombieri--Stepanov Frobenius auxiliary

The D9 conditional phase-obstruction campaign is publicly closed. Fresh comparison gives breadth
priority to D7/H10: the project has audited the successful function-field proof's final finite
spectral implication, but not its central auxiliary-function construction.

Bombieri's source separates five steps that must not be compressed: a Frobenius-twisted source
space, a descent map with nontrivial kernel, noncancellation of the resulting auxiliary function,
perfect-power multiplicity at rational points, and a pole-degree count. Campaign
`LITERATURE-20260726-H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01` fixes the finite-field
algebra and multiplicity budget, plus a saturated `ZMod 2` witness. Curve-level Riemann--Roch and
number-field transfer remain outside.

### H10 Frobenius auxiliary local result

The source algebra is now kernel-checked. Finite characteristic-power expansion, rational-point
descent, perfect-power root multiplicity, and the multiplicity-weighted degree budget all compile
with the nonzero-base requirement visible. A nonzero `ZMod 2` kernel witness has exact
multiplicity `2` at both rational points and saturates the degree bound.

This sharp example reranks the remaining H10 door. Further optimization of the bare
Frobenius/root-count inequality has no universal room; the omission audit should move upstream
to the source's Riemann--Roch dimension balance, polar/tensor injectivity, nonzero optimized
kernel, and pole divisor, then separately examine whether any number-field structure can replace
finite Frobenius. This is `KNOWN_FUNCTION_FIELD_MECHANISM_FORMALIZED`, not a curve theorem,
number-field transfer, or RH progress.

Frozen implementation commit `61bb73ad666e3bdd4ba460bedd93af16256c997d` passed public run
`30205411443`, build job `89802493185`, in `2m31s`. Docs-only immutable evidence is next.

Docs-only immutable evidence `89b7dead3b9a9344dc34c16a1d9e0bfa0c2cd792` passed run
`30205553507`, build job `89802869900`, in `1m30s`; proof source remained frozen. Only
final-ledger CI remains.

Final-ledger commit `b23d601ee8c69a654d542f1da43d16bb042eaf22` passed run
`30205670028`, build job `89803179330`, in `1m30s`; the fixed source-algebra endpoint is
publicly closed.

### Post-H10-D rerank: polar injectivity before dimension surplus

The next H10 source hinge is selected after comparison with the current H1, H2, H7, H11, and H12
frontiers. Bombieri's nonzero auxiliary does not follow from a dimension inequality alone. The
polar-order lemma first identifies the product source with a tensor product, preventing a
nonzero coefficient vector from realizing as the zero function.

The fixed campaign kernel-checks this dependency with an injective coefficient-block model and a
noninjective countermodel. It is an omission audit of a lightly stated source lemma, not a
point-count optimization. The actual curve valuation proof and all number-field transfer remain
outside.

### H10 polar-injectivity local result

The logical gate is now kernel-checked. Strict source-target finrank surplus gives a nonzero
descent kernel, and injective realization preserves nonzeroness. A coefficient-block linear
equivalence supplies an exact finite model of polar separation. Conversely, a two-dimensional
first-projection example has a nonzero descent kernel whose entire realization is zero.

Therefore no dimension-only shortcut is available at this layer; the source's noncancellation
lemma is necessary. A future omission claim must concern the actual curve valuation argument or a
new number-field source/descent structure, not this finite-dimensional inference. This is
`SOURCE_NONCANCELLATION_GATE_FORMALIZED`, with no RH-frontier change.

Frozen implementation commit `011ce4d16bb565d03059ae220e9ad1996e6ec7cb` passed public run
`30206491939`, build job `89805380158`, in `2m25s`. Docs-only immutable evidence is next.

Docs-only immutable evidence `66071f7a4cb4685be1434f8b28558c209a004f78` passed run
`30206663217`, build job `89805830462`, in `1m35s`; proof source remained frozen. Only
final-ledger CI remains.

Final-ledger commit `76c21bb536ad205b53eb8aee2035c2529e32eb96` passed run
`30206809306`, build job `89806209072`, in `1m33s`; H10-E is publicly closed.

### Post-H10 rerank: H9 Redheffer--Mertens determinant

Fresh cross-family ranking selects a historical H9 branch absent from the initial atlas. The
Redheffer matrix converts the summatory Mobius function into an exact determinant by a source
specified integer row elimination. Vaughan, Barrett--Jarvis, and Vaughan II then study the
characteristic polynomial, two dominant roots, and the remaining roots near one. This is an
arithmetic-spectral route distinct from the false pointwise Mertens conjecture and from merely
listing the RH-equivalent summatory bound.

The first fixed campaign compiles the exact eliminator, product shape, unit complementary
determinant, `det A_n=M(n)`, determinant-zero criteria, and low-order checks. It does not assume
or prove `M(n)=O(n^(1/2+epsilon))`, and determinant product control alone does not locate
individual eigenvalues. The next omission-bearing layer, if the source identity survives, is
the factorization of the characteristic polynomial and the quantitative control of its
logarithmically many non-unit roots.

The fixed elimination survives exactly. Lean checks the positive-index divisor bijection,
Vaughan's determinant-one first-row transform, total nonfirst-row cancellation, the unit
successor divisibility determinant, and `det A_N=M(N)` for all positive orders. Exact orders one
through four rule out the transpose and `(1,1)` double-count errors. The result does not improve
the Mertens bound; it confirms that the source's possible extra leverage begins only with the
characteristic polynomial and joint control of the non-unit roots.

One proven Target, eight exact TargetChecks, six standard-only axiom prints, empty forbidden
scans, and full `8771/8771` build pass locally. Frozen implementation commit
`2003f912dfb0627b1c41d4b80db1abc6eb24e5d3` passed public Lean Action run `30207909320`,
build job `89809080863`, in `2m6s`. Proof source is frozen; docs-only immutable evidence is the
next gate before successor selection.

Docs-only immutable-evidence commit `ad5444b8948eab6ac2cf2dd60f0a0e2fb7f85975` passed run
`30208079452`, build job `89809518957`, in `1m29s`, with no `LeanLab/` change from the frozen
implementation. Only final-ledger CI remains before fixed-edge closure and fresh route selection.

Final-ledger commit `6dfb8689243824598d865c911f64c46a0dc8de18` passed run
`30208188470`, build job `89809811907`, in `1m37s`; the determinant endpoint is publicly closed.

### Post-determinant rerank: Redheffer characteristic polynomial

Fresh comparison does not continue H9 merely from implementation momentum. H1's arbitrary-length
moment, H2/H11's sparse-exception amplifier, H7's true spectral convergence, H8's actual all-index
control, and H12's global count assembly all require new global inputs. Vaughan equations
`(7)`--`(12)` instead give an exact unformalized structural edge that decides whether only
`Nat.log 2 N+1` roots genuinely carry the determinant product.

Campaign `LITERATURE-20260726-H9-REDHEFFER-CHARPOLY-01` fixes ordered-factor counts, their
minimal-product support, a denominator-free polynomial eliminator, the generic characteristic
polynomial, exact algebraic multiplicity of eigenvalue one, and low-order sign checks. Dominant
and remaining-root location, Mertens growth, H9, and RH remain outside.

The fixed edge compiles locally. The ordered counts vanish below `2^k`, so only depths through
`floor(log_2 N)` enter; a power-of-two witness makes the top depth nonzero. A polynomial
first-row eliminator clears every denominator before multiplication and yields the exact source
factorization over `Z[X]`. For `N>=2`, precisely `N-floor(log_2 N)-1` roots are one, counted
algebraically.

The audit also finds a small but genuine source boundary: at `N=1`, the matrix is `[1]` and the
unit root has multiplicity one, not the zero returned by the unrestricted displayed formula.
Lean therefore states and checks the order-one case separately. This correction does not touch
the spectral frontier. The remaining `floor(log_2 N)+1` roots are algebraically isolated as a
factor, but no location, separation, or joint-product estimate for them follows.

The 725-line module, one proven Target, eight exact checks, seven standard-only axiom prints,
empty forbidden scans, and full `8772/8772` build pass locally. Classification:
`REDHEFFER_CHARACTERISTIC_POLYNOMIAL_FORMALIZED`; spectral compression and source-boundary
coverage increase, while Mertens growth, the hard gap, and the RH frontier do not.

Frozen implementation commit `4fbad00c4c24c8a5ae9b9885b0a23da82744665b` passed public Lean
Action run `30209691871`, build job `89813735900`, in `2m24s`. Proof source is frozen while
docs-only immutable evidence remains.

Docs-only immutable-evidence commit `ada5bb11085378fb8c1def1e3e9924a4a6b672a9` passed run
`30209857664`, build job `89814144474`, in `1m47s`, with no `LeanLab/` change from the frozen
implementation. Only final-ledger CI remains.

Final-ledger commit `2799ec66850919db744026ae58aaea4c2bd2f769` passed run
`30210035283`, build job `89814585909`, in `1m37s`; the exact characteristic-polynomial
endpoint is publicly closed.

### Post-Redheffer rerank: Riesz exponential smoothing

Fresh comparison retains the Redheffer non-unit roots, H1 arbitrary-length moments, H2 actual
bow exclusion, H7 ground-state convergence, H8 all-index hyperbolicity, H10 geometric transfer,
H11 sparse-exception amplification, and H12 global counting as open. It does not choose another
Redheffer estimate from local momentum.

The missing classical H9 branch is Riesz's 1916 exponential smoothing:

```text
P_2(x)=sum mu(n)n^-2 exp(-x/n^2).
```

Its RH-equivalent decay is explicit and remains unproved. The selected first edge instead audits
the Mellin bridge. Agarwal--Garg--Maji 2022 state the ordinary transform on a region including
`Re(s)>=0`, but `P_2(0)=1/zeta(2)!=0`; therefore the zero endpoint forces divergence there.
The source proof itself first derives the literal identity for `Re(s)<0` and then invokes
analytic continuation.

Campaign `LITERATURE-20260726-H9-RIESZ-MELLIN-BOUNDARY-01` will compile the actual kernel,
the exact literal strip `-1/2<Re(s)<0`, a divergence witness at source parameter `s=1/2`, and
the conditional Mellin holomorphy supplied by an explicit power-decay assumption. The Riesz
decay, continuation of the product identity into the enlarged strip, zero exclusion, and RH
remain outside. Production editing is closed until docs-only preregistration passes public CI.

### Riesz Mellin boundary local result

The preregistration passed public CI, and the 490-line implementation compiles the entire fixed
endpoint. The actual kernel is continuous on `[0,infinity)`, has
`P_2(0)=1/zeta(2)!=0`, and satisfies `P_2(x)=O(x^-a)` for every `0<=a<1/2`.
Consequently the ordinary Mellin integral converges and gives
`zeta(2*s+2) M[P_2](-s)=Gamma(-s)` on exactly the audited base strip
`-1/2<Re(s)<0`.

Lean also proves nonconvergence at Mellin argument `-1/2`, corresponding to the source's
displayed parameter `s=1/2`. This closes the literal-versus-continuation audit but does not
refute the Riesz criterion: continuation may start from the corrected base strip. The open
route edges are the RH-equivalent `x^(-3/4+epsilon)` decay and a rigorous continuation/zero-free
consumer. Local classification is source-domain and historical-coverage progress with
`rh_frontier_delta=0`.

Frozen implementation commit `096aea939d27fb6828b702296c156bbef4ba1559` passed public Lean
Action run `30212146718`, build job `89820083261`, in `2m25s`. Proof source is frozen; the
next gate is docs-only immutable evidence.

Docs-only immutable-evidence commit `5448bd74cdf55a8ead8847f6c7cd50e21e8711e7` passed run
`30212403937`, build job `89820745802`, in `1m39s`, with no `LeanLab/` change from the frozen
implementation. Only final-ledger CI remains.

### Post-Hardy rerank: Farey--Franel--Landau arithmetic transform

The Hardy real-coordinate/sign-consumer endpoint is publicly closed at final ledger
`24567b9a7bd2baae902c83ffbb1b2281a676a074`. Fresh comparison retains Hardy's original
transform, Riesz decay, Redheffer estimates, H2 density, H7 spectral convergence, H10
function-field transfer, H11 pair correlation, and H12 Speiser as live branches.

Farey is selected because it is a canonical historical RH-equivalent branch still absent from
production Lean. Kanemitsu--Yoshimoto Lemma 3 exposes a bounded exact entry: a reduced positive
Farey test sum equals complete numerator-block sums weighted by `M(floor(N/n))`. The
frequency-one exponential specialization collapses exactly to `M(N)`.

Campaign `LITERATURE-20260726-H9-FAREY-MOBIUS-WEYL-01` freezes source endpoint conventions,
reduced-value uniqueness, totient cardinality, the arbitrary-test transform, and the
frequency-one specialization. It does not prove ordering, discrepancy decay, Mertens growth,
H9, or RH. Production editing remains closed until docs-only preregistration passes public CI.

### Farey--Mobius--Weyl transform local result

The preregistration passed public CI, and the 579-line implementation compiles the entire fixed
endpoint. The key omission-sensitive step is a proved finite bijection: every complete numerator
`a/q` maps to its unique reduced pair
`(q/gcd(a,q),a/gcd(a,q))`, and the inverse reconstructs the original numerator. Thus no
duplicate or endpoint convention is hidden in the Mobius inversion.

Lean then proves the actual arbitrary-test Farey sum equals complete blocks weighted by
`M(floor(N/n))`. The frequency-one specialization gives primitive block `mu(q)` and total
`M(N)`. This closes the exact arithmetic entry only. Ordered Franel discrepancy, its squared
error identity, every asymptotic estimate, Mertens growth, H9, and RH remain open.

Frozen implementation commit `10bbaa1825bac871d5664322f85ab04f6668ec20` passed public Lean
Action run `30214982286`, build job `89827558524`, in `2m7s`. Proof source is frozen while
docs-only immutable evidence is published.

Docs-only immutable-evidence commit `c0190936358edf63ebec0588e6fdec4ac0c88ed6` passed run
`30215145080`, build job `89827979109`, in `1m53s`, with no `LeanLab/` change from the frozen
implementation. Only final-ledger CI remains.

Final-ledger commit `8a84e18a30e95bf1be423a949438deb0fdfafabb` passed run
`30215281290`, build job `89828323462`, in `1m35s`; the finite Farey transform endpoint is
publicly closed and cross-family selection resumed.

### Post-Farey rerank: H11 triangular pair mass

Fresh comparison does not continue to ordered Franel discrepancy by inertia. Hardy's transform,
mollifier moments, H7 spectral convergence, H10 transfer, H11 statistics, H12 global counting,
and direct actual-zeta attacks remain live.

H11 is selected because the project has compiled horizontal multiplicity but not the exact
Gallagher--Mueller mechanism that inserts it into the pair-correlation second moment.
Goldston--Lee--Schettler--Suriajaya equations `(5.3)`--`(5.4)` split the triangular mass of all
ordered ordinate pairs into `U*N*(T)` and twice the integral of the strict positive-gap count.

Campaign `LITERATURE-20260728-H11-TRIANGULAR-PAIR-MASS-01` freezes that finite identity, its
actual interval-integral proof, exact agreement with project `horizontalPairCount`, and the
analytic-multiplicity-preserving positive zeta-zero cutoff instance. Fujii's second-moment
estimate, the moving-height `O(L^2)` boundary, PCC, HMH, sparse-exception amplification, and RH
remain outside. Production editing is closed until docs-only preregistration passes public CI.

### H11 triangular pair mass: implementation result

The finite source mechanism is now fully compiler-checked. Implementation
`15381a49ff4dfb92a0ab4e29d5e76383f9789139` passed public run `30333046948`, build job
`90192073198`, in `2m11s`. The exact actual-zeta identity contains
`U * pccPositiveZetaHorizontalPairCount T`; all remaining terms are the integral of strict
positive short-gap counts.

This closes a historical interface, not the analytic pair-correlation route. No omitted factor,
endpoint convention, or multiplicity mismatch was found. The omission search now has a sharper
target: inspect Fujii/Gallagher--Mueller/PCC error terms for any absolute, local, or
last-exception-sensitive control that was discarded when the literature normalized by the total
zero count. Without such control, the already compiled persistent sparse-exception model remains
compatible with density-one conclusions.

Immutable evidence `b6f34cbfef5790fa9e94b338d828fe1b79d37369` passed public run
`30333303052`, job `90192852899`, in `1m40s`, with no proof-source change. H11 triangular mass
therefore leaves the active shortlist at a local stop; its Fujii/PCC and sparse-exception nodes
stay open, but the next campaign must be chosen by a fresh cross-family comparison.

### Post-H11 rerank: Hardy's original Abel moment mechanism

H11 triangular mass is publicly closed at final ledger
`650bd2656b71c4a25a830d77ef49971eb8af1fc4`. Fresh comparison retains its moving-height and
sparse-exception edges, H1's arbitrary mollifier moment, H2 localization, H7 convergence, H9
ordered Franel discrepancy, H10 geometric transfer, and H12 global counting as open.

Hardy's original 1914 proof is selected because the repository has only its real-xi sign
consumer. The source actually proceeds through Cahen-Mellin/theta inversion, an interior
exponential parameter `|alpha|<pi/2`, alternating Abel limits of even moments, and a
`2^(2p)` amplification contradiction. The later Hardy-`Z` signed-integral proof is a different
route and must not be substituted silently.

The audit finds an omission-sensitive boundary: Hardy writes a boundary integral at
`alpha=pi/2` only after invoking a convergence theorem under the assumed eventual sign. The new
campaign keeps the one-sided Abel limit explicit and proves the contradiction using interior
parameters, so it does not assume unconditional boundary integrability.

Campaign `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01` also fixes the exact cross-route identity
`hardyXi(2*t)=8*deBruijnNewmanH 0 (4*t)`. Its full endpoint is the actual infinite-critical-zero
consumer conditional on Hardy's source Abel moment law. The law itself, quantitative counts,
H1, and RH remain open. Production Lean editing is blocked until the docs-only preregistration
passes public CI.

### Hardy Abel moment: local implementation result

The public preregistration gate passed at `03a788e80e6ca0acfb82a41c8e3663bda3a9ef79`, run
`30334772898`, job `90197213274`, in `1m38s`. The full fixed conditional endpoint now compiles
locally. No omitted factor or parity reversal was found: odd moments eliminate an eventually
positive tail, even moments eliminate an eventually negative tail, and the source ratio is
exactly the growth gap between `T^(2p)` and `(2T)^(2p)`.

The omission-sensitive boundary remains real and localized. The contradiction needs only
interior moments selected by the left Abel limit; it does not need an unconditional boundary
Lebesgue integral. The next historical-source question is therefore whether Hardy's
Cahen-Mellin/theta derivation can be compiled into `HardyXiAbelMomentLaw` without importing a
stronger convergence premise. Until then, the zero-infinitude result is conditional and does
not move H1 or RH.
