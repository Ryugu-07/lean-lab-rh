# D9 Suzuki Reciprocal-Log-Derivative Limit Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-D9-SUZUKI-RECIPROCAL-LIMIT-01`

Selected node: `D9-SUZUKI-RECIPROCAL-LIMIT-REGULARITY-01`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

Preregistration commit `b455391bf7211e0136a98b082f1264fee4cac1ca` passed public Lean Action
run `29952313617`, build job `89032753680`, in `1m54s`. Proof-source editing began only after this
gate passed.

## Selection reason

The H8 Jensen generic quantifier campaign is publicly closed at final-ledger commit
`c80b9e6a4114d7d591f4db72e6326810d0fe9d1c`, Lean Action run `29951256366`, build job
`89029220136`, in `1m53s`. Actual-xi all-index hyperbolicity remains open.

Fresh breadth selection compared D4 density, D7 function-field transfer, D9 de Branges/canonical
systems, and D11 automorphic/Iwasawa stress tests. D4 still lacks a last-exception localizer, D7's
finite spectral rigidity is already compiled, and D11 presently supplies robustness tests rather
than an individual-zeta transfer. D9 has a source-backed obstruction card but no theorem-producing
campaign. A June 2026 primary source now gives D9 a sharper finite-to-infinite proposal than the
atlas recorded, so its exact regularity boundary has the highest current omission-audit value.

## Locked primary sources

1. Masatoshi Suzuki, "Weil's quadratic form via the screw function," arXiv:2606.09096v1,
   especially Theorem 5, Corollary 6, and Sections 7--8.
   <https://arxiv.org/abs/2606.09096v1>
2. Masatoshi Suzuki, "Aspects of the screw function corresponding to the Riemann zeta function,"
   Journal of the London Mathematical Society 108 (2023), arXiv:2206.03682.
   <https://arxiv.org/abs/2206.03682>
3. Masatoshi Suzuki, "On the Hilbert space derived from the Weil distribution," Canadian Journal
   of Mathematics, arXiv:2301.00421.
   <https://arxiv.org/abs/2301.00421>
4. J. Brian Conrey and Xian-Jin Li, "A note on some positivity conditions related to zeta- and
   L-functions," arXiv:math/9812166.
   <https://arxiv.org/abs/math/9812166>

The first source is the statement under direct audit. The earlier sources fix the screw-function,
de Branges, and historical positivity context; none is imported as an unproved premise.

## Exact source edge

Suzuki proves unconditionally that, for every finite interval parameter `a > 0` and boundary
parameter `theta`, the entire characteristic function `W(a, theta; z)` has only real zeros. The
paper then states that if finite-valued normalizations `exp(phi(a,z)) W(a,theta(a);z)` converge
uniformly on every compact subset of `C` to

`z^2 * xi(1/2-i*z) / xi'(1/2-i*z)`,

then RH follows. The paper does not state a holomorphy or continuity hypothesis on `phi` in the
displayed corollary. Its heuristic section assumes RH and motivates, but does not prove, the limit.

This creates two distinct interpretation tests:

1. Under the literal finite-valued reading, multiplication by `exp(phi)` preserves zeros, but
   zero-reality is not stable under compact-uniform convergence unless the normalized functions
   have sufficient analytic regularity.
2. Under the natural repair that the normalized functions are entire, their compact-uniform limit
   must be entire. A reciprocal logarithmic derivative can instead have a nonremovable pole where
   the derivative vanishes but the original function does not. The factor `z^2` can cancel the
   central symmetry critical point, but not a generic nonzero one.

If the intended topology is meromorphic convergence on compacta avoiding poles, it must be stated
separately; ordinary entire-function Hurwitz transfer cannot then be applied across the omitted
poles without an additional argument.

## Fixed Lean endpoint

Create `LeanLab/Riemann/SuzukiReciprocalLogDerivativeAudit.lean` and compile all of the following
without placeholders:

1. Define a root predicate for complex-valued functions and the target `z - I`.
2. Define a nowhere-zero punctured approximation equal to `z-I` away from `I` and equal to
   `1/(n+1)` at `I`.
3. Prove the punctured approximations converge uniformly on every set, hence on every compact set,
   to `z-I`, while every approximation is zero-free and the target has the nonreal zero `I`.
4. Put the sequence into the source-shaped form `exp(phi_n(z)) * W_n(z)` with `W_n=1` and
   `phi_n=log(puncturedApproximation_n)`, and falsify the generic finite-normalization
   zero-persistence schema lacking regularity of `phi`.
5. Define the symmetric real-rooted quartic
   `(z^2-(1/5)^2)*(z^2-(7/5)^2)` and its complex derivative `4*z^3-4*z`; prove the derivative
   identity and that every zero of the quartic is real.
6. At `z=1`, prove the derivative is zero while the quartic and `z^2` are nonzero. Deduce that no
   finite-valued function `F` can satisfy
   `quarticDerivative(z) * F(z) = z^2 * quartic(z)` for every `z`.
7. Combine both witnesses in one aggregate route-audit theorem.

Proposed declaration names:

- `suzukiAuditHasOnlyRealZeros`
- `suzukiAuditPuncturedApproximation`
- `suzukiAuditPuncturedApproximation_tendstoUniformlyOn`
- `suzukiAuditFiniteNormalizationZeroPersistenceSchema`
- `not_suzukiAuditFiniteNormalizationZeroPersistenceSchema`
- `suzukiAuditQuartic`
- `suzukiAuditQuarticDerivative`
- `suzukiAuditQuartic_hasOnlyRealZeros`
- `not_exists_suzukiAuditQuartic_reciprocalLogDerivativeExtension`
- `suzukiReciprocalLogDerivativeAudit_endpoint`

Names may change to fit the complex-analysis API, but neither the all-set uniform convergence nor
the nonzero off-center critical-point obstruction may be weakened silently.

## Success and falsification criteria

`FULL_SUCCESS` requires both exact countermodels, source-shaped exponential normalization, exact
Targets and TargetChecks, selected standard-only axiom prints, an empty forbidden scan, full build,
and independent public CI.

`MEANINGFUL_PARTIAL` requires one complete countermodel plus the first exact Lean API obstruction
to the other, without changing the source interpretation.

`SOURCE_FALSIFIED` requires a contradiction for Suzuki's actual `W(a,theta;z)` and xi target under
fully specified source hypotheses. The registered generic models do not seek or claim this.

## Claim boundary

- The punctured sequence is deliberately noncontinuous at one point. It proves that finite-valued
  exponential normalization plus uniform convergence is insufficient without regularity; it is
  not a model of the source's operator-built `W`.
- The quartic is a symmetric all-real-zero model, not the Riemann xi function. It proves that the
  reciprocal-log-derivative target need not possess a finite entire extension away from the
  central symmetry point.
- No actual nonzero critical point of xi is asserted until Lean proves it or it enters as an
  explicit conditional hypothesis.
- The source corollary may admit a repaired meromorphic interpretation. Such a repair changes the
  topology and requires a new zero-transfer proof; it is not silently assumed here.
- This campaign does not refute de Branges theory, Suzuki's unconditional finite-interval
  self-adjointness theorem, or RH.

## Mechanical gates

Before proof-source editing:

- publish this preregistration and require public Lean Action CI;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register exact Targets and TargetChecks;
- print selected transitive axioms;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- run `git diff --check`, the module build, full build, and public CI;
- record literal, holomorphic, and meromorphic source interpretations separately.

## Stop and successor rule

Stop this local campaign at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL` at an exact API obstruction,
`SOURCE_FALSIFIED`, or proof that the endpoint already exists in the project. Local stop returns
the persistent RH Goal to the unfinished historical atlas. D9 remains open unless the actual
finite-interval operator limit is proved or mathematically ruled out. Original conjecture and
direct RH attempts remain open throughout.
