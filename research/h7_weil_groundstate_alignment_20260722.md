# H7 Finite-Prime Weil Ground-State M0 Alignment

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01`

Status: `IMPLEMENTATION_PUBLIC_CI_PASSED / EVIDENCE_COMMIT_PENDING`

Classification:
`MEANINGFUL_PARTIAL / WEIGHTED_COORDINATE_ALIGNMENT_COMPILED /
SOURCE_PROJECT_DOMAIN_GAP_EXPOSED`

This record compares the 2025-2026 finite-prime Weil ground-state construction with the
project's compact additive Weil API. Shared terminology is not treated as equality. A source
identity is recorded as source-only unless the project already has the corresponding object or a
new Lean theorem proves the coordinate bridge.

## Source pins

- `SRC-CONNES-VANSUIJLEKOM-2025`, arXiv:2511.23257: real-zero theorem for a lower-bounded form
  with a simple isolated even ground state.
- `SRC-CONNES-CONSANI-MOSCOVICI-2025`, arXiv:2511.22755: equations `mhat`, `MF1`,
  `bombieriexplicit1bis`, `bombtest`, `bombtest-0`, `toa`, `weilQexp`, `quadratsemi`, `vN`,
  `weilformbase`, `hh`, `bomp`, `weinfty`, and Theorem `finmain`.
- `SRC-CONNES-2026`, arXiv:2602.04022: Fact 6.4 and Section 6.6.
- `SRC-GROSKIN-2026-DICTIONARY`, arXiv:2607.02828: Definitions 2.1-2.4 and Theorem 2.5.
- `SRC-GROSKIN-2026-HIGHPREC`, arXiv:2605.20224: normalization and numerical navigation only.

## Compiled bridge

The module `LeanLab/Riemann/WeilGroundStateAlignment.lean` defines

```text
g(x) = exp(-x/2) f(x + L/2)
```

and compiles these exact statements:

- `compactLaplaceConjInvolution_weilGroundStateLogRoot`;
- `compactLaplaceAutocorrelation_weilGroundStateLogRoot`;
- `compactLaplaceTransform_weilGroundStateLogRoot_criticalLine`;
- `compactLaplaceTransform_weilGroundStateLogRoot_sourceCoordinate`;
- `compactLaplaceTransform_weilGroundStateLogRoot_zero_sourceMoment`;
- `compactLaplaceTransform_weilGroundStateLogRoot_one_sourceMoment`.

The source Fourier convention is negative:

```text
hat f(z) = integral exp(-i*z*x) f(x + L/2) dx.
```

Consequently the source ordinate `z` maps to the project Laplace parameter
`s = 1/2 - i*z`. The project parameter `1/2 + i*z` gives the source value at `-z`.
Even source vectors make the two zero sets agree, but the sign correction is part of M0 and is
not inferred from evenness.

## Fourteen-row inventory

| no. | object | source formula/evidence | project or Lean evidence | classification | verdict |
| --- | --- | --- | --- | --- | --- |
| 1 | support and cutoff parameters | arXiv:2511.22755 Proposition `toadd` fixes `lambda > 1` and `L = 2 log lambda`; `quadratsemi` and `bomp` retain prime powers `n <= lambda^2 = exp L`. arXiv:2607.02828 writes `c = exp L`, `Delta = L/(2*pi)`, and `rho = 2*pi/L`. | The compact explicit formula uses a separate vertical contour parameter named `c`, for example in `symmetrizedCompactLaplaceXi_arithmetic_explicit_formula`; it is not a prime cutoff. | `EXACT` | Source parameter identities agree after the rename `c_prime = lambda^2`. The project's contour `c` is a distinct variable and is never identified with `c_prime`. |
| 2 | Hilbert and test-function domains | arXiv:2511.22755 uses `L^2([0,L],dx)`, its isometric image `L^2([lambda^-1,lambda],du/u)`, a lower-semicontinuous form closure, and piecewise-smooth compactly supported functions in the form domain. | `compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic` and the criterion require a root `g : R -> C` with `ContDiff R infinity g` and `HasCompactSupport g`. | `PROJECT_GAP` | A generic trigonometric polynomial on `[0,L]`, extended by zero, has endpoint jumps or derivative jumps and is not `C infinity` on `R`. The weighted conjugacy does not repair those endpoint jets. The source finite space therefore cannot directly instantiate the current project criterion. |
| 3 | Fourier bases, parity, and coefficient normalization | arXiv:2511.22755 defines `U_n = L^-1/2 exp(2*pi*i*n*x/L)`, `V_n = kappa(U_n)`, and `E_N = span{V_k : abs k <= N}`. arXiv:2607.02828 uses real even coordinates with `u_0=v_0` and `u_(+/-k)=v_k/sqrt 2`. | No project declaration defines this Galerkin basis, even coefficient space, or coefficient isometry. | `SOURCE_ONLY` | The finite basis and normalization are exact source data but are not yet formalized in Lean. |
| 4 | weighted centered root | Proposition `toadd` centers with `x = log u`, while `MF1` supplies the Mellin half-density. Combined, the source-to-project root is `g(x)=exp(-x/2) f(x+L/2)`. | `weilGroundStateLogRoot` is this definition. | `EXACT_AFTER_NAMED_CONJUGACY` | The coordinate map is now a named project definition; no support or regularity assertion is added. |
| 5 | star and autocorrelation | The source additive star is `f*(y)=conj(f(-y))`; `QW(f,g)=Psi(f* * g)`. After centering, the source autocorrelation is `integral f(y+L/2) conj(f(y-x+L/2)) dy`. | `compactLaplaceConjInvolution g x = exp(-x) conj(g(-x))` and `compactLaplaceAutocorrelation` are the project objects. The two compiled bridge theorems identify them with the source expressions times `exp(-x/2)`. | `EXACT_AFTER_NAMED_CONJUGACY` | The weighted project involution is exactly the ordinary source star conjugated by the Mellin half-density. |
| 6 | Fourier/Mellin convention and zero coordinate | Source equation `mhat` is `hat F(z)=integral F(u)u^(-i*z)du/u`. With `x=log u`, this is the negative-sign centered Fourier transform. | `compactLaplaceTransform_weilGroundStateLogRoot_sourceCoordinate` proves `L_g(1/2-i*z)=hat f(z)`. The positive-sign theorem separately proves `L_g(1/2+i*z)=hat f(-z)`. | `EXACT_AFTER_NAMED_CONJUGACY` | The sign-reflected coordinate is compiled explicitly. No unrecorded `z -> -z` convention remains. |
| 7 | pole block and endpoint moments | Source equation `bombtest-0` is `W_(0,2)(F)=hat F(i/2)+hat F(-i/2)`; `quadratsemi` gives the polarized rank-two term. | The endpoint theorems prove `L_g(0)=hat f(-i/2)` and `L_g(1)=hat f(i/2)`. However, `compactWeilArithmeticQuadratic` contains only archimedean minus prime terms, and `compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic` applies after both endpoint values vanish. | `PROJECT_GAP` | The two moments align exactly, but the named project quadratic is the pole-free constrained expression, not the source's unrestricted full form. Equality of the full forms is not claimed. |
| 8 | prime powers, signs, and cutoff | Source `bombieriexplicit1bis`, `quadratsemi`, and `bomp` give a negative prime contribution with weights `Lambda(q)/sqrt(q)` for `1 < q <= exp L`, including both multiplicative directions through the autocorrelation. | `compactSymmetrizedVonMangoldtWeight` and the `tsum` in `compactWeilArithmeticQuadratic` encode the complete project prime side; compact support later makes terms vanish. No theorem currently transports the finite source coefficient formula to these declarations. | `SOURCE_ONLY` | The source finite prime block is pinned exactly. Term-by-term project equality remains blocked by the test-class gap and has not been asserted from matching notation. |
| 9 | archimedean block and `2*pi` normalization | Source `thetaprime` uses `2 theta'(t)/(2*pi)`; `bombtestR` and `weinfty` give the equivalent physical-side density, with the digamma expressions in Proposition `computearch`. | `compactSymmetrizedXiArchimedeanIntegral` is the project's complete archimedean term, and the compact explicit formula has overall zero-side factor `pi`. No compiled theorem identifies the source finite matrix's digamma entries with this project integral after the H7 conjugacy. | `SOURCE_ONLY` | Both normalizations are now separately pinned. A remaining `2*pi` factor is not guessed away; exact cross-evaluation awaits a source-class extension or a direct finite-matrix formalization. |
| 10 | divisor side, multiplicity, and convergence | arXiv:2511.22755 states that convolution squares give absolute convergence over zeros. arXiv:2607.02828 Theorem 2.5 gives `v^T Q_infinity v = sum_rho g_v(rho)` with zeros counted with multiplicity. | `RiemannXiDivisorZeroIndex`, `riemannXiDivisorZeroValue`, `compactWeilZeroQuadratic`, and `compactWeilZeroQuadratic_eq_rawZeroQuadratic` provide a multiplicity-bearing absolutely summable project zero side for smooth compact autocorrelations. | `PROJECT_GAP` | Multiplicity and the intended zero side agree structurally. The finite source test `g_v` has not been shown to inhabit the project's smooth compact root class, so no project equality theorem is claimed. |
| 11 | finite divided-difference matrix | arXiv:2511.22755 Lemma `polarize0` and Sections 6-8 give off-diagonal divided differences and derivative-valued diagonal entries for the pole, prime, and archimedean blocks. | No Lean matrix declaration or diagonal-limit theorem exists for this H7 form. | `SOURCE_ONLY` | The exact finite matrix remains a separate formalization target; numerical implementations are navigation evidence only. |
| 12 | finite Guinand-Weil dictionary direction | arXiv:2607.02828 defines `T_v`, its convolution kernel `K_v`, and `hat g_v(xi)=pi K_v(1-abs(xi)/Delta)` on its compact support, then proves the finite quadratic/zero-sum identity. The paper states only the vector-to-test direction. | The project has generic compact test functions and a divisor formula but no inverse from admissible tests to finite vectors and no density theorem for these `g_v`. | `SOURCE_ONLY` | The July 2026 result materially closes a source-level finite dictionary, including the diagonal, but it supplies neither an inverse nor density in the complete Weil class. |
| 13 | closed form, operator, and ground-state hypotheses | arXiv:2511.22755 proves lower boundedness, lower semicontinuity, form-core approximation, compact resolvent for the associated operator, and existence of a lowest eigenfunction. The finite real-zero theorem assumes the lowest eigenvalue is simple and its eigenvector even; arXiv:2511.23257 requires the corresponding simple isolated even ground state. | The project currently defines neither the H7 closed quadratic form nor its selfadjoint operator, resolvent, parity decomposition, or spectral projections. | `PROJECT_GAP` | Source operator results are not project premises. Simplicity and evenness remain assumptions, not consequences of finite numerics or the compiled coordinate bridge. |
| 14 | three limits | Source form-core results address `N -> infinity` at fixed `lambda`. Connes 2026 Fact 6.4, also arXiv:2511.22755 Lemma `hermfact1`, proves the explicit prolate approximants `k_lambda` converge in Fourier transform to `Xi` uniformly on closed substrips of `abs(Im z)<1/2`. Section 6.6 leaves the true ground-state comparison `xi_lambda` versus a scalar multiple of `k_lambda` open. | No project declaration formalizes any of these H7 limits. | `SOURCE_ONLY` | The previously coarse phrase "ground-state transforms converge to Xi" is corrected. The proved `k_lambda -> Xi` limit does not include the actual lowest eigenvector; the open comparison is the RH-bearing bridge. |

## Exact obstruction

`OBS-H7-WEIL-ALIGN-REGULARITY-01`:

The finite source space consists of trigonometric functions on a closed interval and their
compactly supported multiplicative images. Generic zero extensions are only piecewise smooth at
the support endpoints. The current project criterion is stated for globally `C infinity`
compact roots. Therefore the compiled weighted coordinate map proves the algebraic and transform
identities, but it does not make a source Galerkin vector admissible for
`compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic`.

Smoothing is not an equality repair: it changes the finite matrix, the endpoint moments, and the
ground state. A valid repair must instead extend the project formula to the source form domain or
formalize the source finite form directly and later prove a closure theorem.

## Outcome and next route decision

- `rh_frontier_delta=0`.
- `hard_gap_delta=0`.
- `route_infrastructure_delta=1`.
- `obstruction_map_delta=1`.
- Algebraic M0 rows 4-6 are compiled, including the previously unrecorded Fourier sign.
- The full source/project form equality is not proved because rows 2, 7, 10, and 13 expose an
  exact domain/pole/operator gap.
- The finite dictionary is useful but one-way; it does not prove simple-even structure or a
  spectral limit.

The route is not falsified. The next H7 work should be a separate campaign, not an extension of
this M0 ledger. The highest-value immediate child is to formalize the source finite Galerkin
matrix and parity blocks sufficiently to run a theorem-producing `FALSIFICATION` campaign against
simple/even ground-state uniformity. If that finite hypothesis survives certified probes, a later
`PROOF-ATTEMPT` can target a stable sector gap or the true-ground-state-to-`k_lambda` comparison.
This order tests the source's decisive assumption before investing in an infinite-dimensional
closure extension.

## Mechanical evidence

- Standalone module compile: passed locally.
- `LeanLab/Riemann/Targets.lean`: passed locally.
- `LeanLab/Riemann/TargetChecks.lean`: eight exact H7 statement witnesses passed locally.
- `LeanLab/Riemann/AxiomsAudit.lean`: all eight selected H7 declarations print only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full project build: passed locally with `8,737` jobs.
- Public implementation CI: commit `0ed05ba49605c7de621f16193ff73dd63a7bbabb` passed run
  `29924570570`, build job `88938283725`, in `1m56s`.
- Evidence backfill CI: pending at this checkpoint.
- Persistent RH Goal: active.
