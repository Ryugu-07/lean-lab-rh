# H7 Finite Guinand--Weil Dictionary Explicit Formula Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Selected node: `H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `0e10b1899daf7ce0c3ce48ab4ccd857d7e9c61c8`.
- `parent_public_ci`: Lean Action run `30185002301`, build job `89747968167`, passed in
  `1m53s`.
- `route_selection`: `research/route_selection_post_h9_abel_20260726.md`.
- `global_goal`: active. RH is the target.
- `production_gate`: no production Lean source, Target, TargetCheck, or axiom-audit entry may be
  created or edited before this docs-only state passes public Lean Action CI.

## Locked primary source

Akiva Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated
Weil quadratic form*, arXiv:2607.02828v1 (2026), especially Lemma 2.2 and Theorem 2.5.

For prime cutoff `c>1`, band `N`, and a real even Galerkin vector `v`, the source defines

```text
v -> T_v -> K_v -> ghat_v -> g_v
```

and states

```text
<v,Q_infinity v> = sum*_{zeta(1/2+i z)=0} g_v(z),
```

with multiplicity. Its equivalent arithmetic form is

```text
sum* g_v(z)
  = -(1/pi) * sum_{q<=c} Lambda(q)/sqrt(q)
        * ghat_v(log(q)/(2*pi))
    + 2*g_v(i/2)
    + (1/(2*pi)) * integral_R h_+(r)*g_v(r) dr.
```

The source's proof invokes the Guinand--Weil explicit formula for continuous compactly supported
Fourier weights whose induced entire tests have inverse-square decay on horizontal strips. This
campaign treats the source as an unreviewed S3 preprint: every normalization and analytic
passage must be independently compiled.

## Compiled project state

The project already proves, without RH:

1. the literal centered trigonometric polynomial, Volterra kernel, Fourier weight, and entire
   test `weilFiniteDictionaryTest`;
2. exact prime-source divided differences and
   `weilFinitePrimeSourceMatrix_quadratic_eq_fourierWeight`;
3. continuity and compact support of `weilFiniteDictionaryPhysicalDensity`;
4. exact affine conversion
   `weilFiniteDictionaryTest C N u ((s-1/2)/I)` to the project compact-Laplace coordinate;
5. reflection symmetry and equality with `symmetrizedCompactLaplaceWeight`;
6. inverse-square horizontal-strip decay;
7. absolute summability over `RiemannXiDivisorZeroIndex` with analytic multiplicity;
8. separate literal finite pole, prime, and archimedean source objects.

The project arithmetic explicit formula currently requires `ContDiff R 6 f`. The dictionary
physical density is continuous and compactly supported but only piecewise smooth at the center
and support boundaries, so that theorem cannot be specialized honestly.

## Fixed primary Lean endpoint

Create `LeanLab/Riemann/WeilFiniteDictionaryExplicitFormula.lean` only after public
preregistration CI.

For `2 <= C`, every `N`, every real coefficient vector
`u : Fin (2*N+1) -> R`, and every contour line `1<c`, prove without a target-equivalent premise:

```text
(pi : C) *
  tsum (fun p : RiemannXiDivisorZeroIndex =>
    weilFiniteDictionaryTest C N u
      ((riemannXiDivisorZeroValue p - 1/2) / I))
=
2*(pi : C) *
  symmetrizedCompactLaplaceWeight
    (weilFiniteDictionaryPhysicalDensity C N u) 1
+ compactSymmetrizedXiArchimedeanIntegral
    (weilFiniteDictionaryPhysicalDensity C N u) c
- tsum (compactSymmetrizedVonMangoldtWeight
    (weilFiniteDictionaryPhysicalDensity C N u)).
```

Equivalent reassociation or a theorem first stated with
`symmetrizedCompactLaplaceWeight` on the zero side is allowed only if an unconditional corollary
rewrites it to the displayed literal dictionary test.

## Required source-coordinate corollaries

The campaign endpoint must also compile:

1. `zero`: the displayed zero sum equals the literal source `sum* g_u(z)` under
   `s=1/2+iz`, with multiplicity retained;
2. `pole`: the project pole term rewrites to `2*g_u(i/2)` after division by `pi`, using proved
   evenness rather than a sign convention;
3. `prime`: compact support makes the von-Mangoldt side finite at `q<=C`, and its normalization
   agrees with the existing finite prime-source quadratic;
4. `archimedean`: the project Gamma-real-place integral rewrites to the source
   `(1/(2*pi))*integral h_+(r)*g_u(r) dr`, or to an explicitly proved equivalent normalization;
5. `assembly`: package these identities as the source arithmetic expression and, wherever the
   already compiled finite block definitions suffice, as the cutoff-free finite dictionary
   quadratic-to-zero-sum identity.

The first displayed arithmetic explicit formula is mandatory. A definition that merely names its
right-hand side `Q_infinity` is not an acceptable substitute for matrix/source-block alignment.

## Registered attack order

### Attack A: direct weak-regularity contour

Use the generic theorem `tendsto_selectedXiRightVerticalIntegralFor`. Differentiability,
reflection symmetry, and zero summability are already compiled. Prove directly that

```text
Tendsto
  (selectedXiTopHorizontalIntegralFor
    (symmetrizedCompactLaplaceWeight
      (weilFiniteDictionaryPhysicalDensity C N u)) c)
  atTop (nhds 0).
```

Then reuse the arithmetic right-vertical decomposition, proving only the regularity actually
needed for its pole, prime, and Gamma limits.

### Attack B: source-faithful smooth approximation

If Attack A needs an unavailable sharper top-edge estimate, construct compact `C^6` approximants
to the piecewise-smooth physical density with a fixed support margin. Prove convergence of:

- the multiplicity-bearing zero `tsum`;
- the pole value;
- the finite prime side;
- the Gamma-real-place integral.

Apply the existing `C^6` formula to each approximant and pass to the limit. No convergence clause
may be assumed in a form equivalent to the desired formula.

## Decision criteria

- `FULL_DICTIONARY_EXPLICIT_FORMULA_SUCCESS`: the mandatory formula, all four source-coordinate
  corollaries, honest assembly statement, aggregate certificate, proven Target, exact
  TargetChecks, selected transitive axiom audit, forbidden scans, full build, and public evidence
  sequence all pass.
- `WEAK_REGULARITY_CONTOUR_BLOCKED`: the direct route reaches the exact top-edge limit above but
  cannot prove it from current xi logarithmic-derivative estimates. Record the strongest derived
  bound and the exact missing theorem signature.
- `SMOOTH_APPROXIMATION_BLOCKED`: a concrete approximating family compiles, but one named
  zero/pole/prime/archimedean convergence theorem remains unavailable. Record that theorem with
  all hypotheses and do not assert the limit.
- `SOURCE_NORMALIZATION_MISMATCH`: a factor, sign, cutoff, multiplicity, Gamma density, or affine
  zero coordinate disagrees with Theorem 2.5. Compile the mismatch if possible and stop the
  source claim.
- `PREMISE_CREEP`: the explicit formula, top-edge limit, or all-side convergence is introduced
  as an abstract assumption equivalent to the endpoint. Reject the attempt and do not add a
  Target.
- `local_stop`: full public closure, a source mismatch, or one exact analytic blocker after both
  registered attack modes have been tested and no honest stronger source advance remains. Local
  stop returns to `ROUTE_SELECTION`; it never stops the global RH Goal.

## Known obstacles

- The dictionary test has inverse-square horizontal-strip decay. The current selected-height
  project bound for `logDeriv riemannXi` is `O(R^4)`, so their product does not establish
  top-edge vanishing.
- A source-valid direct proof may need a sharper selected-height bound, a local
  Riemann--von Mangoldt zero count, or a different contour decomposition. None is currently a
  compiled project premise.
- Smooth approximation must preserve enough support control to keep the prime side finite and
  must dominate the zero and Gamma sides uniformly. Pointwise convergence alone is insufficient.
- The derivative jumps at the center and Fourier support endpoints must not be silently replaced
  by global `C^2`, `C^6`, or Schwartz regularity.
- The source uses zeta-zero coordinates `1/2+i z`; the project divisor is in the `s` coordinate.
  All factors of `i`, `pi`, and `2*pi` must be checked in Lean.
- The source's `Q_infinity` is cutoff-free only in the archimedean variable. It still depends on
  finite prime cutoff and finite Galerkin band; no `C->infinity` or `N->infinity` limit is part of
  this campaign.

## Claim and originality boundary

Success would formalize a known explicit-formula theorem for the project's literal finite
dictionary and would close a substantial historical H7 source edge. It would not prove
positivity, simple-even ground states, an inverse/density theorem, H7, or RH. Expected successful
deltas are `source_analytic_bridge_delta=1`,
`historical_route_coverage_delta=1`, and `rh_frontier_delta=0`.

## Mechanical and publication gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct module compilation, exact TargetChecks, selected transitive
`#print axioms`, empty forbidden token/declaration/resource scans, `git diff --check`, full
`lake build`, frozen implementation CI, immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.
