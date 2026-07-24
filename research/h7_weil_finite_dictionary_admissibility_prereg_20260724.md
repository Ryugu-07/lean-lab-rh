# H7 Weil Finite Dictionary Admissibility Preregistration

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01`

Selected node: `H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `46befa6a2e935e73b077140e5e9df24df3623db6`.
- `parent_public_ci`: Lean Action run `30073083407`, build job `89417854356`, passed in `1m39s`.
- `route_selection`: `research/route_selection_post_h7_volterra_20260724.md`.
- `global_goal`: active; RH remains open.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.

## Primary source alignment

The fixed source is Groskin, arXiv:2607.02828, Lemma 2.2 and the test-function definitions
immediately preceding it. For

```text
Delta = log(C)/(2*pi),
hat(g_u)(xi) = pi*K_u(1-|xi|/Delta) for |xi|<=Delta, and 0 otherwise,
g_u(z) = integral_[-Delta,Delta] hat(g_u)(xi)*exp(2*pi*i*z*xi) dxi,
```

the source claims, for every finite even-sector vector, that `g_u` is even and entire of
exponential type at most `log(C)`, that `hat(g_u)` is continuous and compactly supported, and
that

```text
g_u(z) = O((1+|Re z|)^-2)
```

uniformly on each fixed horizontal strip. It then invokes the local Riemann--von Mangoldt zero
count to obtain an absolutely convergent zero sum.

No moment-neutrality premise is part of this lemma.

## Fixed Lean endpoint

Create `LeanLab/Riemann/WeilFiniteDictionaryAdmissibility.lean` and prove the following from the
literal objects in `WeilFiniteDictionarySourceCalculus`.

1. Prove `K_u(0)=0`, continuity of the Volterra kernel, continuity of the piecewise Fourier
   weight across `xi=0` and `xi=+-Delta`, compact support in `[-Delta,Delta]`, and integrability.
2. Define the literal source test by the Fourier integral above. Prove evenness and complex
   differentiability everywhere. Record the exact exponential-type bound with source width
   `log(C)`.
3. Define the logarithmic physical density

```text
f_u(x) = (1/(2*pi))*exp(-x/2)*hat(g_u)(x/(2*pi)).
```

   Prove its continuity and compact support and prove the exact change-of-variables identity
   between `g_u(z)` and the project `compactLaplaceTransform` at `1/2+i*z`. Deduce the exact
   coordinate identity at every actual xi divisor zero.
4. Prove the source-strength decay statement: for every fixed horizontal-strip height `A`, there
   exists `M>=0` such that

```text
|Im z|<=A ->
norm(g_u(z)) <= M*(1+|Re z|)^-2.
```

   The proof may split the two half-bands and integrate by parts twice, retaining every boundary
   and derivative-jump term, or formalize an equivalent bounded-variation/Stieltjes argument.
5. Use the actual xi divisor, with analytic multiplicity, to prove

```text
Summable (fun p =>
  g_u ((riemannXiDivisorZeroValue p - 1/2) / i)).
```

   Also prove summability of the norms. The proof must derive the needed zero-count or reciprocal-
   square majorant from existing certified project theorems.
6. Package items 1--5 in one certificate and register one proven Target only after all mechanical
   gates pass.

The campaign may additionally prove the exact pointwise project prime-weight normalization if it
is needed for the coordinate audit, but that identity cannot substitute for items 4 and 5.

## Decision criteria

- `FULL_ADMISSIBILITY_SUCCESS`: all six items compile, including horizontal-strip inverse-square
  decay, actual multiplicity-bearing norm summability, TargetCheck, axiom audit, full build, and
  public evidence gates.
- `PARTIAL_COORDINATE_TRANSPORT`: continuity, support, entire/even structure, and exact
  source-to-project coordinates compile, but decay or actual-zero summability does not. Register
  only the exact partial theorem and record the first missing analytic implication.
- `BV_INTERFACE_BLOCKED`: the literal Fourier weight has the source boundary behavior, but the
  second integration by parts cannot be derived with the available absolutely-continuous or
  bounded-variation API. Record the precise theorem signature needed; do not assume it.
- `SOURCE_MISMATCH`: a sign, `2*pi`, `1/2` shift, Fourier orientation, boundary value, or claimed
  regularity differs from the literal source. Stop and register the mismatch.
- `PREMISE_CREEP`: any decay, zero-count, or summability premise equivalent to the desired
  conclusion is introduced abstractly. Stop without the aggregate Target.

## Known obstacles

- `hat(g_u)` is continuous but need not be globally `C^1`; derivatives can jump at the origin and
  band endpoints. The existing project explicit formula assumes a compact `C^6` density and
  cannot be applied directly.
- A first integration by parts cancels value boundaries. The second must retain the derivative
  jumps rather than treating them as zero.
- The source zero coordinate is `(rho-1/2)/i`, while the project stores `rho`; all transforms must
  be checked at this exact affine rotation.
- The divisor index carries multiplicity. Replacing it by a set of distinct zeros is forbidden.
- Entirety alone does not imply the required strip decay or zero-sum convergence.

## Claim boundary

This campaign does not prove the Guinand--Weil arithmetic explicit formula for the weaker
piecewise-smooth/BV class, the equality of the total finite matrix quadratic with the zero sum,
the pole or archimedean matrix transports, pole-neutral survival, inverse/density, cutoff limits,
positivity, simple-even ground states, H7, or RH.

## Mechanical gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct warning-as-error compilation, exact TargetChecks, selected transitive
`#print axioms`, an empty forbidden scan, `git diff --check`, full `lake build`, frozen
implementation CI, immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

