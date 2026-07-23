# H7 Weil Archimedean Tail Density Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01`

Selected node: `H7-WEIL-ARCHIMEDEAN-TAIL-DENSITY-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `LOCALLY_PROVEN / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Baseline

- `parent_commit`: `98bc69b87c66212e92dc2efc814bbffc4cf847dd`.
- `parent_public_ci`: Lean Action run `29977016712`, build job `89110861524`, passed in `1m55s`.
- `global_goal`: active; RH remains open.
- `route_selection`: `research/route_selection_post_h1_mellin_identity_20260723.md`.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.
- `preregistration_public_ci`: commit `be0b58b3e27bff4af738d81db6cac3f223f2eee7`, Lean Action run
  `29977635904`, build job `89112697896`, passed in `1m28s`.

## Primary source alignment

The fixed source is Groskin, [arXiv:2607.02828](https://arxiv.org/abs/2607.02828), equation
`arch-source`, the node and diagonal calculations in Theorem 3.2, and only the rank-two part of
that theorem. Connes--Consani--Moscovici, arXiv:2511.22755, equations `thetaprime`, `weinfty`, and
Proposition `computearch` pin the same archimedean density and finite Galerkin block.

The Lean endpoint must use the literal interval kernel

```text
S(r,x,L) = integral_0^L sin(2*pi*x*(1-y/L))*cos(r*y) dy
```

and the literal density

```text
h_+(r) = Re digamma(1/4+i*r/2) - log pi.
```

Defining only the desired closed matrix entries is not sufficient for source alignment.

## Fixed Lean endpoint

1. Define `h_+`, `rho=2*pi/L`, the literal interval kernel `S`, and its source tail-density
   factor `(1/pi^2)h_+(T)S(T,x,L)`.
2. Prove the kernel is differentiable in `x`, with differentiation under the finite interval
   integral justified.
3. For centered integer frequency `n` and `T>rho*N`, prove the exact source node formula and the
   exact derivative formula. The diagonal must come from the derivative of the true source, not
   from differentiating an integer-node surrogate.
4. Construct value and derivative samples from the literal source and then the finite
   divided-difference matrix through `weilFiniteDividedDifferenceMatrix`.
5. Prove the exact entry formula and rank-two Cauchy decomposition with vectors
   `p_T(n)=1/(T/rho-n)` and `q_T(n)=1/(T/rho+n)`.
6. Prove reflection-sector preservation and the all-vector quadratic identity as a scalar times
   the sum of two squares.
7. Define the entrywise interval increment from these source densities and prove its quadratic
   value is the integral of the pointwise sum of squares. Under the explicit premise
   `forall r in [T1,T2], 0<=h_+(r)`, prove the increment is positive semidefinite.

## Decision criteria

- `FULL_SUCCESS_AT_TAIL_DENSITY_ENDPOINT`: all seven items compile without `sorry`; exact
  TargetChecks, selected axiom prints, full build, and all public evidence gates pass.
- `PARTIAL_SOURCE_SAMPLES_ONLY`: the literal node and diagonal identities compile but the
  matrix-integral interchange does not. Record the exact finite-sum or interval-integrability
  obligation and do not register increment nonnegativity.
- `SOURCE_MISMATCH`: a factor of `2`, `pi`, `rho`, a sign, or the diagonal formula differs from
  the primary source. Stop and register the mismatch before any repair.
- `FALSIFICATION_DIAGONAL`: the integer values agree but the derivative of the actual interval
  source does not equal the claimed diagonal surrogate. Stop; the source matrix identification
  is invalid at this endpoint.

## Claim boundary

The source's unconditional tail-order theorem additionally uses the analytic fact
`h_+(T)>0` for `T>=7`, whose published proof includes an Arb interval evaluation at `T=7`, and a
rational-function argument for strict positive definiteness over an interval. This campaign does
not import that sign as an axiom and does not report unconditional archimedean monotonicity unless
Lean proves it. The matrix nonnegativity theorem is conditional on an explicit pointwise sign
premise.

No strict total positivity, tail limit, tail budget, total Weil sign, Herglotz inequality,
simple-even theorem, ground/prolate comparison, source convergence, H7, or RH is in scope.

## Mechanical gates

Production code must pass direct warning-as-error compilation, exact TargetChecks, selected
`#print axioms`, an empty forbidden-token scan, `git diff --check`, and the full `lake build`.
Publication requires frozen implementation CI, immutable-evidence CI, and final-ledger CI. Proof
source freezes after implementation CI.

## Local implementation result

All seven fixed items compile in `LeanLab/Riemann/WeilArchimedeanTailDensity.lean`. The actual
source diagonal agrees with the primary-source formula, so neither `SOURCE_MISMATCH` nor
`FALSIFICATION_DIAGONAL` fired. The implementation also derives continuity of the literal
digamma density from Gamma analyticity and nonvanishing on the right half-plane, allowing the
entrywise increment identity to compile without an added integrability premise.

The result is `FULL_SUCCESS_AT_TAIL_DENSITY_ENDPOINT` locally. It is not public evidence until
the frozen implementation commit passes public CI. The unconditional `h_+` threshold and every
claim boundary above remain open.
