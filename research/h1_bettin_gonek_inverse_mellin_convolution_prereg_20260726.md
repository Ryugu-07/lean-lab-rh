# H1 Bettin--Gonek Inverse Mellin Convolution Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-BETTIN-GONEK-INVERSE-MELLIN-CONVOLUTION-01`

Selected node: `H1-BETTIN-GONEK-INVERSE-MELLIN-CONVOLUTION-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `f7c137b128406dd55b09d81411c2d7e38d81f731`.
- `parent_public_ci`: Lean Action run `30140898700`, build job `89633790335`, passed in
  `1m36s`.
- `route_selection`: `research/route_selection_post_h7_admissibility_20260726.md`.
- `global_goal`: active; RH remains open.
- `production_gate`: no production Lean source may be created or edited before this
  preregistration commit passes public Lean Action CI.

## Primary source alignment

The fixed source is Bettin and Gonek, *The theta=infinity conjecture implies the Riemann
hypothesis*, arXiv:1604.02740, equations `(2.2)`--`(2.4)`. With

```text
G_t(w) =
  (w-1)^2 (w-3/2+it) zeta(w-1/2+it)
  / ((w+1)^2 (w-1/2+it-rho_0) (w+it+1)^4),

g_t(u) = (1/(2*pi*i)) integral_(3-i infinity)^(3+i infinity)
  G_t(w) u^(-w) dw,
```

the source states that `G_t` is holomorphic on `Re(w)>=0` and

```text
G_t(w) << (1+|w+it|)^(-5/2).
```

It then moves the inverse-Mellin line to `Re(w)=+infinity` for `u>1` and to `Re(w)=0` for
`0<u<=1`, obtaining `g_t(u)=0` in the first range and `g_t(u)=O(1)` in the second. Finally it
invokes Mellin convolution to identify

```text
J_t(x) =
  integral_1^infinity M_y(1/2+it) log(y) g_t(y/x) dy
```

and reduces the upper limit to `x`.

The project already compiles the literal regularized `G_t`, the actual mollifier and its
Mellin transform, and the exact `J_t` line integral and residue contour. It does not compile the
standalone `G_t` estimate, `g_t`, its support/bound, or the convolution identity.

## Fixed Lean endpoint

Create `LeanLab/Riemann/BettinGonekInverseMellinConvolution.lean` and prove the following for an
actual nontrivial zero `rho`.

1. Define the literal normalized inverse Mellin kernel for `0<u`:

```text
bettinGonekInverseMellinKernel rho t u =
  (1/(2*pi)) * integral y : R,
    bettinGonekAuxiliaryG rho t (3+y*i) * u^(-(3+y*i)).
```

The principal complex power and the conversion from `dw` to ordinate integration must match the
source normalization exactly.

2. Prove source-strength standalone vertical control. On every fixed real-part strip needed by
the contour argument, derive an integrable bound for
`bettinGonekAuxiliaryG rho t (sigma+y*i)` with decay exponent at least `5/2`. In particular,
prove absolute integrability on `sigma=0` and `sigma=3`. Derive the separate uniform estimates
needed when `sigma` tends to `+infinity`; do not assume them through an abstract decay premise.

3. Prove the inverse-Mellin line shifts and equation `(2.2)`:

```text
1 < u      -> bettinGonekInverseMellinKernel rho t u = 0,
0 < u <= 1 -> norm (bettinGonekInverseMellinKernel rho t u)
                <= bettinGonekInverseMellinBound rho t
```

for an explicit nonnegative finite bound independent of `u`. The first statement must come from
finite rectangles followed by a proved `Re(w)->+infinity` limit. The second must identify the
line-three integral with the line-zero integral.

4. Prove the direct source convolution identity for `2<=x`:

```text
bettinGonekJLineIntegral rho t x 3 =
  integral y in Set.Ioi 1,
    bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
      bettinGonekInverseMellinKernel rho t (y/x).
```

The proof must use the actual `HasMellin` theorem or a direct Bochner Fubini argument. A generic
convolution hypothesis equivalent to the displayed identity is forbidden.

5. Use the compiled support and bound, not an informal cutoff, to prove the source upper
estimate in a precise interval-integral form:

```text
norm (bettinGonekJLineIntegral rho t x 3) <=
  bettinGonekInverseMellinBound rho t *
    integral y in Set.Icc 1 x,
      norm (bettinGonekLogMollifier y (farmerCriticalLinePoint t)).
```

An equivalent interval convention is allowed if all endpoints and zero extensions are proved
to agree.

6. Package items 1--5 in one certificate. Add one proven Target only after the exact
TargetChecks, selected transitive axiom audit, forbidden scan, patch check, and full build pass.

## Decision criteria

- `FULL_INVERSE_MELLIN_SUCCESS`: all six items compile, including support, uniform boundedness,
  actual convolution, source integral bound, exact checks, axiom audit, full build, and public
  evidence gates.
- `PARTIAL_VERTICAL_KERNEL`: standalone decay/integrability and at least one exact line shift
  compile, but support or convolution is blocked. Register only the strongest exact partial
  theorem and record the first missing implication.
- `ANALYTIC_INTERFACE_BLOCKED`: the source statement is consistent, but the required zeta-growth,
  arbitrary-right contour, improper-integral, or Fubini theorem cannot be derived from current
  APIs. Record the exact missing theorem signature and its mathematical hypotheses.
- `SOURCE_MISMATCH`: the claimed `5/2` decay, holomorphy region, power branch, support direction,
  convolution orientation, or `2*pi` normalization fails for the literal source objects. Stop
  and register the mismatch.
- `PREMISE_CREEP`: support, boundedness, convolution, or a tail limit is introduced as an
  assumption equivalent to the target. Stop without the aggregate Target.

## Known obstacles

- On `Re(w)=0`, the zeta argument has real part `-1/2`. The standalone `G_t` proof must obtain
  enough polynomial control from the functional equation or an existing certified growth
  theorem; the rational cancellation used by `BettinGonekJContour.lean` is unavailable.
- Support for `u>1` needs line shifts to arbitrarily large real part and a limit uniform enough
  to integrate over the full ordinate line. A fixed finite rectangle is insufficient.
- The project has no identified generic inverse-Mellin convolution theorem. A direct source-
  specific Tonelli/Fubini proof must establish all norm-integrability hypotheses.
- The source defines `g_t` only for positive `u`; the displayed `0<=u<=1` bound must not silently
  assign a value at zero.
- The actual divisor parameter `rho`, `t` shift, principal complex power, and normalized vertical
  integral must be retained. Replacing them with an abstract holomorphic function is not source
  reconstruction.

## Material difference from prior H1 attempts

The earlier Mellin campaign compiled `H_t`. The earlier J-contour campaign multiplied `G_t` by
`H_t`, canceled zeta and its selected-zero factor, and controlled a rational kernel. This
campaign controls `G_t` before cancellation and proves the missing inverse-transform and
convolution bridge. It therefore cannot reuse the rational J-kernel estimate as a substitute.

## Claim boundary

This campaign does not prove the Cauchy--Schwarz square estimate, the critical-line zeta
second-moment lower bound, integration in `t`, the complete moment-to-power theorem, Farmer's
arbitrary-length moment conjecture, the H1 route endpoint, or RH.

## Mechanical gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct warning-as-error compilation, exact TargetChecks, selected transitive
`#print axioms`, an empty forbidden scan, `git diff --check`, full `lake build`, frozen
implementation CI, immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Production gate

Closed pending a public-green preregistration commit.
