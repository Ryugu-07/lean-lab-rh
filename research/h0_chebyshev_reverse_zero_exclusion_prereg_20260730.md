# H0 Chebyshev Reverse Zero-Exclusion Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H0-CHEBYSHEV-REVERSE-ZERO-EXCLUSION-01`

Selected node:
`H0-VON-KOCH-REVERSE-ZERO-EXCLUSION-01`

Mode: `LITERATURE / OMISSION-AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTRATION_PUBLIC_GREEN / IMPLEMENTATION_LOCAL_GREEN`

Preregistration public receipt:

- commit: `c9c561aaeeff665db804828663719ee9be0745ae`;
- Lean Action run: `30522338862`;
- build job: `90805348547`;
- duration: `1m57s`;
- result: pass.

## Historical target

The source endpoint is the reverse half of the von Koch/Chebyshev criterion. DLMF 25.16.4
records

```text
RiemannHypothesis
  iff
for every epsilon > 0,
  psi(x) = x + O(x^(1/2+epsilon)).
```

Primary historical anchor:

- Helge von Koch, *Ueber die Riemann'sche Primzahlfunction*, Mathematische Annalen 55
  (1902), 441--464, `https://eudml.org/doc/158044`.

Modern authoritative statement:

- DLMF 25.16(i), equation 25.16.4, `https://dlmf.nist.gov/25.16#E4`.

This campaign proves only the implication from the displayed error hypothesis to RH. It does
not assume or prove the error hypothesis.

## Existing compiled entrance

`LeanLab/Riemann/ChebyshevMellin.lean` already proves:

1. Mathlib `Chebyshev.psi` is the exact von-Mangoldt partial sum;
2. the error coefficient has partial sum `psi(N)-N`;
3. on `Re(s)>1`, its L-series is `-zeta'(s)/zeta(s)-zeta(s)`;
4. an `O(N^r)` error bound gives the exact naturally ordered Mellin limit on `Re(s)>r`;
5. ordered convergence is not silently replaced by absolute `LSeriesSummable`.

The open inference is to prove holomorphy of that Mellin value and use it to exclude zeros.

## Proposed Lean objects

The production module may rename these objects, but it must preserve their mathematical
meaning:

```lean
noncomputable def chebyshevPsiFloorErrorExtension (t : Real) : Complex :=
  if 1 < t then
    (Chebyshev.psi t : Complex) - (Nat.floor t : Complex)
  else 0

noncomputable def chebyshevPsiErrorContinuation (s : Complex) : Complex :=
  s * mellin chebyshevPsiFloorErrorExtension (-s)
```

The support cutoff is only a device for using Mathlib's full positive-axis Mellin transform. On
`t>1`, it must reduce exactly to the existing floor-error integrand.

## Fixed proof chain

Under

```lean
hO :
  (fun n : Nat => (Chebyshev.psi n : Complex) - (n : Complex))
    =O[atTop] (fun n => (n : Real) ^ r)
hr0 : 0 <= r
hr1 : r < 1
```

the campaign must compile all of the following.

1. The cutoff floor error is locally integrable on `(0,infinity)` and is
   `O(t^r)` at infinity.
2. `chebyshevPsiErrorContinuation` is complex differentiable, hence analytic, at every
   `s` with `r<Re(s)`. The intended library hinge is
   `mellin_differentiableAt_of_isBigO_rpow`; a hand-written differentiation-under-the-integral
   proof is acceptable only if its domination is explicit.
3. On `Re(s)>1`, the continuation agrees exactly with
   `LSeries chebyshevPsiErrorCoeff s`.
4. With `Z=zetaPoleRemoved`, identity continuation across the convex half-plane `r<Re(s)`
   proves

```text
(s-1) Z'(s) = Z(s) * (1 - (s-1) E(s) - Z(s)).
```

   This pole-removed equation must be proved at `s=1` as an analytic identity, not by dividing
   by a totalized zeta value.
5. Analytic zero order in the displayed differential equation proves `Z(s)!=0` on
   `r<Re(s)`. At a hypothetical zero, the left side has order one less than `Z`, while the
   right side has order at least that of `Z`.
6. Every nontrivial zeta zero satisfies `Re(rho)<=r`.
7. If the Chebyshev error hypothesis holds for every `r=1/2+epsilon`, `epsilon>0`, then every
   nontrivial zero has real part at most `1/2`; reflection under `rho -> 1-rho` supplies the
   reverse inequality and yields `Mathlib.RiemannHypothesis`.

## Required theorem-level endpoints

The final names may differ, but exact TargetChecks must expose statements equivalent to:

```lean
DifferentiableAt Complex
  chebyshevPsiErrorContinuation s
```

under `hO`, `0<=r`, and `r<Re(s)`;

```lean
chebyshevPsiErrorContinuation s =
  LSeries chebyshevPsiErrorCoeff s
```

for `1<Re(s)`;

```lean
zetaPoleRemoved s != 0
```

under `hO`, `0<=r<1`, and `r<Re(s)`;

```lean
IsNontrivialZero rho -> rho.re <= r
```

under the same exponent hypothesis; and

```lean
(forall epsilon > 0,
  chebyshev error =O N^(1/2+epsilon)) ->
RiemannHypothesis.
```

## Negative control

Compile an explicit reflection-symmetric real-part witness at `r=3/4`:

```text
beta = 3/4,
0 < beta < 1,
beta <= r,
1-beta <= r,
beta != 1/2.
```

This prevents claiming that a single fixed error exponent above `1/2`, even combined with the
functional-equation reflection, proves RH. The quantifier over every positive epsilon is
essential.

## Known obstacles and falsification points

- Pointwise ordered Dirichlet convergence alone does not provide holomorphy.
- The floor-error cutoff must be definitionally aligned on `t>1`; no continuous surrogate may
  replace it.
- The zeta pole at `1` must be removed before identity continuation.
- Evaluating a totalized logarithmic derivative at a zero is forbidden.
- A proof that assumes zeta nonvanishing in order to derive the continuation is circular.
- A theorem concluding only an ordered Mellin value, or only restating the source criterion,
  does not meet the endpoint.

## Success and failure

`FULL_FIXED_ENDPOINT_SUCCESS` requires the complete seven-step chain, the fixed-exponent
negative control, exact target registration, no-sorry compilation, standard-only axiom audit,
empty forbidden scans, full build, and public immutable evidence.

If any step fails, record the smallest failed Lean statement and its exact library or
mathematical obstruction in `attempts/` and `research/hard_gap_dag.md`. Failure is a valid
campaign result but does not permit replacing the endpoint by a smaller unrelated theorem.

Expected successful classification:

- `result=VON_KOCH_REVERSE_ZERO_EXCLUSION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `conditional_rh_implication_delta=1`;
- `unconditional_chebyshev_error_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Production gate

No `LeanLab/`, `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`,
`LeanLab/Riemann/AxiomsAudit.lean`, or `LeanLab.lean` edit is allowed until this docs-only
preregistration passes public Lean Action CI.

The gate passed at the receipt above. The fixed endpoint now compiles locally and awaits its
independent public implementation gate.
