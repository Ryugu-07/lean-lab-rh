# H12 Height-Ten Top Endpoint-Transport Preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Parent subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Subattack: `HEIGHT-TEN-TOP-ENDPOINT-TRANSPORT-01`

Primary mode: `PROOF-ATTEMPT / HISTORICAL-SOURCE-REENTRY`

Status: `PREREGISTERED / PRODUCTION_EDIT_PENDING_PUBLIC_CI / GLOBAL_GOAL_ACTIVE`

## Source target

The fixed lower contour in Levinson--Montgomery requires an actual common zero-free horizontal
segment and control of the argument of `zeta'/zeta`. The project has reduced this source input to

```lean
SpeiserStrictNegativeHorizontal 10
```

and has already proved actual strict-negative neighborhoods at both endpoints. The unresolved
input is the compact middle of `0 <= sigma <= 1/2`.

## Candidate comparison

Three complete-boundary producer classes remain:

1. the left low/middle vertical below `13/2`;
2. the right low/middle vertical below `13/2`;
3. the height-ten compact-middle horizontal.

The horizontal is selected because it is one-dimensional, both endpoint values are already
certified, and its source target has no internal sign transition. The vertical producers each
still contain two sign transitions, while the critical-line side additionally needs actual zeta
nonvanishing.

The paired-zero formula was also screened. At `s=sigma+10*I`, a paired kernel can be negative
only if a nontrivial zero has ordinate within `1/2` of ten. Excluding that band independently
would suffice for a structural proof, but the current project has no such exclusion theorem.
Obtaining it from the height-ten count certificate would make the top producer depend on its own
consumer, so this branch is rejected for the present subattack.

## Navigation-only signal

High-precision navigation, which is not a theorem premise, gives approximately

```text
-0.277 < Re (zeta'/zeta)(sigma+10i) < -0.232
0.102 < |(zeta'/zeta)'(sigma+10i)| < 0.112
```

for sampled `0 <= sigma <= 1/2`. This selects endpoint transport over a large point table. No
decimal value, sampled inequality, or imported boolean may occur in the proof.

## Exact target

Full success is the unconditional theorem

```lean
theorem speiserStrictNegativeHorizontal_heightTen :
    SpeiserStrictNegativeHorizontal 10
```

with all three pointwise clauses on the complete segment:

```text
riemannZeta (sigma + 10*I) != 0,
deriv riemannZeta (sigma + 10*I) != 0,
Re ((deriv riemannZeta / riemannZeta) (sigma + 10*I)) < 0.
```

The theorem must compose with the already compiled vertical-boundary consumer once the two
vertical producers are later supplied.

## Planned proof architecture

1. Work at the reflected segment `w=1-s`, where `1/2 <= Re(w) <= 1` and the existing
   first-corrected Euler--Maclaurin formula applies uniformly with cutoff `N=30`.
2. Expose a finite formula for the derivative of
   `eulerMaclaurinOneZetaDerivApprox`. Prove only the norm estimate needed for variation on the
   reflected half-segment; no general second-derivative API is required.
3. Integrate the two finite derivative bounds to transport the already certified value and
   derivative centers at `w=1/2-10i` across the segment.
4. Prove uniform rational upper bounds for `eulerMaclaurinOneZetaError`,
   `eulerMaclaurinOneZetaDerivError`, and
   `levinsonMontgomeryReflectedArchimedeanUpper` on the same segment.
5. Discharge the literal three hypotheses of
   `speiserStrictNegativePoint_of_reflected_eulerMaclaurinOne_margins` for every sigma and
   construct `SpeiserStrictNegativeHorizontal 10`.

The implementation may split the segment into a small fixed number of rational subintervals if
one endpoint transport bound is too coarse. Every subinterval must be covered by an analytic
variation theorem; finite-center checks alone are insufficient.

## Acceptance criteria

- The full actual-function horizontal theorem compiles under default resources.
- Every division is accompanied by proved nonvanishing.
- The proof uses exact rational and proved transcendental enclosures only.
- Exact TargetChecks and selected axiom prints are added.
- Selected declarations use standard axioms only.
- Production files contain no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`,
  `unsafe`, or relaxed resource option.

## Falsification and local stopping rules

- If the one-endpoint derivative bound cannot retain a strict margin, preserve the compiled
  finite second-derivative formula and exact failed inequality, then use at most a small fixed
  rational subdivision before reconsidering the route.
- If the required finite variation bound itself exceeds the observed margin by a structural
  factor, record the exact obstruction and return to the left/right low-height producers.
- Do not optimize a crossing location or a numerical constant after the full horizontal target
  is decided.
- Success stops only `HEIGHT-TEN-TOP-ENDPOINT-TRANSPORT-01`. The complete-boundary subattack,
  parent campaign, H12, and the global RH Goal remain active.

