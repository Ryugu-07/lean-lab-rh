# H11 Moving-Window Boundary Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H11-MOVING-WINDOW-BOUNDARY-01`

Selected node: `H11-GALLAGHER-MUELLER-EXACT-BOUNDARY-01`

Status: `PREREGISTERED / PRODUCTION_GATE_CLOSED`

## Selection reason

The Hardy Abel-moment campaign is publicly closed at final-ledger commit
`72f13a727fd71604095c054cb0f0574436c9795a`. Fresh H1/H2/H7/H10/H11/H12 comparison selected
the moving-window boundary in the Gallagher--Mueller second-moment mechanism because the
published asymptotic deliberately discards exact signed information there.

This is not a numerical optimization. The fixed question is whether retaining the literal
window-overlap measure produces an exact nonnegative remainder and a useful one-sided bridge
before Fujii's analytic estimate is introduced.

## Locked primary sources

1. Daniel A. Goldston, Junghun Lee, Jordan Schettler, and Ade Irma Suriajaya,
   "Pair Correlation Conjecture for the Zeros of the Riemann Zeta-function I: Simple and
   Critical Zeros," arXiv:2503.15449v4, Sections 5 and 9.
   <https://arxiv.org/abs/2503.15449v4>
2. P. X. Gallagher and Julia H. Mueller, "Primes and zeros in short intervals,"
   *Journal fuer die reine und angewandte Mathematik* 303/304 (1978), 205--220.
   <https://eudml.org/doc/152055>

## Source-exact objects

For a finite multiplicity-copy population `gamma : iota -> Real`, define

```text
windowCount gamma U t
  = number of i with t < gamma(i) <= t+U

windowSecondMoment gamma T U
  = integral t in 0..T, windowCount gamma U t ^ 2

windowOverlap T U x y
  = max 0 (min T (min x y) - max 0 (max x y - U)).
```

Endpoint choices are fixed as `t < gamma <= t+U`. Changing them on a null boundary is allowed
only through a proved interval-integral congruence.

For `0 <= T`, `0 <= U`, the exact pair expansion should be

```text
windowSecondMoment gamma T U
  = sum_i sum_j windowOverlap T U (gamma i) (gamma j).
```

If every ordinate lies in `[U,T+U]`, split indices at `gamma <= T`. Interior-interior pairs
contribute the exact triangular weight. Every remaining overlap contribution is nonnegative:

```text
windowSecondMoment
  = interiorTriangularMass + topBoundaryRemainder,
0 <= topBoundaryRemainder.
```

The boundary remainder should also be bounded by `U` times the square of the number of points in
the local band `(T-U,T+U]`, or by an equivalent exact finite bound that exposes the same local
support.

## Fixed Lean endpoint

Create `LeanLab/Riemann/PairCorrelationMovingWindowBoundary.lean`, importing
`LeanLab.Riemann.PairCorrelationTriangularMass`, and compile all blocks below without
placeholders.

1. Define `shortWindowCount`, `shortWindowSecondMoment`, and `pairWindowOverlap`.
2. Prove measurability/integrability and the exact finite pair expansion of the squared count.
3. Prove that an interior pair with `U <= x,y <= T` has overlap
   `max 0 (U-|x-y|)`.
4. Define the interior triangular mass and exact top-boundary remainder for a finite population
   supported in `[U,T+U]`; prove the exact decomposition and remainder nonnegativity.
5. Prove the remainder is supported on the local boundary band and bounded by
   `U * boundaryCount^2`, or an extensionally equivalent finite sum bound.
6. Prove the one-point future control: for `T>0`, `U>0`, a point at `T+U` has zero overlap but
   full triangular self-weight `U`. Use it to reject termwise equality with full triangular
   weights for the future block.
7. Deduce `interiorTriangularMass <= shortWindowSecondMoment`.
8. Instantiate the exact decomposition on the actual multiplicity-expanded zeta population at
   cutoff `T+U`, keeping the lower-support condition explicit if the project has no compiled
   first-zero certificate.
9. Bundle the finite and actual-zeta statements in one aggregate endpoint certificate.

Names may be adjusted to local APIs, but the endpoint may not silently replace the exact overlap
by an asymptotic `O` statement or an abstract assumed identity.

## Adversarial cases

- `U=0`: every overlap and moment is zero.
- `T=0`: the interval integral is zero.
- interior singleton `x in [U,T]`: contribution is exactly `U`.
- upper endpoint singleton `x=T+U`: overlap is zero, not `U`.
- future singleton `T<x<T+U`: overlap is `T+U-x`, not `U`.
- duplicate ordinates: ordered multiplicity copies contribute the square of the fiber size.
- pair gap `|x-y|=U`: triangular and overlap contributions are zero.
- mixed pair with one point above `T`: both orientations must be retained.

## Success and falsification criteria

`FULL_SUCCESS` requires all nine endpoint blocks, an aggregate proven Target, exact
TargetChecks, selected transitive axiom prints, an empty forbidden scan, warning-as-error
compilation, a full build, and independent public CI for preregistration, frozen implementation,
immutable evidence, and final ledger.

`MEANINGFUL_PARTIAL` requires the exact finite pair expansion plus either the exact signed
boundary decomposition or a kernel-checked obstruction to it.

`SOURCE_BOOKKEEPING_CORRECTION` is recorded if the future-block termwise replacement is
falsified while the source's `O(L^2)` proposition remains valid.

## Known obstacles and strict boundary

- The interval indicators use one open and one closed endpoint.
- Squaring a finite count creates ordered pairs, which is required.
- `min`/`max` overlap formulas need separate empty and nonempty interval cases.
- The actual-zeta cutoff at `T+U` and the interior cutoff at `T` have different sigma index
  types; an explicit multiplicity-preserving restriction or a filtered big-cutoff sum is
  required.
- The project does not presently expose the numerical first-zero bound `gamma>14.1`; the Lean
  theorem must retain lower support as a premise unless that fact is independently proved.
- Riemann-von Mangoldt, Fujii's second moment, PCC, HMH, an absolute error below one horizontal
  pair, sparse-exception amplification, H11, and RH remain outside this campaign.

## Mechanical gates

Before proof-source editing:

- publish this docs-only preregistration;
- require public Lean Action CI to pass;
- keep the six inherited protected files untouched and unstaged.

Before accepting any theorem:

- register one aggregate target in `Targets.lean`;
- add exact witnesses in `TargetChecks.lean`;
- print selected transitive axioms in `AxiomsAudit.lean`;
- scan for `sorry`, `admit`, `native_decide`, custom `axiom`, `opaque`, and `unsafe`;
- compile the module with warnings as errors and run the full build;
- freeze the implementation before publishing evidence.

## Stop and successor rule

Stop locally at `FULL_SUCCESS`, `MEANINGFUL_PARTIAL`, or a kernel-checked falsification of the
fixed decomposition. Local stop returns to fresh cross-family `ROUTE_SELECTION`; it does not
stop the global RH Goal. Direct RH attacks and conjecture verification remain open throughout.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; reread governance pointers, current
  census and atlas, H2/H7/H10/H11/H12 frontiers, the H11 finite implementation, and the primary
  source proof of equations `(5.2)`--`(5.4)` before selection.
- `global_goal`: active.

