# R5 Weil Strip Class Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-R5-WEIL-STRIP-CLASS-01`

Mode: `ROUTE_MAP -> CONJECTURE_GENERATION -> ADVERSARIAL_TEST -> FORMALIZATION -> INDEPENDENT_AUDIT`

Route family: R5, explicit formula and test-function positivity.

## Independent Evidence For Same-Route Continuation

The preceding R5 campaign closed only W1a, the pointwise convergent Mellin-convolution product.
Lagarias Appendix A now supplies a distinct exact successor: the physical test space `A_delta`
whose Mellin transforms are analytic in the open strip centered at `1/2`, continuous on its
boundary, and controlled by the uniform norm on the closed strip. W1a supplies the missing
convolution-product theorem needed to prove algebra closure rather than postulate it.

Mathlib independently supplies:

- `AnalyticOnNhd.congr` on open sets and analytic addition, scalar multiplication, composition,
  and multiplication;
- complex differentiability of `conj o F o conj` when `F` is differentiable;
- `ContinuousOn` composition and algebra operations;
- the exact Mellin convergence/value theorems for addition, scalar multiplication, involution,
  conjugation, star, and W1a convolution.

This admits one same-route campaign. It does not admit completeness, density, the explicit formula,
or positivity.

## Fixed Endpoint

Define the symmetric strips

```lean
def weilOpenStrip (delta : Real) : Set Complex :=
  {s | abs (s.re - 1 / 2) < delta}

def weilClosedStrip (delta : Real) : Set Complex :=
  {s | abs (s.re - 1 / 2) <= delta}
```

and a physical-function predicate whose fields are independently checkable:

```lean
structure IsWeilStripAdmissible (delta : Real) (f : Real -> Complex) : Prop where
  delta_pos : 0 < delta
  convergent : forall s, s in weilClosedStrip delta -> MellinConvergent f s
  analyticOn : AnalyticOnNhd Complex (mellin f) (weilOpenStrip delta)
  continuousOn : ContinuousOn (mellin f) (weilClosedStrip delta)
  uniformlyBounded : exists C, 0 <= C /\
    forall s, s in weilClosedStrip delta -> norm (mellin f s) <= C
```

The indivisible endpoint must prove this predicate for:

```lean
0
f + g
c • f
weilInvolution f
(fun x => conj (f x))
weilStar f
weilConvolution f g
```

from the corresponding admissibility hypotheses. For convolution, every analytic and continuous
claim must be derived by combining W1a's pointwise Mellin equality with product closure on the
strip. For conjugation/star, the proof must justify that the two anti-holomorphic conjugations
cancel; continuity alone is insufficient.

Minor elaboration changes are allowed, but no field may be replaced by a closure assumption or a
compact-support premise.

## Candidate Generation And Adversarial Tests

At most five candidates were screened.

### C1: complete metric-space formalization of Lagarias `A_delta`

Deferred. The transform uniform distance is only a pseudometric on raw pointwise functions until
one quotients by almost-everywhere equality and proves the needed Mellin uniqueness. Completeness
also needs a physical inverse/closed-range theorem. Claiming it now would hide a separate hard
functional-analytic edge.

### C2: physical strip-admissibility predicate and algebra closure

Selected. Each source condition is explicit, and W1a now proves convolution closure instead of
encoding it. This is the exact class interface needed before an explicit formula can be stated.

### C3: compactly supported smooth functions

Rejected as the endpoint. No compiled density theorem transfers this narrower class to Lagarias's
closed-strip space, so it cannot replace W1b.

### C4: transform-only bounded analytic functions

Rejected. It omits the physical function and does not prove that a product transform has a physical
convolution representative. That is exactly the interface W1a was built to preserve.

### C5: critical-line `L1` or `L2` class only

Rejected. A single vertical line omits the open analytic strip and boundary data needed for the
unconditional zero distribution and contour motion.

Adversarial tests for C2:

- `delta` must be positive; otherwise the apparent strip can be empty and closure is vacuous;
- the open strip must be open and included in the closed strip;
- `s -> 1-s`, `s -> conj(s)`, and `s -> 1-conj(s)` must preserve both strips exactly;
- pointwise Mellin convergence must be recorded separately because Mathlib's nonintegrable
  integral convention still assigns a value;
- the closed-strip uniform bound must be explicit and finite, not represented by an unchecked
  `sSup`;
- `s -> conj(F(conj s))` must be proved analytic by conjugate-conjugate differentiability;
- multiplication bounds require nonnegative witnesses and use `C*D`;
- no metric separation, completeness, Mellin inversion, density, explicit formula, or positivity
  may be inferred from the class fields.

Normalized tuple:

```text
(positive-width physical Mellin class with closed-strip convergence/continuity/boundedness and
 open-strip analyticity is closed under vector operations, involution, conjugation, star, and
 multiplicative convolution,
 assumptions exactly the four displayed source-facing conditions,
 analytic congruence plus conjugate-conjugate differentiability and W1a Mellin products,
 unresolved frontier: quotient/uniqueness/completeness, explicit formula, density, positivity)
```

## Strength And Stop Audit

The endpoint is unconditional and strictly weaker than RH. It mentions no zeros, primes, or
positivity. What genuinely becomes easier is precise: the complete explicit formula can be stated
on one compiled physical test algebra, and autocorrelations are known to remain in that algebra.

Success classification: `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0` for RH. It completes W1b's
admissible-algebra core only. Metric quotient/completeness and density remain separate prerequisites
if later arguments require them.

The campaign closes `CONJECTURE_FALSIFIED` if any displayed class operation fails under these exact
conditions, or `NO_PROGRESS` if a hidden inversion/uniqueness assumption is required. Success or
failure is campaign-local; the persistent RH goal remains active.

Verification requires standalone and full builds, exact target witnesses, standard-only transitive
axiom output, empty forbidden/declaration/resource scans, `git diff --check`, and public CI.

## Local Result

The fixed endpoint compiles in `LeanLab/Riemann/WeilStripClass.lean`. The physical predicate is
closed under zero, addition, complex scalar multiplication, Weil involution, physical
conjugation, conjugate star, multiplicative convolution, and self-star autocorrelation. The
conjugation proof explicitly derives differentiability of `conj o mellin(f) o conj`; convolution
uses W1a's pointwise convergence and Mellin-product theorems, not a new closure premise.

Standalone compilation, exact TargetChecks, all 16 public transitive axiom prints, empty
forbidden-token/declaration/resource scans, `git diff --check`, and the 8,664-job full build pass.
Every new declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. Classification is
locally `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` for RH. Public commit and CI remain.
