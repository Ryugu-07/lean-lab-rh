# R5 Weil Convolution Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-R5-WEIL-CONVOLUTION-01`

Mode: `ROUTE_MAP -> CONJECTURE_GENERATION -> ADVERSARIAL_TEST -> FORMALIZATION -> INDEPENDENT_AUDIT`

Route family: R5, explicit formula and test-function positivity.

## Independent Evidence For Same-Route Continuation

Discovery Protocol V3 normally switches route after closure. Continuing R5 is admitted here only
because an independent source and library audit identifies the next exact edge, distinct from the
closed involution tuple:

- Lagarias, Appendix A, formula (A.7), defines Weil's covariance pairing through
  `W[f * conjugate(tilde(g))]` and writes its spectral factor as the product of the two Mellin
  transforms.
- Pinned Mathlib has the additive Bochner-convolution theorem `integral_convolution`, including
  the product-integrability/Fubini machinery, but has no multiplicative Mellin-convolution product
  theorem.
- `WeilTestAlgebra.lean` already fixes the source's involution and conjugation conventions, so the
  remaining algebraic edge is now exact rather than speculative.

This evidence admits one same-route campaign. It does not admit the explicit formula or positivity.

## Fixed Endpoint

For complex-valued functions on the positive half-line, define source-faithful multiplicative
convolution

```lean
def weilConvolution (f g : Real -> Complex) (x : Real) : Complex :=
  integral y in Set.Ioi 0, f y * g (x / y) / (y : Complex)
```

The indivisible endpoint is:

```lean
theorem mellinConvergent_weilConvolution
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (weilConvolution f g) s

theorem mellin_weilConvolution
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (weilConvolution f g) s = mellin f s * mellin g s

theorem mellin_weilConvolution_star
    (hf : MellinConvergent f s)
    (hg : MellinConvergent g (1 - conj s)) :
    mellin (weilConvolution f (weilStar g)) s =
      mellin f s * conj (mellin g (1 - conj s))

theorem mellin_weilConvolution_star_criticalLine
    (hf : MellinConvergent f (1 / 2 + t * I))
    (hg : MellinConvergent g (1 / 2 + t * I)) :
    mellin (weilConvolution f (weilStar g)) (1 / 2 + t * I) =
      mellin f (1 / 2 + t * I) * conj (mellin g (1 / 2 + t * I))
```

Minor elaboration changes are allowed; assumptions and mathematical content may not be weakened.
The proof must pass through a real logarithmic-coordinate representation and justify Fubini from
the two displayed convergence assumptions. A transform-value equality without the convergence
theorem does not close the campaign.

## Candidate Generation And Adversarial Tests

At most five candidates were screened.

### C1: complete Riemann-Weil explicit formula

Correct fixed W1 frontier, but still requires the zero distribution, prime sum, pole terms,
archimedean gamma term, contour shift, and regularization in one batch. Deferred as oversized.

### C2: complete Lagarias `A_delta` Banach algebra

This requires strip analyticity, boundary continuity, a uniform strip norm, and completeness in
addition to convolution. It is a valid later edge, but proving only closure before the underlying
Mellin product theorem would invert the dependency order. Deferred.

### C3: generic convergent multiplicative Mellin convolution

Selected. It is the exact analytic content used to pass from the physical convolution in (A.7) to
the product on the spectral side, and its assumptions are expressible by Mathlib's existing
`MellinConvergent` predicate.

### C4: compactly supported smooth test functions only

Rejected as the endpoint. Such a subclass makes integrability easy but no compiled density theorem
transfers it to Lagarias's admissible strip class. It may be an example after the generic theorem,
not a substitute for it.

### C5: define the Weil quadratic form directly by a zero sum

Rejected at this stage. This would bypass, rather than prove, the physical/spectral covariance and
would require the still-open distributional convergence and explicit-formula blocks.

Boundary and falsification tests for C3:

- no unconditional product identity: nonintegrable Bochner integrals can each evaluate to zero;
- no inference of strip analyticity from convergence at one `s`;
- the `dy/y` Jacobian must be present exactly;
- under logarithmic coordinates `x=exp(-w)`, multiplicative convolution must become additive
  convolution with the correct `w-u` direction;
- conjugation sends `s` to `conj(s)`, and the involution then sends it to `1-conj(s)`;
- on `Re(s)=1/2`, the star factor must be `conj(mellin g s)`, not `mellin g s`;
- values at nonpositive `x` are outside the Mellin domain and may not be used to claim a whole-real
  group law.

Normalized tuple:

```text
(MellinConvergent f s and MellinConvergent g s imply convergence and
 M(f *_M g)(s)=M(f)(s)M(g)(s),
 assumptions exactly pointwise Mellin convergence at s,
 logarithmic-coordinate reduction to Mathlib additive Bochner convolution and Fubini,
 unresolved frontier: analytic-strip test class plus zero/prime/pole/archimedean explicit formula)
```

## Strength And Stop Audit

The endpoint is unconditional and strictly weaker than RH. It mentions neither zeta zeros nor
primes nor positivity. What becomes easier is exact: a later Weil distribution can consume a
compiled physical autocorrelation whose spectral value is a Hermitian product, without silently
assuming Fubini or convergence.

Success classification: `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0` for RH. The W1 convolution
subedge is reduced, but the source-faithful analytic test class and complete explicit formula
remain open.

The campaign closes `CONJECTURE_FALSIFIED` if the displayed convergence assumptions do not suffice,
or `NO_PROGRESS` if the source formula requires an additional hidden premise. Success or failure
is campaign-local; the persistent RH goal remains active.

Verification requires standalone and full builds, exact target witnesses, standard-only transitive
axiom output, empty forbidden/declaration/resource scans, `git diff --check`, and public CI.

## Local Result

Date: 2026-07-15

All preregistered propositions compile in `LeanLab/Riemann/WeilConvolution.lean`. The proof defines
the exact physical integral with `dy/y`, proves that `x=exp(-w)` sends it to additive convolution,
and applies Mathlib's `integral_convolution` only after converting both `MellinConvergent`
hypotheses into integrability of the logarithmic lifts.

The independent audit added the self-star endpoint

```lean
theorem mellin_weilAutocorrelation_criticalLine {f : Real -> Complex} (t : Real)
    (hf : MellinConvergent f (1 / 2 + t * I)) :
    mellin (weilConvolution f (weilStar f)) (1 / 2 + t * I) =
      Complex.normSq (mellin f (1 / 2 + t * I))
```

This checks the final conjugation direction used by Weil's covariance form. Classification is
`KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0` for RH. W1a is complete; W1b's analytic-strip class,
W1c's complete explicit formula, W2 positivity, and RH remain open. Standalone and exact target
builds, standard-only axiom output, forbidden scans, `git diff --check`, and the 8,663-job full
build pass locally. The persistent RH goal remains active.

Implementation commit `90874a87a89ee371719c2f50f5cc02eaae8a5040` passed public Lean Action CI
run `29410786209`, build job `87337104802`, in 1m46s. Evidence-backfill commit
`30a816118acf74a0ab9bead03b7541d6929dcfe3` passed public run `29410987990`, build job
`87337750370`, in 1m29s. The campaign is publicly closed and returns to route selection.
