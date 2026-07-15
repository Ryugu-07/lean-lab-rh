# R5 Weil Test Algebra Preregistration

Date: 2026-07-15

Campaign: `CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01`

Mode: `ROUTE_MAP -> CONJECTURE_GENERATION -> ADVERSARIAL_TEST -> FORMALIZATION -> INDEPENDENT_AUDIT`

Route family: R5, explicit formula and test-function positivity.

## Fixed Gap And Indivisible Endpoint

The preceding R3 campaign compiled the exact Li criterion and is closed. Discovery Protocol V3
therefore requires a different route family. The fixed R5 frontier is a source-faithful Weil
explicit formula with zero, finite-prime, pole, and archimedean terms on a test class stable under
multiplicative convolution and involution.

This first R5 campaign does not claim the explicit formula. It is admitted only as one indivisible
formalization of the exact test-function involution in Lagarias, Appendix A, formulas (A.1)-(A.2):

```lean
def weilInvolution (f : Real -> Complex) (x : Real) : Complex :=
  (x : Complex) ^ (-1 : Complex) * f x⁻¹

theorem weilInvolution_involution_of_pos
    (f : Real -> Complex) {x : Real} (hx : 0 < x) :
    weilInvolution (weilInvolution f) x = f x

theorem mellin_weilInvolution (f : Real -> Complex) (s : Complex) :
    mellin (weilInvolution f) s = mellin f (1 - s)

theorem mellin_weilInvolution_zero (f : Real -> Complex) :
    mellin (weilInvolution f) 0 = mellin f 1

theorem mellin_weilInvolution_one (f : Real -> Complex) :
    mellin (weilInvolution f) 1 = mellin f 0
```

The batch must also define the conjugate involution used in the Weil covariance form and prove its
Mellin transform and critical-line specialization:

```lean
def weilStar (f : Real -> Complex) (x : Real) : Complex :=
  conj (weilInvolution f x)

theorem mellin_weilStar (f : Real -> Complex) (s : Complex) :
    mellin (weilStar f) s = conj (mellin f (1 - conj s))

theorem mellin_weilStar_criticalLine (f : Real -> Complex) (t : Real) :
    mellin (weilStar f) (1 / 2 + t * I) =
      conj (mellin f (1 / 2 + t * I))
```

Minor syntactic changes needed by elaboration are allowed, but the mathematical propositions may
not be weakened. The endpoint is one known test-algebra result; helper lemmas do not count as
separate research loops.

## Source Reconstruction

- Jeffrey C. Lagarias, *Li Coefficients for Automorphic L-Functions*, Annales de l'Institut
  Fourier 57 (2007), 1689-1740, DOI `10.5802/aif.2311`, Appendix A, defines
  `f_tilde(x)=x^(-1) f(x^(-1))` and states `M(f_tilde)(s)=M(f)(1-s)`. Formulas (A.3)-(A.7) then
  use this involution in the Weil distribution and covariance form.
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*, arXiv `1910.14368`, Section 4,
  records the compact-support autocorrelation framework, the two moment constraints, and labels
  the proposed semi-local positivity mechanism as Conjecture 4.1.
- Masatoshi Suzuki, *Li Coefficients as Norms of Functions in a Model Space*, arXiv `2301.05779`,
  treats Li norm formulas as a Weil-type RH criterion. It is evidence for the Li/Weil relation,
  not an unconditional positivity theorem.

## Candidate Generation And Falsification

At most five candidates were considered.

### C1: complete Guinand-Weil explicit formula

Proposed result: formalize the full zero/prime/pole/archimedean equality on compactly supported
smooth multiplicative test functions.

Adversarial audit: this is the correct R5 frontier, but it simultaneously requires a completed-xi
logarithmic derivative, contour shift across every zero with multiplicity, von Mangoldt expansion,
gamma-factor transform, and all limiting arguments. No corresponding theorem exists in the pinned
Mathlib or project.

Decision: deferred as the multi-campaign frontier, not weakened.

### C2: Li-special Weil family

Proposed result: use Lagarias's rational Li test functions and identify the Weil form with the
already compiled Li coefficients.

Adversarial audit: these functions require a cutoff covariance formula because their endpoint
moments diverge. More importantly, this immediately repackages the just-closed R3 criterion rather
than switching route.

Decision: rejected for anti-cycling.

### C3: Connes-Consani semi-local positivity

Proposed result: prove that primes below the support cutoff suffice for the full Weil inequality.

Adversarial audit: the source itself labels this Conjecture 4.1 and explains why the preceding local
operator inequality fails. Treating it as a premise would insert the hard positivity step.

Decision: rejected as an unproved RH-strength mechanism.

### C4: finite test-family positivity

Proposed result: verify the arithmetic side for finitely many compactly supported test functions.

Adversarial audit: no finite family is dense by itself, and no quantitative closure theorem would
transfer finite positivity to the complete Weil class. It would be numerical or finite evidence,
not an RH bridge.

Decision: rejected as non-progress for the fixed frontier.

### C5: exact Weil involution and conjugate-star Mellin covariance

Proposed result: compile the indivisible endpoint above using Mathlib's actual Mellin integral,
not an abstract transform variable.

Adversarial tests:

- `x=0`: the pointwise involution is not the identity unless `f 0=0`; the theorem must be stated on
  `0<x`, while Mellin integrals naturally restrict to that domain.
- `s=0` and `s=1`: the transform identity must swap the two endpoint moments exactly.
- complex `s`: conjugation changes `s` to `conj s`; omitting this produces a false star formula.
- `Re(s)=1/2`: `1-conj(s)=s`, so the star transform must specialize to complex conjugation at the
  same spectral point.
- divergent Mellin integrals: Mathlib's integral convention makes the algebraic transform identity
  meaningful without adding a hidden convergence premise; no later explicit-formula theorem may
  infer convergence from this convention.

Decision: **SELECTED**. It is a published exact subedge, is needed by the R5 test algebra, and does
not claim positivity or an explicit formula.

Normalized tuple:

```text
(Lagarias (A.1)-(A.2) plus conjugate-star critical-line specialization,
 no assumptions beyond x>0 for pointwise involutivity,
 Mathlib Mellin change of variables and conjugation of the Bochner integral,
 full multiplicative convolution closure and the zero/prime/archimedean explicit formula)
```

## Strength Audit

The selected endpoint is unconditional and strictly weaker than RH. It does not mention zeta zeros,
primes, positivity, or density. What becomes easier is precise: later convolution and covariance
formulas can use a compiled involution with the correct `1-s` and `1-conj(s)` conventions, and the
two moment constraints can be transported without redoing a change-of-variables proof.

The remaining R5 frontier after success is:

1. multiplicative convolution closure and the Mellin product theorem on a source-faithful class;
2. the complete explicit formula, including all convergence and regularization choices;
3. the exact Weil quadratic form and its RH-equivalent positivity/density theorem;
4. an unconditional positivity mechanism, which remains the genuine RH-hard edge.

Novelty classification if successful: `KNOWN_THEOREM_FORMALIZED` with `hard_gap_delta=0`.

## Stop And Verification Conditions

The campaign succeeds only if every displayed theorem compiles together and the transitive axiom
audit is clean. A false conjugation or endpoint identity closes `CONJECTURE_FALSIFIED`; inability to
prove the source statement without adding convergence or nonzero assumptions closes `NO_PROGRESS`.

Success or failure is campaign-local. The persistent RH goal remains active and returns to
`INDEPENDENT_AUDIT -> ROUTE_SELECTION` after closure.

Verification gates:

1. standalone and integrated Lean builds pass with no `sorry`;
2. exact target checks compile;
3. `#print axioms` contains only standard audited dependencies;
4. forbidden-token, explicit-axiom, `native_decide`, placeholder, and resource-relaxation scans pass;
5. `git diff --check` passes;
6. logs retain `hard_gap_delta=0` and do not describe this algebra as an explicit formula.

## Local Result

Date: 2026-07-15

All preregistered propositions compile in `LeanLab/Riemann/WeilTestAlgebra.lean`. The implementation
uses Mathlib's actual Mellin integral and proves the exact source direction
`M(f_tilde)(s)=M(f)(1-s)`. The conjugate involution satisfies
`M(f_star)(s)=conj(M(f)(1-conj(s)))`, and Lean verifies that `1-conj(1/2+it)=1/2+it`.

The independent audit strengthened the endpoint with

```lean
theorem mellinConvergent_weilInvolution_iff (f : Real -> Complex) (s : Complex) :
    MellinConvergent (weilInvolution f) s <-> MellinConvergent f (1 - s)

theorem mellinConvergent_weilStar_iff (f : Real -> Complex) (s : Complex) :
    MellinConvergent (weilStar f) s <-> MellinConvergent f (1 - conj s)
```

and the boundary counterexample `weilInvolution_involution_not_at_zero`. These distinguish analytic
convergence from the convention that a nonintegrable Bochner integral has value zero.

Classification: `KNOWN_THEOREM_FORMALIZED`, `hard_gap_delta=0`. The complete multiplicative
convolution theorem, source-faithful test class, zero/prime/pole/archimedean explicit formula,
density theorem, and unconditional Weil positivity all remain open. No statement of RH or its
negation is derived. Standalone compilation, exact target checks, selected standard-only axiom
output, the 8,662-job full build, forbidden scans, and `git diff --check` pass locally. The
persistent RH goal remains active. Implementation commit
`24621330af4a24269a1748c5b3a4f924c16a7768` passed public Lean Action CI run `29409014307`, build
job `87331366564`, in 2m27s. Evidence-backfill commit
`1c9e7fe27536bda8e04aa7e7bda2af1d110fe61c` passed public run `29409249934`, build job
`87332127195`, in 1m33s. The campaign is publicly closed and returns to route selection.
