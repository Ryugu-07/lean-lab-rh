# R5 Gaussian-Weil Quadratic Positivity Preregistration

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-QUADRATIC-POSITIVITY-01`

Date: 2026-07-16

Status: `LOCAL_COMPLETE_BRIDGE_REDUCED`

## Route Boundary

The predecessor campaign proves the complete xi explicit formula for every finite complex packet
of the probes

```text
G_(a,b)(s) = exp(a * (s - 1/2)^2) * cosh(b * (s - 1/2)),
             a > 0, b real.
```

This campaign tests the first honest W2 positivity consequence of that algebraic core. Fix one
width `a > 0`, finitely many real shifts `b_i`, and finitely many real coefficients `w_i`. Apply
the packet formula to all ordered pairs with shift `b_i - b_j` and coefficient `w_i * w_j`.
Under RH, a divisor zero `rho = 1/2 + I * gamma` contributes

```text
exp(-a * gamma^2) *
  ((sum_i w_i cos(b_i gamma))^2 + (sum_i w_i sin(b_i gamma))^2).
```

The selected endpoint is the exact equality between the packet zero `tsum` and this summable
square `tsum`, the exact arithmetic explicit formula for the same packet, and nonnegativity of the
real part of the resulting arithmetic quadratic expression under RH.

Closest primary sources:

- J. C. Lagarias, Appendix A on Weil's positivity criterion and its equivalence to RH:
  https://arxiv.org/abs/math/0104132
- J. Arias de Reyna, the Gaussian/Hermite test core and the warning that the separated
  quasicrystal temperedness statement is RH-equivalent: https://arxiv.org/abs/2402.10604

No converse positivity criterion, Bochner theorem, Laplace uniqueness theorem, or temperedness
claim is imported.

## Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: fixed-width Gaussian translates are dense in even Schwartz space | Mathematically plausible, but Mathlib has no packaged Gaussian Schwartz constructor, Hermite completeness in Schwartz topology, or compactly supported smooth density theorem there. L2 density would be too weak. | Defer as a large G6 infrastructure campaign. |
| C2: extend the zero and prime functionals separately from the finite Gaussian core | Continuity or temperedness of the separated prime/zero quasicrystals is not an innocuous analytic lemma; the cited literature identifies the relevant temperedness with RH. | Reject as a hidden assumption of the target. |
| C3: unconditional positivity of the arithmetic Gaussian packet | The explicit formula alone gives equality, not sign. Unconditional sign is precisely the hard content expected from a Weil criterion. | Reject. |
| C4: RH implies finite real Gaussian-Weil quadratic positivity | On the critical line every zero contribution is an exponentially damped sum of two real squares. The completed packet theorem supplies the exact arithmetic expression and summability. A full scratch proof compiles. | Select. |
| C5: the reverse implication from this fixed-width kernel | Boundedness or positive definiteness of the bilateral-Laplace zero trace may constrain off-line zeros, but no cancellation-free uniqueness argument or supporting Mathlib theorem was found. | Reject from this campaign. |

## Pre-Admission Falsification

1. The statement is RH-forward only. No reverse implication or RH equivalence is admitted.
2. The coefficients are real. The theorem must not be advertised as a complex Hermitian PSD
   statement unless conjugate coefficients and the corresponding norm-square identity are proved.
3. The common width remains strictly positive in the arithmetic formula. The critical-line
   pointwise square identity itself may hold for every real width.
4. The exact shift orientation is `b_i - b_j`; sign changes are harmless only after an explicit
   cosine-evenness proof.
5. The zero side must be a genuine divisor-indexed `tsum`, with analytic multiplicity retained.
6. The arithmetic side must be the direct packet pole, GammaR integral, and von-Mangoldt `tsum`,
   not a newly assumed positivity functional.
7. Zero coefficients must reduce the arithmetic expression to zero. A singleton must reduce the
   zero square to `exp(-a * gamma^2) * w^2`.

## Fixed Definitions And Endpoint

Harmless naming and algebraic reassociation are allowed. The final module must expose definitions
equivalent to the following objects.

```lean
def gaussianWeilPairWidth (a : Real) : iota x iota -> Real := fun _ => a

def gaussianWeilPairShift (b : iota -> Real) : iota x iota -> Real :=
  fun q => b q.1 - b q.2

def gaussianWeilPairCoeff (w : iota -> Real) : iota x iota -> Complex :=
  fun q => (w q.1 * w q.2 : Real)

def gaussianXiZeroQuadratic (a : Real) (b w : iota -> Real) : Complex :=
  tsum fun p =>
    riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)

def gaussianXiArithmeticQuadratic
    (a : Real) (b w : iota -> Real) (c : Real) : Complex :=
  2 * Real.pi * packetPole + packetArchimedeanIntegral - tsum packetPrime
```

The indivisible final endpoint is:

```lean
theorem RiemannHypothesis.gaussianXiZeroQuadratic_eq_tsum_sq_add_sq ...

theorem gaussianXiZeroQuadratic_arithmetic_formula
    (ha : 0 < a) (hc : 1 < c) ... :
    Real.pi * gaussianXiZeroQuadratic a b w =
      gaussianXiArithmeticQuadratic a b w c

theorem RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg
    (ha : 0 < a) (hc : 1 < c) ... :
    0 <= (gaussianXiArithmeticQuadratic a b w c).re
```

The first theorem must identify every zero term with

```text
exp(-a * gamma_p^2) *
  ((sum_i w_i cos(b_i gamma_p))^2 + (sum_i w_i sin(b_i gamma_p))^2)
```

and prove that this real family is summable.

## Proof DAG

1. Under RH, rewrite each multiplicity-bearing xi divisor zero as having real part `1/2`.
2. Evaluate the symmetric Gaussian weight there as `exp(-a * gamma^2) * cos(b * gamma)`.
3. Expand the ordered-pair packet and prove the finite cosine-difference Gram identity.
4. Transport absolute summability from the compiled packet zero family to the real square family.
5. Commute the real embedding with `tsum` and prove exact zero-side equality and nonnegativity.
6. Instantiate the packet explicit formula with pair widths, shifts, and coefficients.
7. Take real parts and combine the positive factor `Real.pi` with zero-side nonnegativity.
8. Audit zero coefficients, singleton coefficients, and all selected declarations.

## Stop Conditions

- Do not weaken the endpoint to a finite algebraic identity without the divisor `tsum`.
- Do not omit the direct arithmetic pole, GammaR, or von-Mangoldt terms.
- Do not state unconditional arithmetic positivity.
- Do not infer the reverse implication or claim progress on RH itself.
- Do not replace Schwartz continuity by L2 density.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe/opaque declaration, or
  resource-limit relaxation.
- If the exact square `tsum` and the arithmetic nonnegativity theorem fail under two independent
  proof approaches, classify the local campaign as `NO_PROGRESS` and return to route selection.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: a finite Gaussian explicit-formula test core with no compiled W2 sign theorem
- `hard_gap_after`: if successful, an exact RH-forward positive quadratic kernel on every finite
  real Gaussian shift packet, expressed arithmetically
- `hard_gap_delta`: one conditional W2 kernel bridge; zero for unconditional positivity, the
  converse Weil criterion, Schwartz closure, separated temperedness, and RH
- `assumption_frontier_after`: unconditional arithmetic sign, a converse/density theorem,
  Schwartz continuity, regularization, the full Weil criterion, and RH remain
- `expected_classification`: `BRIDGE_REDUCED`

## Verification Gate

No theorem becomes a later premise until the standalone module, exact Targets and TargetChecks,
selected transitive axiom prints, forbidden token/declaration/resource scans, `git diff --check`,
full project build, public commit, and public CI all pass.

## Local Outcome

Proof Attempt A reaches the complete fixed endpoint in
`WeilGaussianQuadraticPositivity.lean`. Under RH, the critical-line Gaussian evaluation and the
finite cosine-difference Gram identity give an exact pointwise square formula. Lean transports
absolute summability from the direct packet zero family to the real square family and proves the
exact divisor-indexed `tsum` equality. The unconditional packet explicit formula then identifies
the same zero quadratic with the direct pole, GammaR, and von-Mangoldt arithmetic expression;
taking real parts proves its nonnegativity under RH.

The singleton square term and zero-coefficient arithmetic expression reduce exactly. The
warning-free standalone module, Targets, exact TargetChecks, seven selected axiom prints, empty
forbidden scans, `git diff --check`, and the 8,673-job full build pass. Every selected declaration
uses only `propext`, `Classical.choice`, and `Quot.sound`. Classification is locally
`BRIDGE_REDUCED`; publication evidence remains before closure.

Implementation commit `cf271684f786efcb2e83a57d76c51e215205d1d1` passed public Lean Action CI
run `29447980403`, build job `87463120301`, in `1m49s`. Immutable evidence backfill and that
commit's own public CI remain before closure.
