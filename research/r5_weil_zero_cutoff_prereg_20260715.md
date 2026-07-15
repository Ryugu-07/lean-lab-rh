# R5 Weil Finite-Height Zero-Cutoff Preregistration

Campaign: `CAMPAIGN-20260715-R5-WEIL-ZERO-CUTOFF-01`

Date: 2026-07-15

Status: `PUBLICLY_CLOSED_BRIDGE_REDUCED`

## Source Boundary

Lagarias Appendix A requires a symmetric finite-height cutoff of the zero side before the limiting
explicit formula is interpreted. Burnol likewise separates the finite contour identity from the
later distributional and endpoint regularization. This campaign targets only the exact finite
rectangle identity. It does not preregister the height limit, prime-side contour estimates,
regularization, the complete class-E formula, Weil positivity, or RH.

Primary sources:

- https://www.numdam.org/item/10.5802/aif.2311.pdf
- https://arxiv.org/abs/math/9810169

## Route Map And Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: complete class-E explicit formula | Still requires Mellin inversion, horizontal-edge decay, height limits, local regularization, and covariance extension. | Reject as larger than one bounded campaign. |
| C2: finite-height weighted argument principle for xi | Existing genus-one summability and the compact-set estimate in `LiZeroFormula.lean` give the missing uniform boundary control; no RH premise is needed. | Select. |
| C3: unweighted zero count | Correct but too narrow for W1c1 and does not carry the source test transform. | Reject as a standalone endpoint. |
| C4: one weighted pole via `dslope` | Necessary engineering infrastructure, but proving one pole does not connect xi to its complete finite zero multiset. | Keep only inside C2. |
| C5: finite rational zero kernel assumed as the integrand | Merely integrates an already truncated zero expression and bypasses the actual xi logarithmic derivative. | Reject as circular for this edge. |

C2 is unconditional and strictly weaker than RH. It is a finite-height argument-principle theorem
for an entire function whose zero divisor is already known. What becomes easier is W1c1: after
this result, the remaining zero-side work is a genuine height-limit/regularization problem rather
than an unformalized exchange of an infinite Hadamard sum with four boundary integrals.

## Fixed Lean Endpoint

The implementation module will be `LeanLab/Riemann/WeilZeroCutoff.lean`.

```lean
def rectangleBoundaryIntegral (f : ℂ → ℂ) (l r b t : ℝ) : ℂ :=
  (∫ x : ℝ in l..r, f (x + b * Complex.I)) -
    (∫ x : ℝ in l..r, f (x + t * Complex.I)) +
    Complex.I * (∫ y : ℝ in b..t, f (r + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in b..t, f (l + y * Complex.I))

def riemannXiZeroStrictlyInsideRectangle
    (l r b t : ℝ) (p : RiemannXiDivisorZeroIndex) : Prop :=
  l < (riemannXiDivisorZeroValue p).re ∧
    (riemannXiDivisorZeroValue p).re < r ∧
    b < (riemannXiDivisorZeroValue p).im ∧
    (riemannXiDivisorZeroValue p).im < t

theorem summableLocallyUniformlyOn_riemannXiLogDerivZeroTerm :
    SummableLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p)
      riemannXiNonzeroSet

theorem rectangleBoundaryIntegral_weighted_cauchyKernel
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {rho : ℂ} {l r b t : ℝ}
    (hl : l < rho.re) (hr : rho.re < r)
    (hb : b < rho.im) (ht : rho.im < t) :
    rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t =
      2 * (Real.pi : ℂ) * Complex.I * F rho

theorem rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : forall p : RiemannXiDivisorZeroIndex,
      not (riemannXiZeroOnRectangleBoundary l r b t p)) :
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z) l r b t =
      2 * (Real.pi : ℂ) * Complex.I *
        finsum (fun p : RiemannXiDivisorZeroIndex =>
          if riemannXiZeroStrictlyInsideRectangle l r b t p
          then F (riemannXiDivisorZeroValue p) else 0)
```

The boundary predicate will be defined by the four closed edge segments, and the inside predicate
will remain strict. Names and harmless multiplication normalization may change to match imported
notation. The mathematical endpoint may not be weakened to an assumed finite zero sum, one pole,
the unweighted case, or an abstract uniform-summability premise.

The divisor index repeats zero values by analytic multiplicity, so the final `finsum` must retain
that index rather than deduplicate complex values.

## Adversarial Checks And Stop Conditions

- Test orientation on `F = 1` and one pole: bottom/right/top/left must give `+2*pi*I`.
- Test a pole outside each of the four sides: its boundary integral must be zero.
- Test a pole on an edge: the theorem must refuse it through `hboundary`.
- Check that the compensated constant `1/rho` and the Hadamard polynomial derivative integrate to
  zero only after multiplication by an entire `F`.
- Check that near zeros are finite and far zeros are uniformly dominated by a constant multiple of
  `norm rho ^ (-2)` on the complete boundary.
- Reject pointwise-only summability as insufficient for interchanging any boundary integral.
- Reject any use of RH, the complete explicit formula, a project axiom, `sorry`, `native_decide`,
  or a resource-limit relaxation.
- If either the actual xi splice or the four-edge integral exchange is missing, close as
  `NO_PROGRESS` or `DEPENDENCY_GAP_IDENTIFIED`; do not silently shrink the endpoint.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: W1c1 has no compiled finite-height passage from `F * logDeriv xi` to the
  multiplicity-bearing zero sum
- `hard_gap_after`: if successful, the finite-height zero-cutoff subedge of W1c1 is complete;
  height limits, prime-side contour estimates, and W1c2 regularization remain
- `hard_gap_delta`: 1 source-level W1c1 subedge if successful, 0 for RH
- `assumption_frontier_before`: W1c1 finite contour/cutoff, W1c2 regularization, W2 positivity
- `assumption_frontier_after`: W1c1 height-limit/decay, W1c2 regularization, W2 positivity
- `normalized_tuple`: `(finite-height weighted xi argument principle with multiplicity,
  entire weight and zero-free rectangle boundary, genus-one local uniform convergence plus
  weighted rectangular Cauchy kernel, height limit and regularization)`

## Verification Gate

No result may be used later until standalone and full builds, exact TargetChecks, transitive
standard-only axiom output, empty forbidden/declaration/resource scans, `git diff --check`, and
public CI all pass. Every helper belongs to this one indivisible campaign.

## Local Verification Result

The exact preregistered endpoint is proved by
`rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum`. The new module compiles without
warnings; exact target witnesses, all seven selected transitive axiom prints, empty forbidden
scans, `git diff --check`, the 8,635-job standalone module build, and the 8,667-job full build pass.
All selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Local classification is `BRIDGE_REDUCED`: the finite-height W1c1 zero-side subedge is closed.
Height limits, prime-side contour decay, W1c2 regularization, W2 positivity, and RH remain open.
Public CI is still required before final campaign closure.

The implementation commit `7e140a86b6fbe1ed410917b8ee46089bb5dff6fb` passed public Lean Action CI
run `29423254678`, build job `87378909471`, in 3m1s. The evidence-backfill commit and its own CI
remain required before final closure.

Evidence-backfill commit `626fef55bb951d1cb59a76f8ff22250c4bc3a0e2` passed public Lean Action CI
run `29423572352`, build job `87380039889`, in 1m47s. This preregistered campaign is publicly
closed as `BRIDGE_REDUCED`. The global RH Goal remains active.
