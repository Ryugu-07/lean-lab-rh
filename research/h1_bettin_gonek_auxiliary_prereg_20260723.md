# H1 Bettin--Gonek Auxiliary Regularization Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Parent and source

- Parent final ledger: `d4196d0f47d42f1c95d29b48dd341b9a469c514b`.
- Parent public CI: run `29968166845`, build job `89084084918`, passed in `1m54s`.
- Selected node: `H1-BETTIN-GONEK-AUXILIARY-REGULARIZATION-01`.
- Source: Bettin--Gonek, arXiv:1604.02740, Section 2, especially equations `(2.2)` and `(2.3)`.
- Global RH Goal: active.

## Exact target

Create `LeanLab/Riemann/BettinGonekAuxiliary.lean` and define:

```lean
bettinGonekShiftedArgument (t : Real) (w : Complex) : Complex
bettinGonekSelectedPole (rho : Complex) (t : Real) : Complex
bettinGonekCancelledZeta (rho s : Complex) : Complex
bettinGonekAuxiliaryG (rho : Complex) (t : Real) (w : Complex) : Complex
bettinGonekJKernel (rho : Complex) (t x : Real) (w : Complex) : Complex
bettinGonekResidueCoefficient (rho : Complex) (t x : Real) : Complex
```

The cancellation object must be `dslope zetaPoleRemoved rho`, not totalized raw division. For a
nontrivial zero `rho`, prove:

1. `zetaPoleRemoved rho = 0`.
2. Away from `s=rho` and `s=1`, the cancelled object equals
   `(s-1) * riemannZeta s / (s-rho)`.
3. The regularized `G_t` equals the raw Bettin--Gonek formula away from the patched points.
4. The regularized `G_t` is complex differentiable on the open neighborhood
   `{w | -1 < w.re}`, which contains the source half-plane `Re(w) >= 0` and excludes the two
   rational denominator poles with real part `-1`.
5. For `x>0`, the selected-zero pole of `bettinGonekJKernel` has the exact coefficient displayed
   in the source, expressed by a punctured-neighborhood limit of
   `(w - bettinGonekSelectedPole rho t) * bettinGonekJKernel rho t x w`.
6. That coefficient is nonzero for every nontrivial zero and every `x>0`.

## Acceptance statements

The exact theorem names may follow local style, but `TargetChecks.lean` must witness statements
equivalent to:

```lean
theorem bettinGonekCancelledZeta_eq_source
    {rho s : Complex} (hrho : IsNontrivialZero rho)
    (hsrho : s ≠ rho) (hsone : s ≠ 1) :
    bettinGonekCancelledZeta rho s =
      (s - 1) * riemannZeta s / (s - rho)

theorem differentiableOn_bettinGonekAuxiliaryG
    {rho : Complex} (hrho : IsNontrivialZero rho) (t : Real) :
    DifferentiableOn Complex (bettinGonekAuxiliaryG rho t)
      {w | -1 < w.re}

theorem tendsto_bettinGonekJKernel_selectedPole
    {rho : Complex} (hrho : IsNontrivialZero rho) (t : Real)
    {x : Real} (hx : 0 < x) :
    Tendsto
      (fun w => (w - bettinGonekSelectedPole rho t) *
        bettinGonekJKernel rho t x w)
      (nhdsWithin (bettinGonekSelectedPole rho t)
        {bettinGonekSelectedPole rho t}^c)
      (nhds (bettinGonekResidueCoefficient rho t x))

theorem bettinGonekResidueCoefficient_ne_zero
    {rho : Complex} (hrho : IsNontrivialZero rho) (t : Real)
    {x : Real} (hx : 0 < x) :
    bettinGonekResidueCoefficient rho t x ≠ 0
```

## Claim limits

This campaign does not prove:

- the Mellin identity for `H_t`;
- the inverse Mellin support or uniform bound for `g_t`;
- the vertical decay estimate for `G_t`;
- any contour-shift integral equality;
- the convolution identity for `J_t`;
- the Cauchy--Schwarz and zeta second-moment lower-bound chain;
- `BettinGonekMomentToPowerBridge`;
- `FarmerThetaInfinityConjecture`;
- RH.

The existing open bridge and moment Targets remain open with no `leanName` and may not be used as
premises.

## Outcomes and stop rule

- `FULL_SUCCESS_AT_AUXILIARY_ENDPOINT`: all six exact target items compile, including the
  punctured-neighborhood coefficient and nonvanishing.
- `MEANINGFUL_PARTIAL`: the `dslope` cancellation and source equality compile, but a precise
  Mathlib API gap blocks differentiability or the punctured-neighborhood limit.
- `SOURCE_REGULARIZATION_MISMATCH`: the displayed source quotient has an additional singularity
  or the claimed pole coefficient differs after exact substitution.
- `NO_PROGRESS`: no exact source equality can be stated without changing the source object.

Stop at one outcome. Success opens a separately preregistered campaign on decay/contour or on the
Mellin convolution identity. Failure records the exact obstruction and returns to graph-ranked
historical selection. Closing this campaign does not exhaust H1.

## Mechanical gates

Publish this preregistration and require public Lean Action CI before creating the production
module. Then require no-sorry production source, exact Targets and TargetChecks, selected
transitive axiom prints, an empty forbidden scan, direct compiles, `git diff --check`, a full
build, frozen implementation CI, immutable evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Runtime disclosure

- Model: Codex, GPT-5 family; exact serving variant not exposed.
- Reasoning effort: not exposed.
- Numerical loop quota: none under V4.1; serving token budget not exposed.
- Compaction: the inherited summary was used to resume H1 closure; the source TeX, current atlas,
  H1 card, parent preregistration, parent production module, Targets, and available removable
  singularity APIs were re-read before this selection.
