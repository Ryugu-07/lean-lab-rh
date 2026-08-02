# H12 x H1 Low-Zero Paired-Mass Preregistration

Date: 2026-08-02

Campaign: `PROOF-ATTEMPT-20260802-H12-H1-LOW-ZERO-MASS-01`

Parent subattack: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Primary mode: `LITERATURE / PROOF-ATTEMPT / HISTORICAL-OMISSION`

Status: `PREREGISTERED / DOCS-ONLY PUBLIC GATE PENDING / GLOBAL_GOAL_ACTIVE`

## Source hinge

Levinson--Montgomery equation `(2.1)` expresses the real logarithmic derivative as an
archimedean term plus a convergent multiplicity-bearing paired-zero sum. The previous structural
left-boundary proof replaced the complete sum by the upper bound zero. That succeeds for `y>=7`
but loses the sign at `y=13/2`.

The project already compiles the exact equation, the actual xi divisor with multiplicity, and
Hardy's real critical-line sign consumer. The source-level omission test is whether retaining only
one low critical-line zero supplies the missing negative mass.

Primary anchors:

- Levinson and Montgomery, *Zeros of the derivatives of the Riemann zeta-function*, Section 2,
  equation `(2.1)` and the low-height discussion on page 53;
- Hardy's critical-line sign-change mechanism, represented by the compiled
  `HardyXiBracketsZero` consumer;
- the Titchmarsh--Riemann--Siegel critical-line identity already compiled in the project.

## Exact mathematical target

Let

```text
A(y) = levinsonMontgomeryLogDerivArchimedeanTerm(i*y).
```

For every `13/2<=y<=7`, prove

```text
A(y) < 3/500.
```

If `rho=1/2+i*gamma` is a nontrivial zero with `14<=gamma<=15`, isolate one actual divisor-index
term and prove

```text
levinsonMontgomeryRealPairedZeroSum(i*y) <= -1/145.
```

The remaining paired terms are nonpositive. Since `3/500<1/145`, equation `(2.1)` then gives

```text
Re(zeta'/zeta)(i*y) < 0
```

throughout `[13/2,7]`, hence the rotated quotient lies in `Complex.slitPlane`.

Finally prove the actual producer

```text
HardyXiBracketsZero 14 15
```

from kernel-checked endpoint signs. The compiled intermediate-value consumer then supplies the
required `gamma` and closes the residual interval without a continuum quotient table.

## Proposed Lean spine

The intended production module is
`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftLowZeroMass.lean`. Names may change only for
elaboration or namespace reasons.

```lean
theorem levinsonMontgomeryArchimedean_imaginaryAxis_lt_three_div_fiveHundred
    {y : ℝ} (hy0 : 13 / 2 <= y) (hy1 : y <= 7) :
    levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) < 3 / 500

theorem levinsonMontgomeryRealPairedZeroSum_le_neg_one_div_oneFortyFive_of_lowCriticalZero
    {y gamma : ℝ} (hy0 : 13 / 2 <= y) (hy1 : y <= 7)
    (hgamma0 : 14 <= gamma) (hgamma1 : gamma <= 15)
    (hzero : IsNontrivialZero (hardyCriticalLinePoint gamma)) :
    levinsonMontgomeryRealPairedZeroSum ((y : ℂ) * I) <= -1 / 145

theorem speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_of_hardyXiBracket
    (hbracket : HardyXiBracketsZero 14 15)
    {y : ℝ} (hy0 : 13 / 2 <= y) (hy1 : y <= 7) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).re < 0

theorem hardyXi_bracketsZero_fourteen_fifteen :
    HardyXiBracketsZero 14 15

theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_thirteenHalves_seven
    {y : ℝ} (hy0 : 13 / 2 <= y) (hy1 : y <= 7) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane
```

## Success and falsification criteria

- `full_success`: all five displayed outputs compile, with the low-zero bracket derived from
  actual endpoint evaluations and the residual interval closed.
- `meaningful_partial`: the uniform paired-mass consumer compiles and reduces the entire interval
  to the exact two-point proposition `HardyXiBracketsZero 14 15`, while the endpoint evaluator is
  reduced to one named analytic or transcendental obstruction.
- `falsification`: a checked inequality shows that one zero in `[14,15]` cannot dominate the
  archimedean upper, or a kernel-checked endpoint evaluation disproves the proposed bracket
  orientation. Repartition or restore the direct evaluator; do not alter constants merely to
  preserve the campaign.
- `no_progress`: the actual divisor term cannot be isolated from the convergent sum without an
  unproved enumeration premise, or neither existing endpoint backend can express the Hardy-xi
  signs after bounded source-faithful work. Record the exact API or analytic boundary and rerank.

## Assumption and claim boundary

The conditional interval consumer may assume only the explicit critical-line zero or the exact
`HardyXiBracketsZero 14 15`. That assumption cannot become a downstream premise until the actual
bracket theorem compiles.

Navigation values, `mpmath`, external zero tables, decimal approximations, and imported booleans
are forbidden as premises. Rational centers must be justified by proved transcendental
enclosures. No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or relaxed
resource option is permitted.

Even full success closes only the left residual interval `[13/2,7]`. The left low/middle zones,
right low/middle zones, compact-middle top, complete height-ten certificate, H12, and RH remain
separate until their exact declarations compile.

## Runtime

- model: Codex, GPT-5 family; exact serving variant is not exposed;
- reasoning effort: not exposed;
- numerical loop budget: none under V4.1;
- compaction: resumed from the immutable reflected-evaluator checkpoint, then re-read canonical
  governance, HANDOFF, the ranked historical atlas, active attempts, hard-gap DAG, complete-boundary
  preregistration, and source modules before route selection;
- global Goal: active.

## Production gate

Commit this preregistration, route-selection record, attempt entry, and DAG update without Lean
production edits. Public Lean Action must pass before the new production module or registries are
edited.
