# H12 Speiser Admissible-Contour Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Node: `H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Primary source and fixed inference

The fixed source is Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the
Riemann zeta-function*, Acta Mathematica 133 (1974), 49--65, Theorem 1 and section 2:

<https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf>

The source proves that the multiplicity-bearing upper-left counts of `zeta` and `zeta'` differ
by `O(log T)` and proves an exact-count/dense-count alternative. The existing project consumer
shows that those two outputs imply the exact Speiser equivalence. The present campaign attacks
the missing analytic production of those outputs.

The materially new attack angle is to remove the source's low-zero-table use at the fixed
bottom `t=10`. A bottom horizontal segment that is free of both zeta and derivative zeros has
fixed logarithmic-derivative integrals. Their norms are constants independent of the top height,
so no bottom sign is needed for an `O(log T)` count comparison.

No claim of historical novelty is made for changing a fixed contour base. The test is whether
this weakening closes the exact formal dependency that currently blocks the source proof.

## M0 definition alignment

1. `zeta` is Mathlib's `riemannZeta`; `zeta'` is `deriv riemannZeta`.
2. The horizontal segment at height `t` is
   `{sigma + t*I | 0 <= sigma <= 1/2}`. Both endpoints are included because contour
   nonvanishing is a boundary condition.
3. `SpeiserCommonZeroFreeHorizontal t` means `0<t` and pointwise nonvanishing of both actual
   functions on that closed segment. It does not assert a sign of either logarithmic derivative.
4. Zeta zeros at positive height in this segment are nontrivial zeros, with analytic
   multiplicity `burnolZetaZeroMultiplicity`. Derivative zeros use
   `riemannZetaDerivZeroMultiplicity`.
5. Bounded rectangles use the already compiled locally finite xi/zeta and derivative divisors.
   The pole `s=1` lies outside `0<=Re(s)<=1/2`.
6. The source counts use the open region `0<Re(s)<1/2`; horizontal boundary nonvanishing is
   auxiliary contour data and does not change the count convention.
7. A fixed-bottom bound is an existential nonnegative real constant bounding the two fixed
   interval integrals. It is not an asymptotic estimate and carries no RH content.
8. `LevinsonMontgomeryLogCountBound` and `LevinsonMontgomeryCountDichotomy` retain their existing
   project definitions. No new equivalent criterion is introduced.

## Proposed Lean spine

The first exact definitions and theorem targets are:

```lean
def SpeiserCommonZeroFreeHorizontal (t : Real) : Prop :=
  0 < t ∧
    ∀ sigma : Real, sigma ∈ Set.Icc (0 : Real) (1 / 2) →
      riemannZeta (sigma + t * Complex.I) ≠ 0 ∧
        deriv riemannZeta (sigma + t * Complex.I) ≠ 0

theorem exists_speiserCommonZeroFreeHorizontal_between
    {a b : Real} (ha : 0 < a) (hab : a < b) :
    ∃ t : Real, t ∈ Set.Ioo a b ∧ SpeiserCommonZeroFreeHorizontal t

theorem exists_speiserCommonZeroFreeHorizontal_above (B : Real) :
    ∃ t : Real, B < t ∧ SpeiserCommonZeroFreeHorizontal t
```

The fixed-bottom theorem must use the actual interval integrals:

```lean
theorem exists_speiserFixedBottomLogDerivBound
    {b : Real} (hb : SpeiserCommonZeroFreeHorizontal b) :
    ∃ C : Real, 0 <= C ∧
      norm (∫ sigma in (0 : Real)..(1 / 2),
        logDeriv riemannZeta (sigma + b * Complex.I)) +
      norm (∫ sigma in (0 : Real)..(1 / 2),
        logDeriv (deriv riemannZeta) (sigma + b * Complex.I)) <= C
```

The full endpoint is:

```lean
theorem levinsonMontgomeryTheoremOne_actual :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy
```

The final theorem is an open target, not an allowed premise.

## Success criteria

`FULL_SUCCESS` requires:

1. common zero-free slices in every positive-height interval and cofinally;
2. actual zeta and derivative logarithmic-derivative interval integrability on a selected slice;
3. a fixed-bottom bound independent of the variable top height;
4. finite, multiplicity-bearing critical-line indentations compatible with the compiled local
   negative-log-derivative theorem;
5. an exact indented argument-principle count identity for the two actual divisors;
6. the literal `O(log T)` count bound and source dichotomy;
7. exact TargetChecks, selected axiom prints, forbidden scans, and a full build.

`MEANINGFUL_PARTIAL` requires items 1--3, plus the first unproved statement among items 4--6
recorded in theorem-shaped form with no surrogate theorem presented as the global result.

## Falsification criteria

The fixed-bottom weakening fails if any of the following is proved:

- local finiteness does not provide a common horizontal slice because one zero set has a
  continuum of bad imaginary parts;
- nonvanishing of `zeta'` cannot be established on a compact slice away from the pole;
- the bottom logarithmic-derivative integrals require a source sign rather than mere
  nonvanishing for finiteness;
- the source count identity uses the sign at `t=10` in an essential topological orientation,
  not only as a fixed boundary contribution;
- the existing count predicates do not match the source multiplicity or boundary convention.

## Known obstacles and nearest attempts

- `LevinsonMontgomeryPairedMassDensity.lean`,
  `LevinsonMontgomeryLogDerivMassBridge.lean`,
  `LevinsonMontgomeryBoundarySigns.lean`, and
  `LevinsonMontgomeryCriticalIndentation.lean` compile the source's zero-mass, boundary
  alternative, and local critical-zero indentation mechanisms.
- `SpeiserCountingEquivalence.lean` compiles the exact logical consumer but leaves
  `LevinsonMontgomeryLogCountBound` and `LevinsonMontgomeryCountDichotomy` open.
- `WeilZeroCutoff.lean` contains a xi-specific rectangle argument principle based on the
  compiled Hadamard zero sum. There is no ready generic rectangle argument principle for
  `deriv riemannZeta`.
- The source's `t=10` sign proof uses low-zero verification. Such a table is prohibited as an
  unproved premise in this campaign.

## Attack plan

### Attack A: finite bad-height projection

Use compact local finiteness for the actual zeta and derivative divisors, map their finite
supports to imaginary parts, and choose a point in an arbitrary open height interval outside the
finite union. Include both real endpoints and prove positive height excludes trivial zeta zeros.

### Attack B: fixed bottom

Derive analyticity and nonvanishing along the selected compact segment, prove continuity and
interval integrability of both logarithmic derivatives, and package the sum of their norms as a
fixed nonnegative constant.

### Attack C: finite indented contour

For every selected top height, enumerate the finitely many critical-line zeta zeros below it,
choose compatible left semicircle radii from the compiled local theorem, and assemble a
zero-free piecewise contour. Preserve multiplicity and do not assume zero simplicity.

### Attack D: source count theorem

Apply a proved argument principle to zeta and its derivative, compare boundary pieces using the
functional equation and compiled sign information, prove the `O(log T)` error, then recover the
source dichotomy. If the generic argument principle or top-edge estimate does not compile,
record its first exact theorem rather than assume it.

## Assumption frontier and claim boundary

Before and after preregistration, RH, `SpeiserDerivativeZeroFree`,
`LevinsonMontgomeryLogCountBound`, and `LevinsonMontgomeryCountDichotomy` are open. The campaign
may prove them directly but may not use any of them as a premise.

Success on Attacks A--B is historical contour infrastructure. Full success formalizes a known
1974 theorem and the existing project consumer then yields an unconditional Lean proof of
Speiser's equivalence. Neither result proves derivative-zero-freeness or RH.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary during the parent H1 campaign; current
  governance, Handoff, hard-gap DAG, Targets, source count definitions, and the 1974 primary
  source were rechecked before selection.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
