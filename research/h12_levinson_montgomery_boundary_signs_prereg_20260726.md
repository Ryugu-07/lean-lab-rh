# H12 Levinson--Montgomery Boundary Signs and Integer-Height Dichotomy Preregistration

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-BOUNDARY-SIGNS-01`

Selected node: `H12-LM-BOUNDARY-SIGNS-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Primary source

Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the Riemann zeta-function*,
Acta Mathematica 133 (1974), 49--65, Theorem 1 and the paragraph following equations
`(2.1)`--`(2.4)` on source pages 51--52.

- DOI: <https://doi.org/10.1007/BF02392141>
- Full text:
  <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf>

The source uses three boundary facts:

1. `Re(zeta'/zeta)<0` on `sigma=0`, `t>=10`;
2. `Re(zeta'/zeta)<0` on `sigma=1/2` away from zeros, with small left semicircles around
   critical-line zeros;
3. either suitable negative top heights occur cofinally or every sufficiently large height has
   an interior point where `Re(zeta'/zeta)>=0`.

The bottom edge `t=10` is handled in the source by explicit zero-count estimates plus the
verified fact that every zero below height `1000` lies on the critical line. That numerical
certificate is not silently imported here.

## Historical route selection

The preceding H12 campaign publicly closed equation `(2.1)`, explicit Gamma control, and the
open-strip implication

```text
Re(zeta'/zeta)>=0 -> paired mass I1<0 -> dense upper-left zero branch.
```

Fresh comparison retained these exact open edges:

- H2 and H11 still lack a published mechanism amplifying one actual sparse off-line orbit;
- H10 lacks a constructed number-field spectral object or justified regularized trace;
- H7's source reduces the next step to an explicitly open uniform Herglotz inequality or a new
  nonlocal nodal theory;
- H1 reaches Farmer's open arbitrary-length mollified moment conjecture;
- H12 has an adjacent published proof paragraph whose objects now exist in Lean.

This campaign therefore tests the two vertical boundary signs and the exact witness-producing
logical alternative. It does not optimize the already sufficient Gamma remainder. Other
historical families remain open, and original conjectures or direct RH attacks remain permitted
at every later route selection.

## Mandatory Lean endpoints

The intended module is
`LeanLab/Riemann/LevinsonMontgomeryBoundarySigns.lean`.

Names may be adjusted only for Lean conventions. Statement strength and premise visibility must
not weaken.

```lean
theorem differentiableAt_GammaR_of_not_neg_even
    {s : Complex} (hs : forall m : Nat, s != -(2 * m)) :
    DifferentiableAt Complex Complex.GammaR s

theorem logDeriv_GammaR_eq_digamma_of_not_neg_even
    {s : Complex} (hs : forall m : Nat, s != -(2 * m)) :
    logDeriv Complex.GammaR s =
      -(Real.log Real.pi : Complex) / 2 + Complex.digamma (s / 2) / 2

theorem levinsonMontgomery_equation_two_one_closed
    {s : Complex} (hs0 : 0 <= s.re) (hsHalf : s.re <= 1 / 2)
    (hsIm : 10 <= s.im) (hzeta : riemannZeta s != 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryRealPairedZeroSum s

theorem levinsonMontgomeryRealPairedZeroSum_nonpos_of_re_eq_zero
    {s : Complex} (hsRe : s.re = 0) (hxi : riemannXi s != 0) :
    levinsonMontgomeryRealPairedZeroSum s <= 0

theorem levinsonMontgomeryRealPairedZeroSum_eq_zero_of_re_eq_half
    {s : Complex} (hsRe : s.re = 1 / 2) (hxi : riemannXi s != 0) :
    levinsonMontgomeryRealPairedZeroSum s = 0

theorem levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary
    {s : Complex} (hsRe : s.re = 0) (hsIm : 10 <= s.im) :
    riemannZeta s != 0 and (logDeriv riemannZeta s).re < 0

theorem levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_critical_boundary
    {s : Complex} (hsRe : s.re = 1 / 2) (hsIm : 10 <= s.im)
    (hzeta : riemannZeta s != 0) :
    (logDeriv riemannZeta s).re < 0

def LevinsonMontgomeryNegativeLogDerivAtIntegerHeight (n : Nat) : Prop :=
  forall sigma : Real, 0 < sigma -> sigma < 1 / 2 ->
    riemannZeta (levinsonMontgomeryIntegerPoint sigma n) != 0 ->
    (logDeriv riemannZeta
      (levinsonMontgomeryIntegerPoint sigma n)).re < 0

theorem levinsonMontgomery_integer_height_logDeriv_dichotomy :
    (forall N : Nat, exists n : Nat, N <= n and
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) or
    LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers

theorem levinsonMontgomeryDenseBranch_of_not_cofinallyNegativeLogDerivAtIntegers
    (h : not (forall N : Nat, exists n : Nat, N <= n and
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n)) :
    exists T0 : Real, forall T : Real, T0 <= T ->
      T / 2 < (speiserUpperLeftZetaZeroCount T : Real)
```

The integer-height dichotomy is a transparent classical negation theorem. Its first branch is
only a cofinal sign predicate. It is not called an exact-count sequence because contour
admissibility and the argument principle are not yet proved.

## Position in the hard-gap DAG

```text
equation (2.1) + archimedean negativity
  -> critical-line paired sum = 0 away from zeros
  -> Re(zeta'/zeta)<0 on sigma=1/2 away from zeros

nontrivial-zero strip bounds + generic Gamma differentiability
  -> xi and zeta are nonzero on sigma=0, t>=10
paired-kernel positivity on sigma=0
  -> paired reciprocal sum <=0
  -> Re(zeta'/zeta)<0 on sigma=0

classical failure of cofinal interior negativity
  -> eventual nonnegative interior witnesses at integer heights
  -> compiled paired-mass dense branch
```

This campaign attacks every displayed arrow. It does not connect the cofinal-negative branch to
an exact count.

## Assumption frontier

Available unconditional inputs:

- the actual multiplicity-bearing xi divisor and paired reciprocal sum;
- the equality of that paired sum with `Re(xi'/xi)`;
- equation `(2.1)` on the open left half-strip;
- strict negativity of the archimedean term on
  `0<=sigma<=1/2`, `t>=10`;
- every nontrivial xi zero has `0<Re(rho)<1`;
- `GammaR(s)=0` exactly at the nonpositive even integers;
- complex Gamma is differentiable away from its nonpositive integer poles;
- the compiled eventual-nonnegative-log-derivative to dense-count consumer.

Unavailable and prohibited as hidden premises:

- either requested boundary sign;
- a closed-strip version of equation `(2.1)`;
- zero-freeness of zeta on `sigma=0`;
- RH, Speiser derivative-zero-freeness, or any low-height zero table;
- the source bottom-edge certificate;
- contour admissibility, indentation, argument-principle count equality, or the
  `O(log T)` count difference.

## Registered attacks

### Attack A: closed-strip Gamma and factorization

1. Generalize differentiability and nonvanishing of `GammaR` from `Re(s)>0` to every point away
   from its nonpositive even poles.
2. Reprove the Gamma logarithmic derivative formula with the generic non-pole hypothesis.
3. Reconstruct the local xi/Gamma/zeta logarithmic derivative identity at
   `0<=Re(s)<=1/2`, `Im(s)>=10`.
4. Apply the existing digamma recurrence to obtain equation `(2.1)` on the closed region.

### Attack B: termwise paired boundary signs

1. At `Re(s)=1/2`, prove every paired reciprocal term has real part zero, then sum.
2. At `Re(s)=0`, use `0<Re(rho)<1` to prove every paired kernel is nonnegative and hence every
   paired reciprocal term is nonpositive.
3. Prove xi has no zero on the imaginary axis, derive zeta nonvanishing there from the exact
   factorization, and combine both paired signs with strict archimedean negativity.

### Attack C: exact integer-height witness alternative

Negate cofinal strict negativity over all zero-free interior points. Normalize the resulting
threshold to at least `10`, extract a nonzero point with nonnegative real logarithmic derivative
at each later integer height, and feed the existing dense branch.

### Attack D: critical-zero indentation reconnaissance

Use the existing local analytic unit relating xi and zeta plus analytic order factorization to
test the source claim that the principal multiplicity term dominates on a sufficiently small
left semicircle around a critical-line zero. Any compiled local dominance lemma is retained, but
it is not allowed to replace or weaken mandatory Attacks A--C.

## Success criteria

`FULL_BOUNDARY_SIGNS_AND_INTEGER_DICHOTOMY_SUCCESS` requires:

- every mandatory endpoint above;
- actual project zeta, xi, divisor, paired sum, and Speiser count;
- no low-height, contour, or target-equivalent premise;
- a proven Target and exact TargetChecks;
- selected transitive axiom prints;
- empty forbidden scans;
- direct warning-as-error module compilation and full `lake build`;
- frozen implementation, immutable-evidence, and final-ledger public CI.

## Falsification and stopping criteria

- `CLOSED_GAMMA_FACTOR_MISMATCH`: the generic `GammaR` derivative or logarithmic derivative
  differs from the positive-half-plane formula. Compile the corrected formula and stop the
  advertised closed equation `(2.1)`.
- `LEFT_BOUNDARY_FACTORIZATION_MISMATCH`: xi/zeta normalization does not extend to the imaginary
  axis as advertised. Compile the exact corrected identity and record the first failing factor.
- `PAIRED_SIGN_MISMATCH`: a paired kernel on `sigma=0` or paired reciprocal term on
  `sigma=1/2` fails the source sign. Retain an explicit witness and stop the boundary claim.
- `TOTALIZED_LOGDERIV_LEAK`: the logical dichotomy admits a zeta zero as a fake nonnegative
  witness. Strengthen the predicate until nonvanishing is explicit; do not use totalized
  division as source evidence.
- `INDENTATION_INFRASTRUCTURE_GAP`: local analytic order factorization cannot yet produce a
  uniform semicircle sign. Record the missing analytic lemma; this does not negate success of
  mandatory Attacks A--C.
- `local_stop`: full public closure or the first exact obstruction after Attacks A--C. A local
  stop returns to `ROUTE_SELECTION`; the global RH Goal remains active.

## Claim boundary

This campaign does not prove:

- the bottom-edge sign at `t=10` from a certified low-zero table;
- negativity on left semicircle indentations around critical-line zeros;
- that the cofinal negative integer heights avoid all zeta zeros or are admissible contours;
- an exact zeta/zeta-derivative count equality;
- the indented argument principle, `O(log T)` count difference, full
  Levinson--Montgomery theorem, Speiser equivalence, or RH.

Expected classification on success:

- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `known_theorem_formalization_delta=0` until the full Levinson--Montgomery theorem;
- `hard_gap_delta=0` for RH;
- `rh_frontier_delta=0`.

## Production gate

Docs-only preregistration commit `a071e954c0433b072e16facba02b3a6f8647f391` passed public Lean
Action run `30192787155`, build job `89768923636`, in `1m36s`. Production proof editing opened
only after this gate.

## Local implementation result

Attacks A--C succeed in the 426-line
`LeanLab/Riemann/LevinsonMontgomeryBoundarySigns.lean` module:

- `GammaR` is differentiable and nonzero away from its nonpositive even poles, and its
  logarithmic derivative has the expected digamma formula there;
- the xi/Gamma/zeta logarithmic derivative identity and equation `(2.1)` extend to
  `0<=sigma<=1/2`, `t>=10`;
- the actual paired reciprocal sum is nonpositive on `sigma=0` and zero on `sigma=1/2`;
- xi has no imaginary-axis zero because every nontrivial zero has positive real part, and exact
  factorization therefore proves zeta is nonzero on `sigma=0`, `t>=10`;
- `Re(zeta'/zeta)<0` compiles on the left boundary and at every zero-free critical-boundary
  point;
- exact classical negation proves the integer-height cofinal-negative/eventual-nonnegative
  dichotomy, and failure of the first branch feeds the existing dense upper-left-zero count.

Attack D reaches a source-relevant partial endpoint. Every actual xi zero has a local analytic
factor retaining multiplicity, the residual logarithmic derivative is continuous, and the
principal term `m/(z-rho)` has strictly negative real part at every strict left point. This does
not yet prove negativity on a whole left semicircle: near its two critical-line endpoints the
principal real part is not uniformly separated from zero, so a later proof must glue
critical-line endpoint neighborhoods to a quantitatively dominated middle arc.

The proven Target, nine mandatory TargetChecks, selected axiom prints, forbidden scans,
warning-as-error checks, and full `8766/8766` build pass. Selected transitive axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Local classification:

- `result=FULL_BOUNDARY_SIGNS_AND_INTEGER_DICHOTOMY_SUCCESS`;
- `indentation_reconnaissance=LOCAL_FACTOR_AND_PRINCIPAL_SIGN_COMPILED`;
- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Public implementation result

Frozen implementation commit `d45e87b3c6ab9d41217f671b0dc96ec979167b45` passed public Lean
Action run `30193246131`, build job `89770129416`, in `2m7s`. Proof source remains frozen.
Docs-only immutable-evidence commit `4c0ad75da06648c564fa58d9d29c762d46bff823` passed public run
`30193425500`, build job `89770603420`, in `1m34s`, without changing proof source. Publish one
final ledger recording all three public gates and require its own CI.
