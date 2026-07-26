# H12 Levinson--Montgomery Log-Derivative to Paired-Mass Bridge Preregistration

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-LOGDERIV-MASS-BRIDGE-01`

Selected node: `H12-LM-LOGDERIV-MASS-BRIDGE-01`

Mode: `LITERATURE / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary source

Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the Riemann zeta-function*,
Acta Mathematica 133 (1974), 49--65, Theorem 1 and equations `(2.1)`--`(2.4)`.

- DOI: <https://doi.org/10.1007/BF02392141>
- Full text:
  <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf>

The displayed formulas and their use on source pages 51--52 were checked against rendered pages
of the original paper.

## Historical route selection

This selection follows the user-mandated omission search across historical route families.

- H1 critical-line proportions/mollifiers now has the complete Bettin--Gonek conditional bridge;
  its next named premise is Farmer's open arbitrary-length mollified moment conjecture.
- H7/H10 spectral and function-field routes now have finite explicit-formula and spectral-rigidity
  consumers, but the next steps require unconditional positivity, a number-field spectral object,
  or a regularized infinite trace.
- H2 zero density and H11 zero statistics still lack a source-backed theorem amplifying one
  actual sparse off-line orbit.
- H12 retains an adjacent part of a published proof. Equation `(2.1)` is not yet formalized, while
  the project now has both the actual multiplicity-bearing paired zero sum and a differentiable
  Stieltjes representation of the Gamma remainder.

H12 is selected because it is the strongest presently attackable published edge, not because
other historical families are closed. Original conjectures and direct RH proof attempts remain
open at every route selection.

## Exact source identity

For `s = sigma + i*t`, the source equation `(2.1)` is

```text
Re zeta'/zeta(s)
  = -Re 1/(s-1) + (1/2) log pi
    - (1/2) Re digamma(s/2+1)
    + Re sum_rho 1/(s-rho).
```

The final zero sum must be the already compiled, multiplicity-bearing, functional-equation-paired
sum `levinsonMontgomeryRealPairedZeroSum s`. It may not be replaced by an unjustified absolutely
summable raw reciprocal series.

Let

```text
A(s)
  = -Re 1/(s-1) + (1/2) log pi
    - (1/2) Re digamma(s/2+1).
```

The source estimates imply `A(s)<0` for `0<=sigma<=1/2` and `t>=10`. Together with equation
`Re pairedZeroSum = -(1/2-sigma) I1(s)`, this gives

```text
Re zeta'/zeta(s) >= 0  ->  I1(s) < 0
```

at nonzero zeta values in the open left half of the critical strip.

## Mandatory Lean endpoints

The intended module is
`LeanLab/Riemann/LevinsonMontgomeryLogDerivMassBridge.lean`.

Names may be adjusted only for Lean conventions. Statement strength and premise visibility must
not weaken.

```lean
theorem levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re
    {s : Complex} (hxi : riemannXi s != 0) :
    levinsonMontgomeryRealPairedZeroSum s =
      (logDeriv riemannXi s).re

theorem levinsonMontgomery_digamma_stirling
    {z : Complex} (hz : 0 < z.re) :
    Complex.digamma z =
      Complex.log z - 1 / (2 * z) +
        integral over the explicit Stieltjes derivative kernel

theorem levinsonMontgomery_digamma_stirling_remainder_norm_le
    {z : Complex} (hz : 0 < z.re) :
    norm (the explicit Stieltjes derivative remainder at z) <=
      27 / (64 * norm z ^ 2)

theorem levinsonMontgomery_equation_two_one
    {s : Complex} (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hzeta : riemannZeta s != 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryRealPairedZeroSum s

theorem levinsonMontgomeryLogDerivArchimedeanTerm_neg
    {s : Complex} (hs0 : 0 <= s.re) (hsHalf : s.re <= 1 / 2)
    (hsIm : 10 <= s.im) :
    levinsonMontgomeryLogDerivArchimedeanTerm s < 0

theorem levinsonMontgomeryPairedMass_neg_of_logDeriv_riemannZeta_re_nonneg
    {s : Complex} (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsIm : 10 <= s.im) (hzeta : riemannZeta s != 0)
    (hlog : 0 <= (logDeriv riemannZeta s).re) :
    levinsonMontgomeryPairedZeroMass s < 0

theorem levinsonMontgomeryDenseBranch_of_eventuallyNonnegativeLogDerivAtIntegers
    (hlog : LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers) :
    exists T0 : Real, forall T : Real, T0 <= T ->
      T / 2 < (speiserUpperLeftZetaZeroCount T : Real)
```

The final premise records the exact source branch: at every sufficiently large integer height
there is a zero-free point with `0<sigma<1/2` and nonnegative real zeta logarithmic derivative.
It is a consumer interface for the later boundary/contour argument, not an unconditional premise
or an RH-equivalent substitute.

## Position in the hard-gap DAG

```text
actual xi divisor + Hadamard cancellation
  -> Re paired reciprocal sum = Re xi'/xi
  -> exact source equation (2.1)
Stieltjes Gamma representation
  -> explicit digamma remainder and norm bound
  -> A(s)<0 on 0<=sigma<=1/2, t>=10
equation (2.1) + Re zeta'/zeta>=0
  -> paired mass I1(s)<0
  -> compiled half-unit zero localizer
  -> compiled eventual N^-(T)>T/2 dense branch
```

This campaign attacks all arrows shown above. It does not prove the premise that the
nonnegative-log-derivative witness exists at every large integer.

## Assumption frontier

Available unconditional inputs:

- the actual multiplicity-bearing xi divisor and the compiled paired real reciprocal sum;
- the Hadamard factorization, compensated logarithmic-derivative summability, and cancellation of
  its degree-one polynomial term;
- the exact xi functional equation and zeta/Gamma factorization away from `0` and `1`;
- the digamma recurrence;
- the compiled Stieltjes logarithmic-remainder identity on `Re(z)>0`, differentiation under its
  integral, nonnegative periodic kernel, and radial inverse-cube geometry;
- explicit bounds for `pi` and `log 2`;
- the compiled negative-mass localizer and dense integer-height branch.

Unavailable and prohibited as hidden premises:

- the desired equation `(2.1)` or paired-sum/xi-log-derivative equality;
- an abstract digamma asymptotic or remainder inequality;
- the desired sign `A(s)<0`;
- `LevinsonMontgomeryPairedMassNegativeAtIntegers`;
- `LevinsonMontgomeryCountDichotomy`, `LevinsonMontgomeryLogCountBound`, or
  `LevinsonMontgomeryExactCountSequence`;
- RH or `SpeiserDerivativeZeroFree`.

## Registered attacks

### Attack A: Hadamard cancellation and differentiated Stieltjes remainder

1. Average the compensated Hadamard zero term under `rho -> 1-conj(rho)`.
2. Use the already compiled reciprocal-pair cancellation at `0` and `1` to cancel the Hadamard
   polynomial and prove that the real paired reciprocal `tsum` is `Re(xi'/xi)`.
3. Prove the local product logarithmic-derivative formula
   `xi'/xi = 1/s + 1/(s-1) + GammaR'/GammaR + zeta'/zeta` in `0<Re(s)<1/2`.
4. Apply `digamma(z+1)=digamma(z)+1/z` to obtain equation `(2.1)` exactly.
5. Differentiate the compiled identity `scaledGamma=exp(StieltjesRemainder)`. Prove
   `digamma(z)=log(z)-1/(2z)+R(z)`, where `R` is the explicit integral of
   `-2 Q(t)/(z+t)^3`.
6. Bound `R` by `27/(64*norm(z)^2)` using `Q<=1/8`, the compiled radial inverse-cube bound,
   and the exact integral of `(t+norm z)^(-3)`.
7. Prove `A(s)<0` with rational bounds at `t>=10`, then combine the two exact identities with
   the already compiled paired-mass equation.
8. Map eventual integer-height log-derivative witnesses into the existing dense branch.

### Attack B: direct Gamma logarithmic derivative

If taking logarithmic derivatives of the scaled-Gamma identity causes branch or quotient
friction, differentiate the equality itself, cancel its nonzero factors, and identify the
derivatives of `Gamma` and the explicit Stirling main term directly. The same explicit
Stieltjes integral and numerical sign endpoint are mandatory.

## Success criteria

`FULL_LOGDERIV_MASS_BRIDGE_SUCCESS` requires:

- every mandatory endpoint above;
- no abstract Gamma bound, paired-sum equality, or target-equivalent premise;
- actual project zeta, xi, divisor, paired mass, and existing Speiser count;
- a proven Target and exact TargetChecks;
- selected transitive axiom prints;
- empty forbidden scans;
- direct warning-as-error module compilation and full `lake build`;
- frozen implementation, immutable-evidence, and final-ledger public CI.

## Falsification and stopping criteria

- `HADAMARD_NORMALIZATION_MISMATCH`: the paired sum differs from `Re(xi'/xi)` by a nonzero
  constant. Compile the exact corrected identity and stop the advertised equation `(2.1)`.
- `GAMMA_REMAINDER_TOO_WEAK`: the proved explicit remainder does not make `A(s)<0` at `t=10`.
  Record the sharp rational inequality and try Attack B; do not insert the desired sign as a
  premise.
- `LOWER_HEIGHT_REQUIRED`: the bound closes only above an explicit height greater than `10`.
  Compile that honest threshold and record the source mismatch; it does not count as full success.
- `SOURCE_IDENTITY_MISMATCH`: project xi normalization changes a pole or digamma term.
  Compile the exact project identity and stop the advertised source alignment.
- `local_stop`: full public closure or the first exact obstruction after both attacks. A local
  stop returns to `ROUTE_SELECTION`; the global RH Goal remains active.

## Claim boundary

This campaign does not prove:

- the low-height sign verification at `t=10`;
- negativity of `Re(zeta'/zeta)` on the full lower and critical-line contour boundaries;
- existence of a nonnegative interior witness when the exact-count top sequence fails;
- the indented-contour argument principle;
- the `O(log T)` count difference, full count dichotomy, Speiser equivalence, or RH.

Expected classification on success:

- `source_analytic_bridge_delta=1`;
- `historical_route_coverage_delta=1`;
- `known_theorem_formalization_delta=0` until the full Levinson--Montgomery theorem is compiled;
- `hard_gap_delta=0` for RH;
- `rh_frontier_delta=0`.

## Mechanical and publication gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct compilation, exact TargetChecks, selected `#print axioms`, empty
forbidden scans, `git diff --check`, full `lake build`, frozen implementation CI,
immutable-evidence CI, and final-ledger CI.

No production Lean source may be created or edited until this preregistration commit passes public
Lean Action CI. The six inherited user/exposure files remain untouched and unstaged.
