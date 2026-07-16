# R5 Compact Laplace Xi-Divisor Separator Preregistration

Campaign: `CAMPAIGN-20260716-R5-COMPACT-LAPLACE-SEPARATOR-01`

Date: 2026-07-16

Status: `LOCAL_VERIFIED`

Mode: `LITERATURE`

## Fixed Proposition

For any multiplicity-bearing xi divisor index and any positive error, construct one smooth
compactly supported function on the additive logarithmic line whose bilateral Laplace transform
is exactly one at the selected xi zero and has arbitrarily small absolute `tsum` over every
different xi-zero value. The indivisible endpoint is

```lean
theorem exists_compactSupport_xiDivisor_laplace_tsum_separator
    (p0 : RiemannXiDivisorZeroIndex) {epsilon : R} (hepsilon : 0 < epsilon) :
    exists f : R -> C,
      ContDiff R infinity f and
      HasCompactSupport f and
      compactLaplaceTransform f (riemannXiDivisorZeroValue p0) = 1 and
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        norm (compactLaplaceTransform f (riemannXiDivisorZeroValue p))) and
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
        else norm (compactLaplaceTransform f (riemannXiDivisorZeroValue p))) < epsilon
```

The formal module may use Lean Unicode and package the function as a Mathlib test function, a
Schwartz map with compact-support proof, or an equivalent raw function. It must retain actual
smooth compact support, exact target normalization, complete multiplicity-bearing divisor
summability, and the strict `tsum` bound. Equal-value multiplicity copies must be protected rather
than falsely separated.

## Source Alignment

- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, arXiv:2006.13771,
  Appendix C, Proposition C.1, reduces the compact-support Weil converse to a smooth Mellin
  interpolation function with finite prescribed zeros, one protected value, and quadratic decay
  on the remaining zeta zeros: https://arxiv.org/abs/2006.13771
- That proposition cites H. Yoshida, *On Hermitian forms attached to zeta functions* (1992), for
  the underlying compact-support Weil criterion and separator construction.
- The present endpoint is a project-specialized `ell^1` version on the already compiled complete
  xi divisor. It is sufficient for a dominated zero-functional separation step but does not by
  itself state the explicit formula or Weil positivity.

No novelty claim is allowed. Classification on success is at most `BRIDGE_REDUCED` or
`KNOWN_MECHANISM_RECONSTRUCTED` pending independent source comparison.

## Five-Candidate Audit

1. **Full Connes--Consani archimedean positivity:** rejected for this campaign. Its decisive
   operator spectrum bound uses prolate functions, a 1,732-term trigonometric approximation,
   external high-precision parameters, and computer-assisted inequalities not yet represented in
   Lean.
2. **Generic integration of the current strip class:** rejected. Closed-strip boundedness alone
   supplies no quantitative vertical decay for the horizontal contour edges.
3. **Immediate Gaussian/Hermite Schwartz density:** rejected. Mathlib has Schwartz/Fourier
   infrastructure but no packaged Hermite completeness theorem, and extending the separated
   arithmetic distributions by assumed tempered continuity would hide an RH-equivalent premise.
4. **Compact log-Laplace xi-divisor separator:** admitted. It has a complete mechanism from
   compact bumps, integration by parts, finite exponential interpolation, convolution powers, and
   the compiled reciprocal-square xi-zero sum.
5. **Another fixed-width Gaussian reformulation:** rejected by anti-cycling. W2g2 already closes
   width compression and no stronger unconditional sign mechanism is supplied.

## Adversarial Audit

1. A transform cannot distinguish multiplicity copies with the same zero value. The endpoint
   excludes the full equal-value class from the small tail.
2. A normalized compact bump can have transform modulus larger than one at finitely many other
   zeros. Those values must be annihilated before taking convolution powers.
3. Choosing a larger finite annihilation set after estimating the polynomial tail is circular,
   because the polynomial bound can grow. The fixed mechanism instead chooses one threshold
   `q<1`, proves the superlevel of the base transform is finite, annihilates exactly that fixed
   superlevel, and only then sends the convolution exponent to infinity.
4. The finite exponential polynomial is uniformly bounded on the xi strip because its shifts are
   real and every xi zero has real part in `(0,1)`.
5. Additive convolution preserves smooth compact support, and the bilateral Laplace transform of
   a convolution is the product whenever both factors have compact support.
6. Modulating the base bump by `exp(-rho0*x)` makes its transform at `rho0` the strictly positive
   bump integral, avoiding an unproved noncancellation assertion.
7. Two integrations by parts give a uniform `C / norm(s)^2` bound on the xi strip. The compiled
   reciprocal-square divisor theorem then gives absolute summability without zero counting,
   simplicity, or an enumeration.

## Fixed Proof DAG

1. Define `compactLaplaceTransform f s = integral x, exp(s*x)*f(x)` and prove linearity,
   translation covariance, and integrability for compactly supported continuous functions.
2. Build a nonnegative smooth bump, modulate it by the selected zero, normalize by its strictly
   positive integral, and prove exact target value one.
3. Integrate by parts twice and prove a strip-uniform inverse-square bound. Deduce absolute
   summability of its transform over the complete xi divisor.
4. Fix a rational threshold `q` in `(0,1)`. Prove the unwanted `norm(transform)>=q` value set is
   finite, preserving the full equal-target-value class.
5. Reuse the compiled finite exponential separation lemma to construct a complex polynomial
   vanishing on that unwanted finite value set and nonzero at the target. Realize polynomial
   evaluation physically as a finite complex linear combination of real translates of the bump.
6. Define compactly supported additive convolution powers and prove their Laplace transform is the
   corresponding power. Combine with the translated polynomial packet.
7. Bound the surviving divisor tail by a fixed summable square family times `q^(m-2)` and choose
   `m` large enough for the strict `epsilon` bound.
8. Compile the exact endpoint, target witness, selected transitive axiom prints, forbidden scans,
   full local build, and independent public CI.

## Rejection Conditions

- Do not assume RH, simple zeros, a zero enumeration, Riemann--von Mangoldt asymptotics, a
  compact-support Paley--Wiener theorem, or the source's separator lemma.
- Do not replace compact support by Gaussian or Schwartz decay alone.
- Do not replace the complete xi divisor `tsum` by a finite set or a set without multiplicity.
- Do not claim that this proves the explicit formula, unconditional Weil positivity, G7, or RH.
- Reject any `sorry`, `admit`, `native_decide`, project axiom, unsafe declaration, or resource-limit
  relaxation.
- If physical convolution covariance or the inverse-square transform bound fails under two
  independent formal approaches, close locally as `NO_PROGRESS` and return to route selection.

## Accounting

- `hard_gap_before`: G6/W1 open; G7/W2 open; G3/M2 parked
- `hard_gap_after_if_complete`: G6/W1 remains open with one compact-support reverse-separation
  subedge compiled; G7/W2 remains open
- `hard_gap_delta`: 0 for fixed hard-gap nodes and RH
- `assumption_frontier_before`: no compiled smooth compact-support separator on the complete xi
  divisor
- `assumption_frontier_after_if_complete`: compact-support xi-divisor separation is available;
  generic explicit-formula integration and unconditional positivity remain unproved

## Local Result

The fixed proposition now compiles exactly as
`exists_compactSupport_xiDivisor_laplace_tsum_separator` in
`LeanLab/Riemann/WeilCompactLaplaceSeparator.lean`. The implementation follows the preregistered
superlevel-first construction. Its geometric estimate is slightly stronger and simpler than the
planned square-family form: after annihilating the fixed `norm(F)>=1/2` value set, the surviving
tail is bounded by `B * (1/2)^m * norm(F)`, and the already proved summability of `norm(F)` closes
the strict `tsum` bound. This changes no endpoint or assumption frontier.
