# H12 Speiser Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H12-SPEISER-COUNTING-EQUIVALENCE-01`

## Source region

Levinson--Montgomery count zeros with multiplicity in

```text
0 < Im(s) < T, 0 < Re(s) < 1/2.
```

The Lean set `speiserUpperLeftRectangle T` uses exactly these four strict inequalities.  The
critical line, real axis, height `T`, and the line `Re(s)=0` are excluded.

## Functions and multiplicity

- `speiserUpperLeftZetaZeroCount T` sums `analyticOrderNatAt riemannZeta` over the finite set of
  nontrivial zeta zeros in the source rectangle.
- `speiserUpperLeftDerivZeroCount T` sums `analyticOrderNatAt (deriv riemannZeta)` over the finite
  derivative-zero set in the same rectangle.
- `riemannZetaDerivDivisor` is the meromorphic divisor of `deriv riemannZeta` on `{1}ᶜ`.  The
  source rectangle lies in that domain, and `riemannZetaDerivDivisor_apply` identifies its values
  with the natural analytic multiplicities.

No boundary zero receives half weight.  A future indented-contour theorem must produce these open
rectangle counts exactly.

## Speiser condition

`SpeiserDerivativeZeroFree` means

```text
∀ s, 0 < Im(s) ∧ 0 < Re(s) ∧ Re(s) < 1/2 → zeta'(s) ≠ 0.
```

The restriction to positive height matches the source count.  The separate theorem
`criticalStripRealAxisZeroFree` proves that nontrivial zeta zeros cannot lie on the real axis by
combining `deBruijnNewmanH_mul_I_re_pos` with the exact `H_0`--xi coordinate.  Conjugation and the
functional equation then make `SpeiserZetaZeroFree` equivalent to `Mathlib.RiemannHypothesis`.

## Theorem 1 outputs

- `LevinsonMontgomeryLogCountBound` is the literal eventual `O(log T)`-shaped absolute count
  difference bound with an explicit nonnegative constant.
- `LevinsonMontgomeryCountDifferenceSublinear` is only its `o(T)` consequence.  Lean proves the
  implication using `Real.isLittleO_log_id_atTop`.
- `LevinsonMontgomeryCountDichotomy` says either exact count equality occurs at unbounded heights,
  or the zeta count is eventually greater than `T/2`.

The final compiled consumer assumes the log bound and dichotomy as hypotheses.  It does not assert
that either analytic source theorem has yet been formalized.

## Result classification

`riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryTheoremOne` is a conditional
assembly theorem.  It proves that the two source-faithful analytic outputs suffice for the full
Speiser equivalence.  It is route infrastructure with `rh_frontier_delta=0`, not an unconditional
RH theorem and not yet a completed formalization of Speiser's theorem.
