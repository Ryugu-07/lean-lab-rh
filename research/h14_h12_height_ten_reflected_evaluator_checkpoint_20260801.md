# H14 x H12 Height-Ten Reflected Evaluator Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `MEANINGFUL_PARTIAL / ACTUAL_ZETA_PRODUCER_REDUCTION /
HEIGHT_TEN_CERTIFICATE_OPEN`

## Compiled result

`LeanLab/Riemann/LevinsonMontgomeryHeightTenCertificate.lean` proves without `sorry`:

1. an explicit Cauchy first-derivative remainder for the actual ordered eta series;
2. actual finite eta-quotient error balls for `riemannZeta` and `deriv riemannZeta`;
3. nonvanishing of the eta factor whenever the real part is below one;
4. the exact reflected real logarithmic-derivative identity
   `Re(zeta'/zeta)(s) = -Re(zeta'/zeta)(1-s) + A(s) + A(1-s)`;
5. an explicit enclosure of each `A` from the compiled Stieltjes digamma remainder;
6. robust error-ball inequalities converting finite centers into actual quotient signs; and
7. `speiserStrictNegativePoint_of_reflected_hardyLittlewood_margins`, which turns finite
   reflected margins into the actual pointwise Speiser sign condition.

The reflection is the substantive repair. Direct eta evaluation degenerates as the left-half
real part approaches zero. Reflection sends every `0 < sigma <= 1/2` to real part at least
`1/2`, while the previously compiled left-boundary theorem handles `sigma=0` exactly.

## Falsification result

The fixed Cauchy radius `r=sigma/2` is rejected. Nonrigorous high-precision navigation found its
derivative radius still larger than the center at the critical-line endpoint for `N=10^5`, and
the loss worsens toward zero. Choosing `r` near `1/log N` restores the expected
`N^-sigma log N` scale; at reflected real part `1/2`, navigation found favorable margins around
`N=10^6`. None of these floating-point observations is used by Lean.

## Exact remaining boundary

The module does not prove `SpeiserStrictNegativeHorizontal 10`, the low-height count equality,
or `LevinsonMontgomeryHeightTenCertificate`. The remaining producers are:

1. proof-generating enclosures for finite complex logarithms, exponentials, powers, and norms;
2. a finite rational subcover of the height-ten segment proving all reflected margins; and
3. an actual multiplicity-bearing zeta/zeta-derivative zero-count certificate below height ten.

The next primary attack is a short Johansson-style Euler--Maclaurin evaluator backed by
kernel-checked Taylor/rational intervals. The compiled PF5 exponential Taylor certificates show
that this proof-producing pattern already works in the repository. The eta-reflection evaluator
remains an independent cross-check, not the sole route.

Local audit: the 705-line module, five exact TargetChecks, five selected axiom prints, aggregate
import, forbidden scan, and patch check pass. The selected declarations use only `propext`,
`Classical.choice`, and `Quot.sound`; the full build passes `8820/8820`.

## Claim boundary

This checkpoint reduces an actual analytic producer. It is not a numerical certificate, the
height-ten certificate, the unconditional Levinson--Montgomery dichotomy, Speiser equivalence,
H12, or RH. The global RH Goal remains active.
