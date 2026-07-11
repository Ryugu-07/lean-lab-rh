# M1-11 Analytic Logarithm Branch Attempt

Date: 2026-07-11

Fixed gap: `G2/F1/Balazard-Saias`.

## Statement

On a simply connected open set, prove that a nonvanishing holomorphic complex function has a
holomorphic logarithm branch, with derivative `g'/g`. Then instantiate it for `riemannZeta` on a
domain that avoids `1` and contains no zeta zero.

## Source

Titchmarsh-Heath-Brown, *The Theory of the Riemann Zeta-function*, Sections 14.2 and 14.25. The
analytic branch of `log zeta` is required before Borel-Caratheodory can control `1/zeta`.

## Strategy

Start from mathlib's continuous exponential lift. Near a point `z`, compare it with
`f(z) + Complex.log (g(w) / g(z))`. Continuity puts both differences in the principal exponential
strip, and equality of their exponentials makes them equal there. The local principal-log formula
then supplies the derivative.

## Compiler Attempts

1. Initial proof failed on namespace qualification for `Filter.Tendsto` and `Real.pi`, unfolding
   the composed exponential equality, and an invalid attempt to use `linarith` on a complex
   equality.
2. The second pass replaced those steps with explicit exponential equalities, `abs_im_le_norm`,
   `Complex.exp_inj_of_neg_pi_lt_of_le_pi`, and `sub_eq_iff_eq_add`.
3. The remaining filter target mismatch was resolved by giving the exact target values of the two
   `Tendsto` statements and transporting metric-ball membership with `Tendsto.eventually`.

## Result

`lake env lean LeanLab/Riemann/AnalyticLogBranch.lean` passes. There is no `sorry`, `admit`, or new
axiom. The Balazard-Saias estimate remains unproved; the next source edge is the quantitative
Borel-Caratheodory/Hadamard bound for reciprocal zeta.
