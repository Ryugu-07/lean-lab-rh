# Route Selection after the Positive-Cosh Li3 Obstruction

Date: 2026-07-17

Decision: `SELECT H6 time-zero third Li covariance / DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`

## Comparison

| target | mathematical value | checked leverage | current obstacle | decision |
| --- | --- | --- | --- | --- |
| Direct W2/G7 positivity | RH-equivalent | complete fixed-width Gaussian arithmetic criterion | no new global cancellation mechanism after the exact local-prime sign obstruction | eligible, no new attack selected |
| Direct M2/G3 approximation | RH-equivalent | complete Baez-Duarte criterion and Burnol obstruction theory | no new approximant family beyond the rejected projection, ladder, sparse-Gram, and q=2 branches | eligible, no new attack selected |
| H1/H2 finite counts | honest shared infrastructure | xi divisor finiteness and reflection | does not reach a mollifier, density, or exceptional-zero exclusion estimate | defer |
| Repeat generic H6 positive-kernel extrapolation | would feed the all-index Li route | exact first-two moment theorem | `OBS-H6-POSITIVE-COSH-LI3-01` gives a compiled positive two-atom counterexample at order three | reject |
| Actual theta-kernel third Li coefficient | first unproved order beyond H6-X; tests a scalable cumulant mechanism on the real source | exact `A,B,C` moments, `B^2<=A*C`, time-zero xi bridge, and compiled `lambda1<1` bound | requires a fourth source moment, a genuine weighted Chebyshev covariance proof, third logarithmic differentiation, and exact Li-index alignment | select |

## Materially new attack angle

The closed generic branch asked whether positivity and ordinary Hankel inequalities alone force
higher Li positivity. They do not. This campaign instead uses two facts absent from the
countermodel as a conjunction:

1. for the positive theta weight, the coordinates `X(u)=u*tanh(u)` and `Y(u)=u^2` are similarly
   ordered, suggesting the exact covariance inequality `A*D >= B*C`;
2. at time zero, the compiled exact xi bound gives `lambda1<1`, hence the normalized mean
   `B/A<1/2`.

Writing `b=B/A`, `c=C/A`, and `d=D/A`, the registered third expression is

`6*b + 12*(c-b^2) + 4*d - 12*b*c + 8*b^3`.

The two moment inequalities give `c-b^2>=0` and `d>=b*c`; therefore it is bounded below by

`6*b + (12-8*b)*(c-b^2)`.

This is strictly positive when `b>0` and `b<3/2`. The time-zero theorem `lambda1<1` supplies a
stronger bound. Every algebraic and analytic step remains to be checked by Lean.

## Adversarial screening

- The public two-atom model has `Li1>0`, `Li2>0`, and `Li3<0`; its normalized first mean is too
  large for the proposed sufficient condition, so it does not refute this campaign.
- A finite positive-measure algebra check confirms that similarly ordered `X,Y` imply the required
  covariance, but that calculation is not a Lean premise.
- A 35-digit `mpmath` screen of the source series and integrals selected the target only. At `t=0`
  it returned approximately `(Li1,Li2,Li3)=(0.0230957089661,0.0923457352280,0.207638920554)`;
  sampled times from `-100` through `100` also gave a positive third value. No numerical value or
  quadrature error claim may enter the proof.

## Source search

- X.-J. Li, *The Positivity of a Sequence of Numbers and the Riemann Hypothesis*, JNT 65 (1997),
  fixes the standard all-index differential criterion.
- Bombieri and Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, JNT 77
  (1999), supplies the transformed-zero context.
- D. H. J. Polymath, arXiv:1904.12438, supplies the exact de Bruijn-Newman theta heat family.
- M. W. Coffey, *Relations and positivity results for the derivatives of the Riemann xi function*,
  JCAM 166 (2004), proves positivity facts for xi derivatives at `s=1`, but the bounded search did
  not locate this exact covariance-to-third-Li argument.
- K. Maslanka, arXiv:math/0402168, computes many Li coefficients. Numerical positivity is context,
  not proof. No novelty or priority claim is made.

## Next state

Preregister the exact fourth moment, covariance certificate, third derivative normalization,
standard Li-index bridge, sign theorem, falsification surface, and stop conditions. No Lean proof
source may be edited until the preregistration commit passes public Lean Action CI.
