# M1-12 Reciprocal-Zeta Subpower Attempt

Date: 2026-07-11

Fixed gap: `G2/F1/Balazard-Saias/reciprocal-zeta-subpower`.

## Statement

Under RH, for `0 < delta <= 1/2` and `0 < eta`, prove a constant `C > 0` uniformly bounds
`norm (riemannZeta s)^(-1)` by `C * (1 + |Im(s)|)^eta` on
`1/2 + delta <= Re(s) <= 1`.

## Strategy

Follow Titchmarsh Theorem 14.2: construct and normalize `log zeta` on an RH zero-free disk; derive
an outer polynomial bound from Abel continuation and a fixed right-circle logarithm bound from
absolute convergence; apply Borel-Caratheodory; derive three-circles from Mathlib's Hadamard
three-lines theorem; reserve a `delta/2` radial margin to obtain an exponent strictly below one;
then exponentiate and patch finite heights by residue control plus compactness.

## Compiler Attempts

1. The Borel proof initially failed on positivity coercions, reciprocal-denominator inequalities,
   and `mul_le_mul` argument order. Explicit positivity witnesses and factored term bounds resolved
   these without changing the estimate.
2. The three-circles bridge initially failed only when simplifying
   `c + exp(log(z-c))`; an explicit nonzero proof and ring normalization closed the map back to the
   original point.
3. The source geometry was first observed to degenerate if Borel and the target strip use the same
   `delta`: the left endpoint then has interpolation exponent one. Calling Borel with `delta/2`
   creates the required strict margin; Lean verifies the uniform maximum exponent is below one.
4. The low-height compactness proof could not include `s=1` directly because Mathlib assigns zeta
   a nonzero junk value at its pole, making the reciprocal discontinuous there. The route was split:
   the residue theorem bounds a pole neighborhood, and continuity handles the compact complement.

## Result

`LeanLab/Riemann/ReciprocalZetaSubpower.lean` compiles the exact preregistered theorem
`RiemannHypothesis.exists_reciprocalZeta_subpower_bound` with no `sorry`, `admit`, or new axiom.
This closes only the reciprocal-zeta subedge. Truncated Perron and contour balancing remain before
the Balazard-Saias estimate is proved.

Full `lake build` passes with 8602 jobs. The final theorem's trusted dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`; placeholder, explicit-declaration, and diff checks
pass.
