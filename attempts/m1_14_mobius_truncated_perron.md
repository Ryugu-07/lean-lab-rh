# M1-14 Mobius Truncated Perron Completion

Date: 2026-07-11

Fixed gap: `G2/F1/Balazard-Saias/truncated-Perron`.

## Sole Target

Prove one absolute constant `C>0` such that, uniformly for `N>=2`, `T>=1`, and
`1/2<=Re(s)<=1`,

```text
norm(mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s)
  <= C * (N+1)^2 / T.
```

## Route

The implementation follows the audited Titchmarsh Lemma 3.12 specialization:

1. Compute the oriented rectangle boundary integral of `w^-1` as `2*pi*i` using its Cartesian
   decomposition, symmetric odd cancellation, `integral_div_sq_add_sq`, and the positive/negative
   arctangent inverse identities.
2. Define the pole-subtracted quotient with Mathlib's `dslope`; prove it is entire and combine its
   zero boundary integral with the reciprocal boundary integral.
3. Move the contour left for `a=log y>0`, prove the remote vertical side vanishes, and obtain the
   exact positive-side bound on `norm(K_T(y)-1)`. M1-13 supplies the negative-side bound.
4. Expand reciprocal zeta by the absolutely convergent Mobius L-series on `Re(s+w)>1`. A fixed
   `Re=5/2` summable majorant justifies series-integral exchange through interval dominated
   convergence.
5. Identify each integrated term with its Dirichlet coefficient times `K_T(x/n)`.
6. For `x=N+1/2`, prove `1/|log(x/n)| <= 3*n`. This converts every coefficient error into a
   universal multiple of `x^2*T^-1*n^(-3/2)`, which is summable.
7. Sum the norm bounds and choose the absolute constant from the finite p-series total.

## Compiler Notes

- The residue theorem was not assumed. The rectangle calculation was derived from checked real
  arctangent integrals and Cauchy-Goursat for the removable part.
- Finite-height integration and the infinite Mobius sum were exchanged only after a checked
  dominated-convergence majorant.
- The final theorem is stronger than required in two harmless ways: its proof does not need
  `N>=2` or the upper condition `Re(s)<=1`, though both remain in the source-facing statement.
- No kernel lemma, residue identity, or finite-sum rewrite is counted separately as the batch
  result.

## Result

`exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le` compiles the exact sole target
without `sorry`, `admit`, a Perron premise, or a new axiom.

`result_class`: `HARD_GAP_REDUCED`.

This removes only `G2/F1/Balazard-Saias/truncated-Perron`. The Balazard-Saias contour shift and
error balancing remain open, so Balazard-Saias, M1, G2, D, and RH are not complete.

Full `lake build` passes with 8603 jobs. The residue theorem, positive kernel theorem,
series-integral exchange, and final source theorem each depend only on `propext`,
`Classical.choice`, and `Quot.sound`; incomplete-proof, explicit-declaration, and diff checks pass.
