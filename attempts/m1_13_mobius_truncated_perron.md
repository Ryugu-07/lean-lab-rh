# M1-13 Mobius Truncated Perron Attempt

Date: 2026-07-11

Fixed gap: `G2/F1/Balazard-Saias/truncated-Perron`.

## Sole Target

For `x=N+1/2` and the vertical line `Re(w)=2`, prove an absolute
`C*(N+1)^2/T` approximation of `mobiusDirichletPartialSum N s` by the source Perron integral,
uniformly for `N>=2`, `T>=1`, and `1/2<=Re(s)<=1`.

## Source Audit

The batch checked Titchmarsh Lemma 3.12 and Theorem 14.25(A) from
`/tmp/TitchmarshZeta.pdf` (SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`). The specialization
uses `a_n=mu(n)`, `c=2`, and half-integral `x`. The stronger Balazard-Saias estimate remains
distinct from Titchmarsh's pointwise convergence theorem.

## Lean Route

`LeanLab/Riemann/TruncatedPerron.lean` now checks:

- the absolutely convergent identity `LSeries_moebius_eq_reciprocal_riemannZeta` on `Re(s)>1`;
- Cauchy-Goursat for `exp(a*w)/w` on a rectangle wholly inside the right half-plane;
- exact horizontal-side bounds and vanishing of the remote right vertical side when `a<0`;
- `norm_perronIntegrand_vertical_integral_le_of_neg`, the quantitative negative-side Perron
  inversion estimate;
- `norm_truncatedPerronKernel_two_le_of_lt_one`, its source-specialized `c=2`, `0<y<1` form.

No standalone derivative, integration-by-parts identity, or kernel rewrite is counted as closure
of the preregistered target.

## Compiler Attempts

1. Real-parameter complex derivatives initially exposed incompatible inferred scalar-structure
   proof terms. Composing a complex affine derivative with `Complex.ofReal` produced a stable
   checked proof.
2. A first integration-by-parts idea was rejected as insufficient: on a finite symmetric interval
   it gives no `1/T` decay. The proof switched to Titchmarsh's rectangle deformation.
3. The no-pole rectangle compiled after making the real and imaginary corners explicit with
   `Complex.mk` and proving the rectangle remains in `Re(w)>0`.
4. Horizontal estimates use the exact integral of `exp(a*x)`; the remote vertical estimate tends
   to zero through `Real.tendsto_exp_atBot`.
5. The same rectangle argument cannot prove the `y>1` side because moving left crosses `w=0`.
   Pinned Mathlib exposes rectangle Cauchy-Goursat but no rectangle residue theorem. The exact next
   dependency is the boundary identity for `1/w` giving `2*pi*i`, followed by the positive-side
   kernel estimate for `norm(K_T(y)-1)`.

## Result

`result_class`: `DEPENDENCY_GAP_IDENTIFIED`.

The sole Mobius truncated Perron theorem remains open, so the fixed hard gap is not removed. The
strictly smaller checked dependency is the complete negative-side kernel estimate; the unresolved
frontier is the positive-side residue contribution, then absolute-series interchange and summation
of the source errors. No `sorry`, `admit`, or new axiom is present.

Full `lake build` passes with 8603 jobs. The three audited M1-13 declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`; incomplete-proof, explicit-declaration, and
`git diff --check` scans pass.
