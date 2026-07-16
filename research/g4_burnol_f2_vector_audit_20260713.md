# G4-F2 Burnol Vector Dependency Audit

Date: 2026-07-13

Audit ID: `AUDIT-20260713-G4-F2-01`

Result: `DEPENDENCY_GAP_IDENTIFIED`

## Primary Source

Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, Advances in Mathematics 170 (2002), 56-70, arXiv
`math/0103058v2`, <https://arxiv.org/abs/math/0103058>.

The audited arXiv v2 source is the gzip-compressed TeX file cached at
`/tmp/burnol0103058.tar`, SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.
Relevant source lines are:

- 295-360: invariant Mellin multipliers and the Baez-Duarte phase construction;
- 364-391: `Z`, `A`, the second phase operator `V`, and the model space;
- 393-420: `psi(w,k)`, `Q_lambda`, the exact `Y` limit, pairing, and orthogonality corollary;
- 434-462: the pre-boundary pairing calculation;
- 465-521: the imported `k=0` oscillatory estimates and first boundary limit;
- 524-576: the `k>=1` oscillatory integral, explicit series, and full existence theorem.

Burnol's `k=0` theorem explicitly invokes Lemmas 4 and 6 of Baez-Duarte, Balazard, Landreau, and
Saias, *Notes sur la fonction zeta de Riemann, 3*, Advances in Mathematics 149 (2000), 130-144,
DOI `10.1006/aima.1999.1861`. The `k>=1` extension is proved in the Burnol source itself.

## Correct Operator Boundary

F1b constructed the unitary

```text
T = (1-M)^(-1),       multiplier (s-1)/s,
```

which sends the original target and kernels to `chi1` and `-A(t/theta)`. F2 uses a different
unitary: the Baez-Duarte phase of `A`. If

```text
Z(s) = Mellin(A)(s) = (s-1) zeta(s) / s^2,
```

then, away from the null set of critical-line zeta zeros,

```text
V(s) = conj(Z(s)) / Z(s)
     = (s/(1-s))^3 * zeta(1-s)/zeta(s).
```

The Lean definition should use a total unit-modulus phase, for example value `1` when `Z=0`, and
prove agreement with the source quotient almost everywhere. Dividing by zeta at a critical-line
zero is forbidden. The already compiled countability and nullity of critical-line zero ordinates
supplies the almost-everywhere bridge.

This `V` commutes with normalized multiplicative dilation and sends `A` to its time reversal
`J(A)(t)=t^(-1) A(1/t)`. These are the source facts that make the cutoff pairing calculation work.

## Exact Vector Construction

For `re(w)<1/2`, Burnol defines

```text
psi(w,k)(t) = (log(1/t))^k * t^(-w) * 1_(0,1](t),
Q_lambda f = 1_[lambda,infinity) * f,
PreY(lambda,w,k) = V^(-1) Q_lambda V psi(w,k).
```

For `0<lambda<=1`, `re(s)=1/2`, and every natural `k`, the source theorem is

```text
Tendsto (PreY(lambda,w,k))
  (nhdsWithin s {w | re(w)<1/2})
  (nhds (Y(lambda,s,k))).
```

The source uses an inner product linear in the first argument. Mathlib's complex inner product is
conjugate-linear in the first argument and linear in the second, so Burnol's
`(D_theta A,Y)` is represented as `inner Y (D_theta A)` in Lean.

Burnol uses normalized dilation

```text
D_theta A(t) = theta^(-1/2) A(t/theta),
```

whereas the project's existing `burnolModelKernelL2 theta` represents `A(t/theta)`. F2 must expose
the scalar relation explicitly and may not silently identify these vectors.

## Pairing And Orthogonality

Before taking the boundary limit, unitary invariance, cutoff self-adjointness, support of `J(A)`,
and dilation commutation reduce the pairing to an explicit Mellin derivative. After passage to the
boundary, Burnol obtains

```text
(D_theta A, Y(lambda,s,k))
  = (-d/ds)^k [theta^(s-1/2) * Z(s)]
```

for `lambda<=theta<=1`. In Lean's convention the left side is
`inner (Y lambda s k) (normalizedModelKernel theta)`.

For the lower-bound route only the forward zero-order implication is required: if

```text
(k+1 : ENat) <= analyticOrderAt riemannZeta s,
```

then all derivatives through order `k` of zeta vanish at `s`. Since `(s-1)/s^2` is analytic and
nonzero on the critical line, the same derivative vanishing holds for `Z`; the pairing formula
then puts `Y(lambda,s,k)` in `(burnolModelKernelSpan lambda)^orthogonal`.

The source states an iff, but the reverse direction is not needed for F3-F5 and is not part of the
fixed completion gate.

## Genuine Existence Dependency

The boundary limit is not a generic continuity statement. The uncut vectors `psi(w,k)` have a
singularity as `w` approaches the critical line. Burnol proves that `Q_lambda V psi(w,k)` has a
limit by introducing

```text
phi(w,k)(t) = lim_(delta->0) integral_delta^1
  (log(1/v))^k v^(-w) d/dv [sin(2*pi*t/v)/(pi*t/v)] dv.
```

For `k=0`, BBLS Lemmas 4 and 6 provide holomorphy and the uniform estimates. For `k>=1`, Burnol
rewrites the oscillatory integral and obtains the explicit small-`t` series

```text
phi(w,k)(t) = d^k/dw^k [U(w)t^(-w)]
  + 2*(-1)^k*k! * sum_(j>=1)
      (-1)^j (2*pi*t)^(2j)/(2j+1)! * 2j/(w+2j)^(k+1).
```

Applying `(1-M)^2`, then `Q_lambda`, yields one lambda-independent square-integrable majorant:

```text
O(1)                         on [lambda,1],
O((1+log t)^2/t)             on [1,infinity),
0                            on (0,lambda).
```

Dominated convergence gives the physical `L2` limit, and the inverse phase isometry gives `Y`.
These physical estimates are indispensable input to F3's Gram asymptotics. A proof that merely
produces some vector with the right pairings is therefore insufficient.

## Lean Inventory

Already available:

- the complex Fourier-Mellin `L2` isometry and explicit representatives;
- `hasMellin_burnolA` and the explicit model kernels;
- a local pattern for multiplication by a unit-modulus measurable frequency function;
- countability/nullity and almost-everywhere nonvanishing of zeta on the critical line;
- `MemLp.indicator`, dominated convergence, Mellin differentiation, complex analytic order, and
  `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`;
- submodule span induction and orthogonal-complement membership APIs.

Not available as a packaged theorem:

- the physical time-reversal isometry for Lebesgue `L2(0,infinity)`;
- the cutoff multiplication operator as a self-adjoint `L2` projection;
- the Baez-Duarte `V` phase and its physical action on `A`;
- the sine-kernel Mellin identity needed for `U psi`;
- the BBLS Lemma 4/6 oscillatory improper-integral estimates;
- local-uniform complex differentiation of the full oscillatory kernel;
- the lambda-independent transformed representative bounds used by F3.

## Fixed Implementation Boundary

F2 remains one indivisible completion batch with two internal gates.

Gate A must compile the total phase `V`, its inverse, the positive-half-line complex `L2`
isometry, normalized dilation commutation, time reversal of `A`, `Q_lambda`, `psi(w,k)`, and the
exact pre-boundary pairing for `re(w)<1/2`.

Gate B must compile the oscillatory kernel continuation, its equality with the transformed
left-half-plane vector, the source uniform estimates, the exact critical-line `L2` limit,
lambda-independent physical representative bounds, the boundary pairing, and zero-order
orthogonality to the entire model span.

Gate A alone is `FORMALIZATION_ONLY` and leaves F2 open. No F3 theorem may begin until both gates
compile without unchecked premises.

## Frontier

- `hard_gap_before`: G4/F2 open and selected; F3-F5 open; M2/G3 historically unselected (open under V4.1).
- `hard_gap_after`: G4/F2 remains open and selected with its exact source boundary recovered;
  F3-F5 and M2/G3 are unchanged.
- `hard_gap_delta`: zero theorem edges closed; the false identification of `T` with `V` and the
  hidden BBLS oscillatory dependency are removed from the planning assumptions.
- `assumption_frontier_before`: F2 was summarized as a generic projected boundary limit after F1.
- `assumption_frontier_after`: F2 explicitly requires the second phase, physical cutoff,
  oscillatory continuation, source estimates, dominated `L2` convergence, and order-to-
  orthogonality bridge. No premise is added.
- `next_admitted_batch`: the preregistered indivisible F2 implementation. Partial Gate A work must
  remain inside that batch and may not be published as F2 completion.
