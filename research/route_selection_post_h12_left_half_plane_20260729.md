# Route Selection after H12 Left-Half-Plane Winding

Date: 2026-07-29

Status: `H8_CONREY_LI_HALF_STRIP_SELECTED`

## Closed parent

Campaign `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01` is publicly closed at
closure-receipt commit `5861e2fcc0eacaef93db3a665cb29df7ca79d790`, Lean Action run
`30404007167`, build job `90425190201`, in `1m35s`.

That campaign closes only the strict-left principal-log winding inference and its actual
horizontal `zeta'/zeta` endpoint formula. Actual strict-negative height production, the global
indented argument principle, Jensen top variation, the count outputs, H12, and RH remain open.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H8 Conrey--Li Hardy RKHS | Reconstruct the second half of Theorem 2: restricted kernel-center density, contractive multiplier extension, adjoint analytic continuation, and the half-strip Cayley bound. | The first RKHS stage compiles, but the printed continuation argument has never been kernel-checked. It contains exact well-definedness, density, conjugation, and analytic-extension hinges. | **Select.** |
| H1 Hardy/Selberg/Levinson | Prove Hardy's Abel source law, Selberg's global moments, or an arbitrary-length mollified moment. | These are direct and important, but every current successor requires a new global estimate rather than an untested bounded source inference. | Retain open. |
| H2 classical density | Prove the inverse Mellin line and global contour shift for the actual detector. | The first missing theorem is exact, but it starts a broad analytic package and no new inversion input has appeared. | Retain open. |
| H7 spectral/trace | Construct the infinite arithmetic operator and control its trace limit. | Finite source calculus compiles; the missing infinite producer remains broad. | Retain open. |
| H10 function fields | Construct actual curve intersections, Hodge index, and Frobenius point-count identities. | The numerical consumer compiles, but the geometric producer needs substantial absent algebraic-geometry infrastructure. | Retain open. |
| H11 zero statistics | Find an absolute-error source statistic that detects a persistent sparse off-line orbit. | Existing normalized errors absorb sparse exceptions; no source-backed amplifier is fixed. | Retain open. |
| H12 Speiser | Assemble the global indented contour and Jensen top estimate. | The exact local topological step has just closed; immediate continuation would be route inertia. | Retain open. |

H8 is not adjacent-route continuation. Since its first stage publicly closed, the project has
intervened on Selberg sign changes, the classical zero detector, Turing completeness, Conrey
character sums, and Levinson--Montgomery winding.

## Primary-source lock

The fixed source is J. Brian Conrey and Xian-Jin Li,
*A note on some positivity conditions related to zeta- and L-functions* (1998), Theorem 2:

<https://arxiv.org/abs/math/9812166>

After deriving the upper-half-plane Cayley transform

```text
B(z) = (W(z)-W(z+i))/(W(z)+W(z+i))
```

with norm at most one, the source introduces the Hardy space on `Im z > -1/2` with kernel

```text
L(w,z) = 1 / (2*pi*i*(conj(w)-z-i)).
```

It defines a kernel multiplier on centers with `Im w>0`, extends it from their dense span to a
contraction, uses the adjoint on one kernel vector to continue `B`, and then continues the
pointwise multiplier identity to prove `|B|<=1` throughout the half-strip.

## Omission-sensitive hinges

The source proof requires all of the following:

1. the multiplier rule on finite kernel combinations is well-defined;
2. positive definiteness gives the exact contraction inequality;
3. centers restricted to `Im w>0` are dense in the larger half-strip Hardy space;
4. the adjoint formula respects the complex-inner-product conjugation convention;
5. the denominator used to continue `B` never vanishes in `Im w>-1/2`;
6. the continuation is independent of the selected kernel center;
7. the multiplier identity extends analytically before the global norm bound is used.

The paper-level argument may be correct. A failure under the literal hypotheses must identify
the first one of these hinges, not silently assume the desired continuation.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`.
- `node`: `H8-CONREY-LI-HALF-STRIP-EXTENSION-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: construct the source half-strip Hardy RKHS with its exact kernel; prove
  density of upper-half-plane kernel centers; construct the contractive kernel multiplier and
  its adjoint; produce an analytic extension of the actual upper Cayley transform; and prove
  norm at most one throughout `Im z>-1/2`.
- `meaningful_partial`: compile the exact half-strip domain and kernel algebra, restricted-center
  density for an analytic RKHS, and the full adjoint continuation and norm-bound consumer under
  an explicit contractive kernel-multiplier premise; record the first failed concrete Hardy-space
  or multiplier-construction theorem exactly.
- `negative_controls`: no density from unrestricted kernel centers alone; no promotion of a
  bounded upper-half-plane function without the Hardy multiplier; no conjugation swap; no
  claim that a supplied contraction has been constructed; no actual-xi specialization.
- `strict_boundary`: no construction of the concrete `F(W)` or positive shift for
  `W=1/xi(1-i*z)`, no source value-distribution theorem, no H8 result, and no RH result.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
