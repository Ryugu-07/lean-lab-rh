# H1 Bettin--Gonek J-Contour Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-J-CONTOUR-01`

Selected node: `H1-BETTIN-GONEK-J-CONTOUR-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `IMPLEMENTED_LOCAL / FROZEN_IMPLEMENTATION_PENDING`

## Baseline

- `parent_commit`: `64782a564a19a8e9c25a0d520bcbbcb2397b807a`.
- `parent_public_ci`: Lean Action run `29980056767`, build job `89119806051`, passed in `1m36s`.
- `route_selection`: `research/route_selection_post_h7_archimedean_tail_density_20260723.md`.
- `global_goal`: active; RH remains open.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.

## Primary source alignment

The fixed source is Bettin--Gonek, arXiv:1604.02740, equations `(2.3)`--`(2.5)`. For a selected
nontrivial zero `rho` with `1/2<=Re(rho)`, real `t`, and `x>=2`, the product of the source
auxiliary transform and mollifier Mellin transform cancels to

```text
(w-3/2+i*t) x^w /
  ((w-(rho+1/2-i*t)) (w+1)^2 (w+i*t+1)^4).
```

Moving the line from `Re(w)=3` to `Re(w)=0` crosses only
`p=rho+1/2-i*t` and gives equation `(2.5)`. The boundary-line integral is `O(1)` uniformly in
`x`, since `|x^(i*y)|=1`. The residue has norm equal to a fixed positive scale times
`x^(Re(rho)+1/2)`.

## Fixed Lean endpoint

Create `LeanLab/Riemann/BettinGonekJContour.lean` and prove all of the following from the literal
source objects.

1. On `Re(w)>3/2`, identify
   `bettinGonekAuxiliaryG rho t w * bettinGonekH t w * x^w` with
   `bettinGonekJKernel rho t x w`, using the compiled actual-mollifier Mellin identity rather than
   an abstract transform value.
2. Define the normalized infinite vertical-line integral of `bettinGonekJKernel`, and prove
   vertical integrability on `Re(w)=0` and `Re(w)=3` for every `x>0`.
3. For finite symmetric rectangles whose height exceeds the selected pole ordinate, prove the
   exact one-pole residue identity. Prove both horizontal edge integrals tend to zero as the
   height tends to infinity.
4. Deduce the infinite contour formula matching source equation `(2.5)`:

```text
JLine(rho,t,x,3) = JLine(rho,t,x,0) +
  bettinGonekResidueCoefficient rho t x.
```

5. Prove an `x`-uniform boundary estimate: for fixed `rho,t`, there is a finite nonnegative
   constant `C` such that every `x>0` satisfies `norm(JLine(rho,t,x,0))<=C`.
6. Define the source residue scale, prove it is strictly positive, and prove the exact identity

```text
norm(bettinGonekResidueCoefficient rho t x)
  = residueScale(rho,t) * x^(Re(rho)+1/2).
```

7. Combine the contour identity, boundary bound, and residue norm into the source lower inequality
   placing the selected-zero power below `norm(JLine(...,3))+C`.

The final theorem must package items 1--7 and be registered as one proven Target only after all
mechanical gates pass.

## Decision criteria

- `FULL_SUCCESS_AT_J_CONTOUR_ENDPOINT`: all seven items compile, including finite-to-infinite
  contour passage, uniform boundary bound, exact residue norm, TargetChecks, axiom audit, full
  build, and public evidence gates.
- `PARTIAL_CONTOUR_ONLY`: the finite or infinite contour identity compiles but the `x`-uniform
  boundary majorant or selected-residue lower inequality does not. Record the exact integrability
  or norm obligation; do not register the aggregate endpoint.
- `SOURCE_MISMATCH`: the compiled `G_tH_t` product, contour orientation, `2*pi*i` normalization,
  or selected residue differs from equations `(2.3)`--`(2.5)`. Stop and register the mismatch.
- `PREMISE_CREEP`: the proof requires an assumed vertical-decay, contour-shift, or boundary-bound
  proposition instead of deriving it for the actual rational kernel. Stop without a proven Target.

## Known obstacles

- The selected pole has variable imaginary part, so the finite rectangle must carry the explicit
  height condition before the limit.
- The other rational poles lie on `Re(w)=-1` and must remain outside the closed rectangle.
- Horizontal decay must be uniform over real parts in `[0,3]`; pointwise vertical integrability is
  not enough.
- The infinite line normalization must account for `dw=i dy`, turning `1/(2*pi*i)` into
  `1/(2*pi)`.
- The residue lower term must retain the exact exponent `Re(rho)+1/2` and a strictly positive
  denominator scale.

## Claim boundary

No theorem in this campaign may claim inverse Mellin support or boundedness for `g_t`, vertical
decay of `G_t` alone, the Mellin convolution identity, equation `(2.4)`, the full
moment-to-power bridge, Farmer's moment conjecture, H1, or RH. No open proposition may be used as a
premise. An abstract meromorphic kernel does not satisfy the endpoint.

## Mechanical gates

No `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, or resource-limit
relaxation. Require direct warning-as-error compilation, exact TargetChecks, selected transitive
`#print axioms`, an empty forbidden scan, `git diff --check`, full `lake build`, frozen
implementation CI, immutable-evidence CI, and final-ledger CI.

The six inherited user/exposure files remain untouched and unstaged.

## Local result

All seven fixed items now compile in `LeanLab/Riemann/BettinGonekJContour.lean`. The literal
`G_t H_t x^w` product is the source rational kernel; both vertical lines are integrable; the
finite rectangle crosses exactly the selected pole; both horizontal sides tend to zero from a
derived `O(|u|^-4)` bound; and the normalized infinite identity is
`JLine(3)=JLine(0)+residue`. Lean proves `norm(JLine(0))<=2`, strict positivity of the residue
scale, the exact residue norm, and the selected-zero lower inequality with constant `2`.

The exact TargetCheck and selected transitive axiom audit pass. The forbidden scan is empty,
`git diff --check` passes, and the full 8,757-job build succeeds. No inverse Mellin, standalone
`G_t` decay, convolution, moment transfer, Farmer conjecture, H1, or RH claim is introduced.
Public frozen-implementation evidence is still required.
