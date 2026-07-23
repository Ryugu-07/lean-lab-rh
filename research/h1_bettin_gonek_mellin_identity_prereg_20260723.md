# H1 Bettin--Gonek Mellin Identity Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`

Selected node: `H1-BETTIN-GONEK-H-MELLIN-IDENTITY-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Baseline

- `parent_commit`: `26a6f93ccc4b7532f21b50acc2ffbb1debfd338c`.
- `parent_public_ci`: Lean Action run `29973710220`, build job `89100966535`, passed in `1m33s`.
- `global_goal`: active; RH remains open.
- `route_selection`: `research/route_selection_post_h7_weil_prime_block_20260723.md`.
- `production_gate`: no production Lean source may be created before this preregistration commit
  passes public Lean Action CI.
- `preregistration_gate`: commit `3dfe6e96bbbb57474aa241630a3624c4ed290b3d` passed public Lean
  Action run `29974255134`, build job `89102575415`, in `1m49s`; production editing began only
  after this gate.

## Primary source alignment

The fixed source is Bettin--Gonek, [arXiv:1604.02740](https://arxiv.org/abs/1604.02740), equations
`(2.1)`--`(2.2)`. For real `x>1`,

```text
M_x(s) log x = sum_{n <= x} mu(n) n^(-s) log(x/n),
```

and for `s=1/2+it`, `Re(w)>3/2`,

```text
H_t(w) = integral_1^infinity M_x(s) log(x) x^(-w) dx
       = 1 / ((w-1)^2 zeta(w+s-1)).
```

Mathlib's Mellin convention is `mellin f q = integral_0^infinity x^(q-1) f(x) dx`. Therefore the
source integral must be represented at Mellin parameter `q=1-w`. Since `farmerMollifier x s=0`
for `x<=1`, no extra lower-interval term is permitted.

## Fixed Lean endpoint

1. Define the source weighted mollifier `farmerMollifier x s * log x` and the individual Mobius
   logarithmic source term supported on `x>=n`.
2. Prove pointwise that the actual real-cutoff `farmerMollifier`, after multiplication by
   `log x`, equals the source finite sum and the corresponding infinite sum with inactive terms
   equal to zero.
3. Prove the scaled kernel identity
   `integral_(n,infinity) log(x/n) * x^(-w) dx = n^(1-w)/(w-1)^2`
   for positive natural `n` and `1<Re(w)`, including integrability.
4. For `s=farmerCriticalLinePoint t` and `3/2<Re(w)`, construct a summable norm majorant for the
   individual source terms and justify exchanging the Mobius sum with the Mellin integral.
5. Identify the resulting exponent as `w+s-1`, invoke the project theorem
   `LSeries_moebius_eq_reciprocal_riemannZeta`, and prove the exact source value.
6. Package convergence and value as a `HasMellin` theorem at parameter `1-w`, plus a named
   `bettinGonekH` equality in the displayed source normalization.

## Decision criteria

- `FULL_SUCCESS_AT_MELLIN_ENDPOINT`: all six items compile without `sorry`; exact TargetChecks,
  selected axiom prints, full build, and all public evidence gates pass.
- `PARTIAL_KERNEL_ONLY`: the pointwise source formula and scaled kernel compile, but the absolute
  series-interchange proof does not. Record the exact failed summability or measurability
  obligation; do not register the `H_t` identity as proven.
- `SOURCE_MISMATCH`: the existing real-cutoff mollifier, Mellin exponent convention, or Mobius
  coefficient produces a different exponent or normalization. Stop and register the mismatch.
- `FALSIFICATION_VALUE`: Lean identifies an omitted boundary term at `x=1`, a failure of absolute
  convergence under `Re(w)>3/2`, or a mismatch between the finite floor cutoff and the source
  condition `n<=x`.

## Claim boundary

The campaign proves only the first displayed Mellin identity in the Bettin--Gonek analytic chain.
It proves no inverse Mellin theorem for `G_t`, no support or boundedness for `g_t`, no vertical
decay, no contour shift, no selected-residue lower bound, no moment-to-power bridge, no Farmer
moment bound, and no RH.

An abstract function carrying the desired Mellin transform cannot satisfy the endpoint. The proof
must start from the existing `farmerMollifier` and use the literal Mobius coefficients and
real-cutoff condition.

## Local result

Decision: `FULL_SUCCESS_AT_MELLIN_ENDPOINT`; immutable evidence and final-ledger CI remain for
campaign closure.

All six fixed items compile. The actual real-cutoff mollifier equals both the finite source sum
and the pointwise supported `tsum`; the scaled kernel is integrable with the exact source value;
the integrated norms admit the summable majorant `n^(1/2-Re(w))/(Re(w)-1)^2`; Bochner Fubini is
justified; and the resulting Mobius L-series gives the exact reciprocal-zeta `H_t` formula. The
endpoint is packaged as `HasMellin` at parameter `1-w` and as
`bettinGonekMellinIdentity_endpoint`.

No source mismatch or omitted `x=1` boundary term was found. The claim boundary above is
unchanged.

The 576-line production module compiles standalone with warnings as errors. Twelve exact
TargetChecks, nine selected standard-only axiom prints, the empty production forbidden scan,
`git diff --check`, and the full 8,755-job build pass locally.

Frozen implementation commit `1ca590891a51da76712e8a2dd177287de56d0b43` passed public Lean
Action run `29976558428`, build job `89109449098`, in `2m6s`. Proof source is frozen; only
immutable evidence and final-ledger publication remain for campaign closure.

Immutable-evidence commit `17a1c46f2cb62c1aa351d2d918e872f1cbc9340e` passed public Lean
Action run `29976815386`, build job `89110232514`, in `1m53s`. Only docs-only final-ledger CI
remains for campaign closure.

## Mechanical gates

Production code must pass direct compilation, exact TargetChecks, selected `#print axioms`, an
empty forbidden-token scan, `git diff --check`, and the full `lake build`. Publication requires a
frozen implementation CI, immutable-evidence CI, and final-ledger CI. The proof source is frozen
after implementation CI.
