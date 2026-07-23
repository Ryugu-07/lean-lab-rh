# H1 Bettin--Gonek Mellin Identity Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`

Production module: `LeanLab/Riemann/BettinGonekMellinIdentity.lean`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Source coordinates

Primary source: Bettin--Gonek, *The theta=infinity conjecture implies the Riemann hypothesis*,
arXiv:1604.02740, equation `(2.1)`. For `s=1/2+i*t` the source writes

```text
M_x(s) log x = sum_{n <= x} mu(n) n^(-s) log(x/n)

H_t(w) = integral_1^infinity M_x(s) log x x^(-w) dx
       = 1 / ((w-1)^2 zeta(w-1/2+i*t)),  Re(w)>3/2.
```

The Lean proof starts from the existing real-cutoff `farmerMollifier`; it does not introduce an
abstract function with the desired transform.

## Object map

| source object | Lean object | alignment |
| --- | --- | --- |
| `M_x(s)` | `farmerMollifier x s` | Existing literal Mobius mollifier with real cutoff `n<=floor x` and logarithmic taper. |
| `M_x(s) log x` | `bettinGonekLogMollifier x s` | Multiplication cancels the taper denominator for `x>1`. |
| `mu(n)n^(-s)log(x/n) 1_(n<=x)` | `bettinGonekMollifierSeriesTerm s n x` | Uses the actual Mobius `LSeries.term` and `Ici n` support. |
| `log(x/n)x^(-w)` | `bettinGonekLogKernel n w x` | Literal scaled logarithmic kernel. |
| weighted source term | `bettinGonekMellinSeriesTerm s w n x` | Product of `x^(-w)` with the supported Mobius term. |
| source integrand | `bettinGonekWeightedMollifier t w x` | `x^(-w) M_x(1/2+i*t) log x`. |
| source `H_t(w)` | `bettinGonekH t w` | Set integral over the literal interval `(1,infinity)`. |

## Real-cutoff and boundary alignment

Lean proves both the finite formula over `Finset.Icc 1 floor(x)` for `x>1` and the pointwise
infinite supported formula for every real `x`. The `n=0` L-series term is zero. At `x=1`, the only
potential active term has `log(1)=0`; for `x<1` every positive-natural term is inactive. Hence no
boundary or lower-interval correction is inserted when the full-line integral is restricted to
`(1,infinity)`.

## Kernel and Fubini boundary

For positive `n` and `Re(w)>1`, the substitution `x=n*u` is compiled with the principal complex
power on positive reals and gives

```text
integral_n^infinity log(x/n) x^(-w) dx = n^(1-w)/(w-1)^2.
```

On the critical line, the integrated norm of the `n`th term is bounded by

```text
n^(1/2-Re(w)) / (Re(w)-1)^2.
```

This majorant is summable exactly under the source condition `Re(w)>3/2`. The proof uses this
bound to establish Bochner integrability of the pointwise `tsum` and to invoke the sum-integral
exchange theorem. Thus the equality is not obtained by formally interchanging a conditionally
convergent series.

## Mellin and reciprocal-zeta alignment

Mathlib defines `mellin f q` with weight `x^(q-1)`. The source weight `x^(-w)` therefore uses
parameter `q=1-w`. After integrating one Mobius term, Lean proves the exact exponent identity

```text
mu(n) n^(-s) n^(1-w) = LSeries.term(mu, w+s-1, n).
```

For `s=1/2+i*t` and `Re(w)>3/2`, the argument `w+s-1` has real part greater than one, so the
compiled theorem `LSeries_moebius_eq_reciprocal_riemannZeta` applies. The final source-normalized
identity is

```text
bettinGonekH t w =
  1 / ((w-1)^2 * riemannZeta (w-1/2+t*i)).
```

## Claim boundary and next edge

This campaign closes equation `(2.1)` and packages it as both `HasMellin` and the named `H_t`
equality. It proves no inverse Mellin theorem for the source auxiliary function, no support or
boundedness for `g_t`, no vertical decay for `G_t`, no contour shift, no selected-residue lower
bound, no moment-to-power bridge, no Farmer arbitrary-length moment conjecture, and no RH.

The next H1 analytic edge is to construct the inverse Mellin object with enough support,
boundedness, and decay to justify the convolution and contour movement. Cross-route selection
must compare that edge with the still-open H7 archimedean source block and other historical
mechanisms.

## Mechanical status

- Production module: 576 lines; standalone warning-as-error compile passed.
- Targets: one new proven actual-mollifier Mellin-identity Target.
- Exact TargetChecks: 12 new witnesses compile.
- Axiom audit: 9 selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Direct production, registry, and module builds pass.
- Production forbidden scan is empty; `git diff --check` passes.
- Full build: 8,755 jobs, passed with inherited replay warnings only.
- Frozen implementation: commit `1ca590891a51da76712e8a2dd177287de56d0b43` passed public Lean
  Action run `29976558428`, build job `89109449098`, in `2m6s`; proof source is frozen.
- Immutable-evidence publication and its public Lean Action CI remain.
- `rh_frontier_delta=0`; `hard_gap_delta=0`; `source_mellin_bridge_delta=1`.
