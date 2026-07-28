# Route Selection after H0 Chebyshev--Mellin

Date: 2026-07-28

Status: `RERANK_COMPLETE / H9_FRANEL_RANK_MERTENS_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H0-CHEBYSHEV-MELLIN-01` is publicly closed at final-ledger
commit `71705474e8d38968c39400a2455745c519a31818`, Lean Action run `30343150121`, build job
`90223131928`, in `2m0s`.

Its frozen source proves the cancellation-preserving naturally ordered Dirichlet--Mellin bridge,
the exact actual Chebyshev/von-Mangoldt identities, the floor correction, and a compiled
counterexample to identifying ordered convergence with Mathlib's absolute `LSeriesSummable`.
The RH-strength Chebyshev error estimate, local uniform continuation, reverse zero exclusion,
H0, and RH remain open.

## Fresh cross-family comparison

This rerank uses historical omission value, direct relation to an open RH edge, exact source
availability, and whether the repository already contains both sides of a missing inference.
Proof convenience is not a ranking field.

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy/mollifier | Prove Hardy's source Abel moment law or an arbitrary-length mollified moment strong enough for the compiled Bettin--Gonek consumer. | Direct RH value is high, but this rerank found no new convergence or long-mean-value input beyond the already isolated blockers. | Retain open. |
| H2 bow exclusion | Exclude an actual slowly bending off-line zero configuration using density or moment information. | Direct RH value is maximal; the known estimates still lose the required sparse local information. | Retain open. |
| H7 spectral | Prove true finite-prime operator convergence and preserve ground-state orientation in the limit. | The finite source calculus is deep, but the missing continuum compactness and source convergence remain broad. | Retain open. |
| H9 Franel | Order the compiled reduced Farey set, reconstruct one-based rank discrepancy, and prove the exact Franel Mertens quadratic formula. | The project now has the actual finite Farey/Mertens transform but not the ordered geometry that Franel used. The primary source gives a finite exact identity, so endpoint and convention errors are falsifiable. | **Select.** |
| H10 function field | Realize the finite Frobenius rigidity interface from actual curve/cohomology data and test number-field transfer. | High structural value; the required geometric realization is still much broader than the present finite API. | Retain open. |
| H12 Speiser | Complete the global Levinson--Montgomery zero-count comparison. | Source-exact and important, but no new global contour or counting input appeared after the previous reconstruction. | Retain open. |

H9 is not selected by implementation inertia. It was explicitly deferred after the earlier
Farey transform campaign while H11 and H0 were explored. H0 is now publicly closed, and no new
input changes the larger H1/H2/H7/H10/H12 blockers. The still-missing Franel order-to-Mertens
bridge is therefore the highest-value bounded historical edge in this comparison.

## Source finding

Franel's 1924 paper orders the Farey fractions and studies their deviation from equally spaced
points. Landau's immediately following note connects the Farey statement to the Mertens
criterion. Kanemitsu--Yoshimoto 1996, Theorem 3, states an exact finite identity for the positive
Farey convention:

```text
delta_nu = rho_nu - nu / Phi(N),

sum_{nu=1}^{Phi(N)} delta_nu^2
  = 1 / (12 * Phi(N)) *
      (sum_{m,n<=N}
        M(floor(N/m)) * M(floor(N/n)) * gcd(m,n)^2 / (m*n) - 1).
```

Their `rho_1,...,rho_Phi(N)` are the increasing positive reduced fractions with denominator at
most `N`; `rho_Phi(N)=1`. They introduce `rho_0=0` only as a supplement. Thus the existing
project convention `0<a<=q<=N`, which excludes `0/1` and includes `1/1` once, matches the
summation in Theorem 3.

The existing module `LeanLab/Riemann/FareyMobiusWeyl.lean` already proves:

```text
F_N(f) = sum_{1<=n<=N} M(floor(N/n)) * V_f(n),
```

for the actual duplicate-free Farey pair set. The missing source inference is to specialize this
transform to the counting/rank function, expose the pointwise block remainder, square it, and
evaluate the finite remainder correlation as the gcd kernel.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H9-FRANEL-RANK-MERTENS-01`.
- `node`: `H9-FRANEL-RANK-MERTENS-QUADRATIC-01`.
- `mode`: `LITERATURE`, with mandatory finite `FALSIFICATION` controls.
- `full_endpoint`: actual rational-value ordering and one-based rank; pointwise Mertens block
  remainder; exact squared correlation expansion; and the complete finite Franel
  Mertens/gcd identity.
- `meaningful_partial`: all ordering, rank, count-transform, pointwise discrepancy, and exact
  Mertens correlation quadratic statements compile, while the remaining source gcd-kernel
  collapse is recorded as an explicit finite Dedekind/sawtooth correlation obstacle.
- `negative_controls`: no lexicographic pair ordering, no zero-based rank, no inclusion of
  `0/1`, no omission or duplication of `1/1`, no floating-point comparison, no division by the
  zero cardinality at `N=0`, and no claim that the exact finite identity supplies the
  RH-equivalent asymptotic estimate.
- `strict_boundary`: the Franel asymptotic estimate, Mertens square-root cancellation, H9, and
  RH remain open even if the exact identity compiles.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public Lean
  Action CI.

