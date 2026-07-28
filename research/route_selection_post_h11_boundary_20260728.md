# Route Selection after H11 Moving-Window Boundary

Date: 2026-07-28

Status: `RERANK_COMPLETE / H0_CHEBYSHEV_MELLIN_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H11-MOVING-WINDOW-BOUNDARY-01` is publicly closed at final-ledger
commit `a79f218d97f41d27d59ec12293927882d1069283`, Lean Action run `30339249648`, build job
`90210877424`, in `1m37s`.

Its frozen source proves the exact moving-window pair-overlap expansion, the nonnegative local
top-boundary remainder, its `U * boundaryCount^2` bound, and an actual multiplicity-expanded
zeta specialization. It corrects only termwise bookkeeping inside the source `O(L^2)` error.
Fujii's estimate, PCC, absolute last-exception control, H11, and RH remain open.

## Fresh cross-family comparison

This rerank applies the user's historical omission-search priority. A route receives priority
when the repository already contains both sides of an important historical inference but has not
checked their exact bridge.

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H0 Riemann/von Koch | Connect the actual Chebyshev `psi` partial sums to the von Mangoldt L-series, its Mellin representation, and the half-plane selected by a prime-error exponent. | The project has deep xi/Weil explicit formulas, while the classical prime-counting error route has no dedicated Target. Mathlib now supplies the source arithmetic objects but lacks the cancellation-based L-series convergence theorem needed for the bridge. | **Select.** |
| H1 mollifier | Prove the open arbitrary-length mollified mean value or a source-backed weaker input that still reaches the compiled Bettin--Gonek consumer. | Direct RH value remains high, but no new mean-value input appeared in this rerank. | Retain open. |
| H2 bow exclusion | Exclude one actual off-line zero bow using density or moment estimates. | Direct RH value is maximal; audited estimates still lose the required sparse local information. | Retain open. |
| H7 spectral | Prove convergence of finite source operators and ground states to a true xi object. | The finite certificate layer is deep, but the continuum source data remain broad. | Retain open. |
| H9 Franel | Order the existing reduced Farey pairs and prove Franel's exact squared-discrepancy identity. | Strong historical successor with a located primary source. It remains the leading next candidate, but H9 was recently advanced while H0's prime-error edge is still absent. | Queue next. |
| H10 function field | Transfer finite power-sum rigidity through actual curve/cohomology data. | High analogy value; the missing geometric realization remains broad. | Retain open. |
| H12 Speiser | Complete the global Levinson--Montgomery count theorem. | Source-exact and important, but already heavily reconstructed without a new global contour input. | Retain open. |

## Source finding that fixes the node

Riemann's 1859 memoir writes `log zeta(s) / s` as the Mellin transform of his weighted
prime-counting function and then uses vertical inversion. Von Koch differentiates the Euler
product, introduces the prime-power logarithmic counting function, and derives prime-counting
errors from zero locations. The exact modern arithmetic coefficient is the von Mangoldt function,
and its summatory function is Chebyshev's `psi`.

The current Mathlib checkout contains:

```text
Chebyshev.psi x = sum_{n <= x} vonMangoldt(n),
L_vonMangoldt(s) = -zeta'(s) / zeta(s)       for Re(s) > 1,
LSeries_eq_mul_integral                      after convergence is supplied.
```

What it does not expose is the cancellation theorem needed by the reverse prime-error channel:

```text
sum_{n <= N} a(n) = O(N^r)
  implies
sum a(n) / n^s converges for Re(s) > r.
```

For `a(n)=vonMangoldt(n)-1`, the partial sum is exactly `psi(N)-N`. Proving this generic theorem
and its exact specialization distinguishes the true von Koch exponent from the unconditional
absolute-convergence line.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H0-CHEBYSHEV-MELLIN-01`.
- `node`: `H0-RIEMANN-VON-KOCH-PSI-MELLIN-01`.
- `mode`: `LITERATURE`.
- `positive_endpoint`: cancellation-based L-series convergence from partial-sum growth; exact
  `psi`/von-Mangoldt partial sums; source Mellin formulas; floor-corrected error coefficients;
  and a theorem sending any registered `psi(N)-N = O(N^r)` bound to convergence throughout
  `Re(s)>r`.
- `open_analytic_edge`: prove locally uniform convergence or an analytic integral continuation
  on the same half-plane, identify it with the continued zeta logarithmic derivative, and exclude
  zeros by the pole-removed zeta differential equation.
- `negative_controls`: no unconditional RH-strength error bound, no inference from pointwise
  convergence to holomorphy, no use of the totalized logarithmic derivative at a zeta zero, no
  deletion of the floor correction, and no RH claim.
- `strict_boundary`: von Koch's RH-equivalent error estimate, analytic continuation from the
  conditional Dirichlet series, zero exclusion, H0/H9, and RH remain open.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public Lean
  Action CI.
