# Tier 2 Inventory: Li / Hadamard Route

Date: 2026-07-09

Target: `T2.inventory.li.hadamard`

## Inventory Question

Does the current local project plus mathlib have enough support to make a useful structural route
through Li's criterion and a Hadamard product for the xi function?

## Useful Infrastructure Found

- Local xi bridge:
  - `riemannXi_eq_mul_completedRiemannZeta`
  - `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`
  - `analyticAt_riemannXi`
  - local logarithmic derivative facts around `1`
- Zeta zero set API:
  - `riemannZetaZeros`
  - `mem_riemannZetaZeros`
  - `isClosed_riemannZetaZeros`
  - `isDiscrete_riemannZetaZeros`
  - `IsCompact.inter_riemannZetaZeros_finite`
- Local analytic and zero-order API:
  - `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
  - `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`
  - `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq_zero`
- Meromorphic divisor API:
  - `MeromorphicOn.divisor`
  - `MeromorphicOn.divisor_apply`
  - `AnalyticOnNhd.divisor_apply`
  - divisor algebra lemmas for products and sums
- Local canonical decomposition API on balls:
  - `canonicalFactor`
  - `meromorphic_canonicalFactor`
  - `analyticOnNhd_canonicalFactor`
  - `meromorphicOrderAt_canonicalFactor`
  - `canonicalFactor_eq_zero_iff`
  - `_root_.MeromorphicOn.exists_canonicalDecomp`
- Jensen and value-distribution support:
  - `MeromorphicOn.circleAverage_log_norm`
  - `AnalyticOnNhd.circleAverage_log_norm`
  - `AnalyticOnNhd.sum_divisor_le`
  - `logCounting`
  - `locallyFinsuppWithin.logCounting_divisor`
  - `logCounting_isBigO_one_iff_analyticOnNhd`
- Log-derivative support:
  - `Complex.deriv_log_comp_eq_logDeriv`
  - `MeromorphicOn.logDeriv`
  - `Meromorphic.logDeriv`
- Completed-zeta support:
  - `RiemannHypothesis`
  - `riemannZeta`
  - `completedRiemannZeta`
  - `completedRiemannZeta₀`
  - the functional equation for `completedRiemannZeta₀`

## Missing Pieces For A Direct Structural Route

- No direct mathlib statement of Li's criterion was found.
- No global Hadamard product or canonical product theorem for entire functions over all zeros was
  found. `Analysis/Complex/Hadamard.lean` is a three-lines theorem file, not the product theorem.
- No ready global zero enumeration with multiplicity for `riemannXi` or completed zeta was found.
  The zeta-zero API is a set-level API, while a Li/Hadamard route needs a divisor or locally finite
  indexed family with multiplicities.
- No ready bridge from the Taylor coefficients of `s * log (riemannXi s)` at `1` to a zero-sum
  expression was found.
- No ready order-one growth theorem for the project-local `riemannXi` was found, and such a theorem
  is needed before a classical xi Hadamard product can be stated cleanly.

## Recommendation

Do not choose Li/Hadamard as the immediate Tier 2 proof route.

The local analytic infrastructure is strong enough for small bridge lemmas, but the route is not yet
ready as a direct structural attack. If this route is reopened later, the first proof-engineering
targets should be:

- package `riemannXi` or `completedRiemannZeta₀` as a global entire object;
- build a local divisor for `riemannXi` on balls and relate its support to
  `IsNontrivialZero` plus the trivial-zero exclusion;
- prove finite local zero-counting statements for `riemannXi`;
- only then investigate canonical decomposition, Jensen, and log-counting as possible bridges
  toward a product or coefficient identity.

Next route: complete the Nyman-Beurling inventory before making the `T2.pivot` decision.
