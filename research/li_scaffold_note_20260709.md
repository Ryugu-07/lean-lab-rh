# Local Xi and Li Scaffold Note

Date: 2026-07-09

This note summarizes the verified Tier 1 scaffold in `LeanLab.Riemann`. It is a
result note for the local definitions and theorem chain in this repository. It
does not claim a Li-criterion formalization, an all-coefficients theorem, or a
proof of the Riemann Hypothesis.

## Source Files

- `LeanLab/Riemann/Basic.lean`: project predicates and the RH orientation theorem.
- `LeanLab/Riemann/LiScaffold.lean`: local xi/Li scaffold and proof chain.
- `LeanLab/Riemann/Targets.lean`: compiled target ledger.
- `research/blueprint.md`: proof-engineering DAG and route notes.
- `attempts/riemann_hypothesis_initial.md`: loop-by-loop attempt log.

## Verified Local Xi Bridge

The local function `riemannXi` is related to mathlib's completed zeta expression
away from the pole-removal points by:

- `riemannXi_eq_mul_completedRiemannZeta`

The local zero predicate bridge is packaged as:

- `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`

The reverse direction was split through Gamma-factor edge cases before packaging:

- `isZetaZero_of_riemannXi_eq_zero`
- `completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`
- `riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`
- `eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero`
- `Gammaℝ_ne_zero_of_isNontrivialZero`
- `riemannXi_eq_zero_of_isNontrivialZero`

## Verified Center Scaffold

The project has a local center-value and local logarithm scaffold around
`s = 1 / 2`:

- `riemannXi_half_re_pos`
- `riemannXi_half_mem_slitPlane`
- `analyticAt_log_riemannXi_half`
- `differentiableAt_log_riemannXi_half`
- `hasDerivAt_log_riemannXi_half`
- `deriv_log_riemannXi_half`
- `deriv_log_riemannXi_half_eq_zero`

These are local analytic facts for the repository's `riemannXi`. They do not
state any global zero-location theorem.

## Verified Local Li Coefficients

The first local Li candidate is identified with a real expression and shown to
have positive real part:

- `liCoefficientCandidate_zero_eq_eulerMascheroni`
- `liCoefficientCandidate_zero_eq_ofReal`
- `liCoefficientCandidate_zero_re_pos`

The second local Li candidate has real-valued packaging and positive real part:

- `liCoefficientCandidate_one_im_eq_zero`
- `liCoefficientCandidate_one_eq_ofReal_re`
- `liCoefficientCandidate_one_re_pos`

The final proof of `liCoefficientCandidate_one_re_pos` uses the following
checked reduction chain:

- `liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt`
- `liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt`
- `liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`
- `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`

The Mellin-log estimate is built from interval splitting, sign control on the
small interval, right-tail exponential comparison, and rational numeric bounds:

- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real`
- `mellin_log_integral_Ioo_zero_one_nonpos`
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one`
- `mellin_log_integral_Ioi_one_le_integral_exp_tail`
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound`
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`

The Li-side threshold lower bound uses coarse but Lean-checked numerical
estimates:

- `Real.eulerMascheroniConstant_gt_571_over_1000`
- `Real.log_four_mul_pi_lt_2533_over_1000`
- `liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty`
- `liCoefficientCandidate_zero_re_lt_one`
- `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`

## Limits

The current project proves only local scaffold facts and positivity for the
first two local Li candidates. It does not prove positivity for all Li
coefficients. It does not formalize the Li criterion. It does not prove the
Riemann Hypothesis.

The coefficient route is intentionally paused after `liCoefficientCandidate 1`.
Continuing one coefficient at a time would not by itself provide a structural
route to RH. The next work should select a Tier 2 structural route only after a
bounded inventory of available mathlib infrastructure.

## Recommended Next Step

Perform the Tier 2 inventory in two short notes:

- `T2.inventory.li.hadamard`: entire functions, zero multisets, Hadamard
  products, and log-derivative infrastructure for a Li-criterion route.
- `T2.inventory.nyman.beurling`: `L2`, closures, density, step functions, and
  fractional-part infrastructure for a Nyman-Beurling or Baez-Duarte route.

After both inventories, choose one route in `T2.pivot` and update the blueprint
before starting another proof chain.
