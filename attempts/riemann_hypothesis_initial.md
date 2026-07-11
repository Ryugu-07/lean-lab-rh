# Attempt: Riemann Hypothesis initial scaffolding

Date: 2026-07-08

## Objective

Start RH work as a Lean-checked research workflow:

- define the formal scope;
- map major human approaches;
- create first Lean wrappers around mathlib's RH material;
- verify that no proof file advances with placeholders.

## Formal target

Use mathlib's `RiemannHypothesis`.

Project-local predicates introduced in `LeanLab/Riemann/Basic.lean`:

- `IsZetaZero`
- `IsTrivialZeroPoint`
- `IsNontrivialZero`
- `OnCriticalLine`
- `InCriticalStrip`

## First Lean statements

Planned and then checked:

- `trivial_zero_is_zeta_zero`
- `zeta_zero_not_in_closed_right_half_plane`
- `zeta_zero_re_lt_one`
- `nontrivial_zero_re_lt_one`
- `riemannHypothesis_iff_nontrivial_zeros_on_line`
- `RiemannHypothesis.nontrivial_zero_on_line`
- `RiemannHypothesis.zero_on_line_or_trivial`
- `riemannZetaZeros_closed`
- `riemannZetaZeros_discrete`
- `compact_inter_riemannZetaZeros_finite`
- `zeta_eq_dirichlet_series_of_one_lt_re`

## Literature map

Recorded in `research/riemann_hypothesis_scope.md`.

Initial route preference:

1. Li criterion or Nyman-Beurling/Báez-Duarte, because they look more modular for formal decomposition.
2. Classical zero-free regions, because mathlib already contains a strong `Re(s) ≥ 1` nonvanishing theorem.
3. Spectral/Hilbert-Pólya/Connes/Berry-Keating remains high-level inspiration until its components are made precise enough for Lean.

## Verification log

Passed on 2026-07-08:

- `lake env lean LeanLab/Riemann/Basic.lean`
- `lake build`
- placeholder keyword scan over `LeanLab attempts research`
- full project placeholder keyword scan over `/Users/karasuakamatsu/lean-lab`

No theorem in this attempt is treated as completed unless those checks keep passing.

## Loop 2026-07-08-01: critical line to critical strip

Statement selected:

- `RiemannHypothesis.nontrivial_zero_inCriticalStrip`: assuming RH, every project-local nontrivial zeta zero is in the open critical strip.

Reason:

- This is a minimal wrapper around the current definitions.
- It creates a reusable interface for later Li criterion or Nyman-Beurling work.
- It does not assert any new unconditional progress toward RH.

Status before Lean check:

- Passed.

Lean result:

- Added `RiemannHypothesis.nontrivial_zero_inCriticalStrip` to `LeanLab/Riemann/Basic.lean`.
- First compile attempt failed because dot-style invocation of `RiemannHypothesis.nontrivial_zero_on_line` was not accepted for `hRH`.
- Replaced it with explicit theorem invocation:
  `RiemannHypothesis.nontrivial_zero_on_line hRH hs`.
- `lake env lean LeanLab/Riemann/Basic.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- Under RH, every project-local nontrivial zeta zero lies in the open critical strip.
- This is a conditional packaging theorem, not unconditional progress toward RH.

Next route:

- Try one unconditional statement about trivial zeros or the shape of the zero set.
- Then inspect whether mathlib already has enough `completedRiemannZeta` / `xi` support to begin Li-coefficient scaffolding.

## Loop 2026-07-08-02: trivial zeros lie to the left of the critical strip

Statement selected:

- `trivial_zero_re_lt_zero`: each mathlib-indexed trivial zero point `-2 * (n + 1)` has negative real part.

Reason:

- This is an unconditional fact about the already-formalized trivial-zero family.
- It separates trivial zeros from the open critical strip interface.
- It is small enough to test how well Lean simplifies complex coercions from integer/natural arithmetic.

Status before Lean check:

- Passed.

Lean result:

- Added `trivial_zero_re_lt_zero` to `LeanLab/Riemann/Basic.lean`.
- `norm_num` plus `positivity` discharged the real-part inequality.
- `lake env lean LeanLab/Riemann/Basic.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- Every point in the standard trivial-zero family `-2 * (n + 1)` has negative real part.
- This is an unconditional arithmetic/complex-coercion lemma.

Next route:

- Use this to prove that each trivial-zero point is outside the open critical strip.
- Then inspect the available completed-zeta/xi declarations for possible Li-coefficient scaffolding.

## Loop 2026-07-08-03: trivial zeros are outside the open critical strip

Statement selected:

- `trivial_zero_not_inCriticalStrip`: each standard trivial-zero point is not in the open critical strip.

Reason:

- This packages loop 02 into the exact predicate used by the RH scaffold.
- It is unconditional and should be reusable when separating trivial and nontrivial zeros.

Status before Lean check:

- Passed.

Lean result:

- Added `trivial_zero_not_inCriticalStrip` to `LeanLab/Riemann/Basic.lean`.
- The proof uses `trivial_zero_re_lt_zero` and the first component of `InCriticalStrip`.
- `lake env lean LeanLab/Riemann/Basic.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- Standard trivial-zero points are outside the open critical strip.
- The trivial-zero separation interface is now sufficient for the current scaffold.

Next route:

- Stop adding trivial-zero wrappers unless a later proof needs a sharper one.
- Inspect mathlib declarations around `completedRiemannZeta`, completed zeta functional equation, derivatives, and possible `xi` naming to decide whether Li-coefficient scaffolding is feasible.

## Loop 2026-07-08-04: local xi scaffold and functional equation

Statement selected:

- Define a project-local `riemannXi` using `completedRiemannZeta₀`.
- Prove `riemannXi_one_sub`: `riemannXi (1 - s) = riemannXi s`.

Reason:

- mathlib has `completedRiemannZeta₀`, `completedRiemannZeta₀_one_sub`, and differentiability support, but no direct `riemannXi` declaration was found.
- Defining `riemannXi` from `completedRiemannZeta₀` avoids relying on the arbitrary values of the meromorphic `completedRiemannZeta` at its poles.
- Li-coefficient work needs a symmetric xi-like function before any coefficient positivity statements can be stated.

Status before Lean check:

- Passed.

Lean result:

- Added `LeanLab/Riemann/LiScaffold.lean`.
- Added local definition `riemannXi`.
- Proved `riemannXi_one_sub`.
- First compile attempt failed because the xi definition depends on noncomputable complex division.
- Added `noncomputable section`; the proof then compiled.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- mathlib does not appear to expose a ready-made `riemannXi` declaration in this project version.
- A local xi-like function can be safely defined from `completedRiemannZeta₀`.
- The local xi function satisfies the expected symmetry `s ↦ 1 - s`.

Next route:

- Prove differentiability of `riemannXi`.
- Then define a first Li-coefficient expression using `iteratedDeriv` only after differentiability support is checked.

## Loop 2026-07-08-05: differentiability of local xi

Statement selected:

- `differentiable_riemannXi`: the project-local `riemannXi` is differentiable over `ℂ`.

Reason:

- Li coefficients are built from derivatives of xi-like expressions.
- Before defining those coefficients, we need a Lean-checked differentiability interface for the local xi scaffold.

Status before Lean check:

- Passed.

Lean result:

- Added `differentiable_riemannXi` to `LeanLab/Riemann/LiScaffold.lean`.
- First proof attempt with plain `fun_prop` failed because it did not know `completedRiemannZeta₀` is differentiable.
- Switched to explicit composition:
  - prove the polynomial factor is differentiable by `fun_prop`;
  - use mathlib's `differentiable_completedZeta₀`;
  - add an explicitly typed constant-differentiability fact.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The local xi scaffold now has both symmetry and global differentiability.
- This is enough to start defining derivative-based Li coefficient expressions, but not enough to assert Li's criterion.

Next route:

- Define a minimal Li-coefficient expression using `iteratedDeriv`.
- Keep it as a definition first; only prove algebraic properties that Lean can verify without importing unproved RH-equivalence claims.

## Loop 2026-07-08-06: first Li coefficient candidate expression

Statement selected:

- Define `liCoefficientCandidate n` as the derivative expression corresponding to the candidate
  for the `(n + 1)`-st Li coefficient:
  `iteratedDeriv (n + 1) (fun s => s ^ n * log (riemannXi s)) 1 / n!`.
- Prove `liCoefficientCandidate_zero`: the `n = 0` case is the derivative of
  `log (riemannXi s)` at `1`.

Reason:

- This gives a concrete derivative-based object for the Li route.
- The name says `Candidate` because no RH-equivalence or positivity criterion has been formalized.
- The first property is purely definitional/algebraic and does not need analytic assumptions about the complex logarithm.

Status before Lean check:

- Passed.

Lean result:

- Added `liCoefficientCandidate` to `LeanLab/Riemann/LiScaffold.lean`.
- Added `liCoefficientCandidate_zero`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The Li route now has a concrete derivative-based candidate sequence.
- The `n = 0` case reduces to the first derivative of `log ∘ riemannXi` at `1`.
- This remains only a candidate expression; no positivity theorem, log analyticity theorem, or RH-equivalence theorem has been proved.

Next route:

- Investigate local nonvanishing of `riemannXi` at `1`, because analytic use of `log ∘ riemannXi` needs a nonzero base value or a local nonvanishing statement.
- A safe next theorem may be an exact value for `riemannXi 1` if it can be derived from the current definition and mathlib's completed-zeta normalization.

## Loop 2026-07-08-07: xi value and nonvanishing at one

Statement selected:

- `riemannXi_one`: `riemannXi 1 = 1 / 2`.
- `riemannXi_one_ne_zero`: `riemannXi 1 ≠ 0`.

Reason:

- The next analytic step for `log (riemannXi s)` needs a nonzero base value at `s = 1`.
- The exact value follows directly from the local definition, because the factor `s * (s - 1)` vanishes at `s = 1`.
- This avoids needing any extra value theorem for `completedRiemannZeta₀ 1`.

Status before Lean check:

- Passed.

Lean result:

- Added `riemannXi_one` and `riemannXi_one_ne_zero` to `LeanLab/Riemann/LiScaffold.lean`.
- Both proofs are direct simplifications from the local definition of `riemannXi`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The local xi scaffold has the exact value `riemannXi 1 = 1 / 2`.
- In particular, `riemannXi 1` is nonzero.
- This is a pointwise fact only; it does not yet prove local nonvanishing near `1` or analytic behavior of `log ∘ riemannXi`.

Next route:

- Investigate mathlib support for differentiability/analyticity of `Complex.log` composed with a function at a point where the function value is nonzero or lies in `slitPlane`.
- Decide whether the Li route should use principal `Complex.log` directly or introduce a local analytic logarithm abstraction.

## Loop 2026-07-08-08: local analyticity of log xi at one

Statement selected:

- `analyticAt_log_riemannXi_one`: `fun s => log (riemannXi s)` is analytic at `1`.

Supporting facts:

- `analyticAt_riemannXi`: local `riemannXi` is analytic at every point.
- `riemannXi_one_mem_slitPlane`: `riemannXi 1 ∈ slitPlane`.

Reason:

- mathlib's principal `Complex.log` is analytic on `slitPlane`.
- Loop 07 proved `riemannXi 1 = 1 / 2`, which should place the value in `slitPlane`.
- This is the first safe analytic fact about the Li-candidate logarithm, still far short of Li's criterion.

Status before Lean check:

- Passed.

Lean result:

- Added `riemannXi_one_mem_slitPlane`, `analyticAt_riemannXi`, and
  `analyticAt_log_riemannXi_one` to `LeanLab/Riemann/LiScaffold.lean`.
- First proof attempt for `riemannXi 1 ∈ slitPlane` using direct `norm_num` failed.
- A second attempt using `ofReal_mem_slitPlane` exposed a coercion mismatch between real and complex division.
- Final proof unfolds `mem_slitPlane_iff` and proves the positive-real-part branch directly.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The project now has a Lean-checked local analytic fact:
  `AnalyticAt ℂ (fun s => log (riemannXi s)) 1`.
- This justifies the principal-log expression at the base point `1`.
- It still does not prove global log analyticity, local nonvanishing on an explicit neighborhood, Li positivity, or RH equivalence.

Next route:

- Use `analyticAt_log_riemannXi_one` to prove the first derivative expression is legitimate at `1`.
- A safe next target is a `DifferentiableAt` wrapper or a theorem identifying `liCoefficientCandidate 0`
  with a derivative whose differentiability is known.

## Loop 2026-07-08-09: derivative legitimacy for the first Li candidate

Statement selected:

- `differentiableAt_log_riemannXi_one`: `log ∘ riemannXi` is differentiable at `1`.
- `hasDerivAt_log_riemannXi_one`: its derivative is `deriv riemannXi 1 / riemannXi 1`.
- `liCoefficientCandidate_zero_eq_logDeriv`: the first candidate coefficient equals that logarithmic derivative.

Reason:

- Loop 08 proved analyticity of `log ∘ riemannXi` at `1`.
- mathlib has `HasDerivAt.clog`, which supplies the standard logarithmic derivative when the value is in `slitPlane`.
- This advances the Li-candidate scaffold without asserting positivity or RH equivalence.

Status before Lean check:

- Passed.

Lean result:

- Added `differentiableAt_log_riemannXi_one`.
- Added `hasDerivAt_log_riemannXi_one`.
- Added `deriv_log_riemannXi_one`.
- Added `liCoefficientCandidate_zero_eq_logDeriv`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The first Li-candidate expression now has a Lean-checked logarithmic-derivative interpretation:
  `liCoefficientCandidate 0 = deriv riemannXi 1 / riemannXi 1`.
- This is a local derivative fact at `1`, not a positivity or RH-equivalence statement.

Next route:

- Investigate whether `deriv riemannXi 1` can be simplified using the definition of `riemannXi`.
- A likely safe target is a product-rule lemma reducing `deriv riemannXi 1` to values/derivatives of `completedRiemannZeta₀` at `1`, without claiming any special zeta constant.

## Loop 2026-07-08-10: simplifying the derivative of local xi at one

Statement selected:

- `deriv_riemannXi_one`: `deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2`.

Reason:

- Loop 09 reduced the first Li-candidate expression to `deriv riemannXi 1 / riemannXi 1`.
- The local definition of `riemannXi` has a factor `s * (s - 1)`, so the term involving
  `deriv completedRiemannZeta₀ 1` should vanish at `s = 1`.
- This is a product-rule computation, not a special-value theorem for zeta.

Status before Lean check:

- Passed.

Lean result:

- Added `deriv_riemannXi_factor_one`.
- Added `deriv_riemannXi_one`.
- Added `liCoefficientCandidate_zero_eq_completedZeta₀`.
- First proof attempt used direct `simp` on the derivative of the whole `riemannXi` expression; this failed because Lean did not expose the product-rule structure.
- The successful proof split off the elementary factor `s * (s - 1) / 2`, proved its derivative at `1`, then used product-rule simplification.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- `deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2`.
- Therefore `liCoefficientCandidate 0 = completedRiemannZeta₀ 1`.
- This is still only a local derivative/product-rule computation in the Li scaffold; it is not a special-value theorem, positivity theorem, or RH-equivalence theorem.

Next route:

- Investigate whether `completedRiemannZeta₀ 1` has an existing mathlib simplification or symmetry consequence.
- If not, leave it as the natural endpoint for the first candidate coefficient and switch to a second minimal Li-scaffold target.

## Loop 2026-07-08-11: explicit value for the first Li candidate

Statement selected:

- `liCoefficientCandidate_zero_eq_eulerMascheroni`: the first Li candidate equals
  `((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1`.

Reason:

- Loop 10 reduced the first candidate coefficient to `completedRiemannZeta₀ 1`.
- Local mathlib search found `completedRiemannZeta₀_one` in
  `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.
- This is a direct special-value substitution; it does not claim sign, Li criterion, or RH
  equivalence.

Status before Lean check:

- Passed.

Lean result:

- Imported `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.
- Added `liCoefficientCandidate_zero_eq_eulerMascheroni`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The first local Li candidate is now tied to the existing mathlib special-value theorem:
  `liCoefficientCandidate 0 =
    ((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1`.
- This is still a value identity, not a positivity theorem.

Next route:

- Convert the expression to a real-coerced form using `Complex.ofReal_log` for positive
  real input.
- After that, investigate whether available bounds for `Real.eulerMascheroniConstant`,
  `Real.log`, and `Real.pi` are sufficient for the first positivity check.

## Loop 2026-07-08-12: real-valued form of the first Li candidate

Statement selected:

- `liCoefficientCandidate_zero_eq_ofReal`: the first Li candidate equals the complex embedding of
  `((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ)`.

Reason:

- Loop 11 gave a complex expression involving `Complex.log (4 * (Real.pi : ℂ))`.
- For later positivity checks, the expression should be rewritten as an embedded real number.
- The needed fact is `Complex.ofReal_log` on the positive real input `4 * Real.pi`.

Status before Lean check:

- Passed.

Lean result:

- Added `liCoefficientCandidate_zero_eq_ofReal`.
- The first proof attempt tried to rewrite `Complex.ofReal_log` directly, but the argument shape
  was `4 * (Real.pi : ℂ)` rather than `((4 * Real.pi : ℝ) : ℂ)`.
- The successful proof first inserted `harg : 4 * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ)`,
  then rewrote by `Complex.ofReal_log` and finished by normalization.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The first local Li candidate is now Lean-checked to be a real number embedded in `ℂ`.
- This prepares the first positivity question, but does not itself prove positivity.

Next route:

- Search existing mathlib bounds around `Real.eulerMascheroniConstant`, `Real.log`, `Real.pi`,
  and `Real.exp` to see whether
  `0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1`
  is feasible without adding substantial analytic estimates.

## Loop 2026-07-08-13: positivity of the first Li candidate

Statement selected:

- `liCoefficientCandidate_zero_real_pos`:
  `0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1`.
- `liCoefficientCandidate_zero_re_pos`: `0 < (liCoefficientCandidate 0).re`.

Reason:

- Loop 12 proved the first local Li candidate is an embedded real number.
- Li's criterion would require nonnegativity of a whole sequence; proving the first term positive
  is a small sanity check for the scaffold.
- Directly using the coarse bound `1 / 2 < Real.eulerMascheroniConstant` is not enough, so the
  proof uses the stronger general lower approximation
  `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 11`.

Status before Lean check:

- Passed.

Lean result:

- Added `liCoefficientCandidate_zero_real_pos`.
- Added `liCoefficientCandidate_zero_re_pos`.
- The proof bounds `Real.eulerMascheroniConstant` below by
  `83711 / 27720 - Real.log 12`.
- It bounds `Real.log (4 * Real.pi)` by splitting
  `log (4π) = log 12 + log (π / 3)`, using `Real.log_two_lt_d9`,
  `Real.log_three_lt_d9`, `Real.pi_lt_d4`, and `Real.log_le_sub_one_of_pos`.
- The remaining comparison is a rational inequality handled by `norm_num`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The first local Li candidate has Lean-checked positive real part.
- This is the first positive Li-candidate sanity check in the project.
- It does not establish positivity for any `n > 0`, Li's criterion, or RH equivalence.

Next route:

- Decide whether to continue with the `n = 1` Li-candidate derivative expansion or to first
  factor out reusable numerical/log-bound lemmas from the `n = 0` positivity proof.

## Loop 2026-07-08-14: first derivative layer for the second Li candidate

Statement selected:

- `liCoefficientCandidate_one_eq_secondDeriv`:
  `liCoefficientCandidate 1 = deriv (deriv (fun s => s * log (riemannXi s))) 1`.
- `deriv_id_mul_log_riemannXi_one`:
  the first derivative of `fun s => s * log (riemannXi s)` at `1` is
  `log (riemannXi 1) + deriv riemannXi 1 / riemannXi 1`.
- `deriv_id_mul_log_riemannXi_one_eq_completedZeta₀`:
  the same derivative is `log (1 / 2 : ℂ) + completedRiemannZeta₀ 1`.

Reason:

- Loop 13 completed only the `n = 0` positivity sanity check.
- For `n = 1`, the Li candidate is a second derivative of `s * log (riemannXi s)`.
- Before expanding a second derivative, the first derivative layer should be Lean-checked.

Status before Lean check:

- Passed.

Lean result:

- Added `liCoefficientCandidate_one_eq_secondDeriv`.
- Added `deriv_id_mul_log_riemannXi_one`.
- Added `deriv_id_mul_log_riemannXi_one_eq_completedZeta₀`.
- The first attempt after product-rule rewriting left the subgoal
  `deriv (fun s => log (riemannXi s)) 1 = deriv riemannXi 1 / riemannXi 1`;
  explicitly rewriting by `deriv_log_riemannXi_one` solved it.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The project now has a Lean-checked first derivative layer for the `n = 1` Li candidate.
- This does not compute the actual second derivative and does not prove positivity of
  `liCoefficientCandidate 1`.

Next route:

- Try to express `liCoefficientCandidate 1` as the derivative at `1` of the already-expanded
  first-derivative expression, or inspect whether mathlib has enough local analytic machinery to
  justify differentiating the logarithmic derivative cleanly.

## Loop 2026-07-08-15: analytic justification for the second Li derivative

Statement selected:

- `analyticAt_id_mul_log_riemannXi_one`:
  `fun s => s * log (riemannXi s)` is analytic at `1`.
- `analyticAt_deriv_id_mul_log_riemannXi_one`:
  its derivative function is analytic at `1`.
- `differentiableAt_deriv_id_mul_log_riemannXi_one`:
  its derivative function is differentiable at `1`.
- `hasDerivAt_deriv_id_mul_log_riemannXi_one`:
  the derivative of that derivative at `1` is `liCoefficientCandidate 1`.

Reason:

- Loop 14 identified `liCoefficientCandidate 1` with a second derivative but did not justify the
  local analytic structure of the first derivative function as a reusable interface.
- mathlib has `AnalyticAt.deriv`, which is the cleanest way to certify that this second derivative
  is a legitimate local analytic derivative.

Status before Lean check:

- Passed.

Lean result:

- Added `analyticAt_id_mul_log_riemannXi_one`.
- Added `analyticAt_deriv_id_mul_log_riemannXi_one`.
- Added `differentiableAt_deriv_id_mul_log_riemannXi_one`.
- Added `hasDerivAt_deriv_id_mul_log_riemannXi_one`.
- A direct `fun_prop` attempt did not find the project-local `analyticAt_riemannXi` and
  `riemannXi_one_mem_slitPlane` facts. The successful proof explicitly combined the identity
  function's analyticity with `analyticAt_log_riemannXi_one`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate now has a Lean-checked analytic differentiability interface.
- This still does not compute `liCoefficientCandidate 1` explicitly and does not prove its
  positivity.

Next route:

- Try a local product-rule expansion of the second derivative using this analytic interface, or
  inspect whether rewriting the derivative of `log ∘ riemannXi` through `logDeriv riemannXi`
  is easier.

## Loop 2026-07-08-16: local product-rule expansion for the second Li candidate

Statement selected:

- `eventually_deriv_id_mul_log_riemannXi_eq`:
  in a neighborhood of `1`, the derivative of `fun t => t * log (riemannXi t)` is
  `fun s => log (riemannXi s) + s * deriv (fun t => log (riemannXi t)) s`.
- `liCoefficientCandidate_one_eq_deriv_productRule`:
  `liCoefficientCandidate 1` is the derivative at `1` of that product-rule expression.

Reason:

- Loop 15 gave analyticity of `fun s => s * log (riemannXi s)` and of its derivative at `1`.
- To compute or estimate the `n = 1` local Li candidate, the second derivative should first be
  rewritten into an expression whose terms are recognizable as a log derivative layer.
- mathlib provides `AnalyticAt.eventually_analyticAt` and `Filter.EventuallyEq.deriv_eq`, which
  let the project justify the product-rule rewrite locally instead of asserting a global identity.

Status before Lean check:

- Passed.

Lean result:

- Added `open scoped Topology` to enable neighborhood notation.
- Added `eventually_deriv_id_mul_log_riemannXi_eq`.
- Added `liCoefficientCandidate_one_eq_deriv_productRule`.
- The first Lean attempt failed only because `𝓝` was not in scope; opening the topology scope
  fixed the notation issue.
- The local rewrite uses `analyticAt_log_riemannXi_one.eventually_analyticAt`, then applies
  `deriv_fun_mul` pointwise in that neighborhood.
- The Li-candidate rewrite then follows from `Filter.EventuallyEq.deriv_eq`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The `n = 1` local Li candidate now has a Lean-checked product-rule expansion interface.
- This still does not compute an explicit value for `liCoefficientCandidate 1`, does not prove
  its positivity, and does not establish Li's criterion or RH equivalence.

Next route:

- Try to rewrite `deriv (fun s => log (riemannXi s)) s` locally as
  `deriv riemannXi s / riemannXi s`, or introduce a project-local log-derivative expression for
  `riemannXi` near `1`.

## Loop 2026-07-08-17: local logarithmic derivative rewrite

Statement selected:

- `eventually_riemannXi_mem_slitPlane_one`:
  in a neighborhood of `1`, `riemannXi s ∈ slitPlane`.
- `eventually_deriv_log_riemannXi_eq_logDeriv`:
  in a neighborhood of `1`,
  `deriv (fun t => log (riemannXi t)) s = logDeriv riemannXi s`.
- `eventually_deriv_log_riemannXi_eq`:
  the same local identity in fraction form,
  `deriv (fun t => log (riemannXi t)) s = deriv riemannXi s / riemannXi s`.
- `liCoefficientCandidate_one_eq_deriv_logDeriv` and
  `liCoefficientCandidate_one_eq_deriv_logDeriv_fraction`:
  the `n = 1` local Li candidate is the derivative at `1` of
  `log (riemannXi s) + s * logDeriv riemannXi s`, equivalently of
  `log (riemannXi s) + s * (deriv riemannXi s / riemannXi s)`.

Reason:

- Loop 16 reduced the second local Li candidate to the derivative of a product-rule expression.
- The remaining opaque term was the derivative of `log ∘ riemannXi`.
- mathlib already has `Complex.deriv_log_comp_eq_logDeriv`, but it requires the function value to
  lie in `slitPlane`; continuity of `riemannXi` and `riemannXi_one_mem_slitPlane` provide this
  condition locally near `1`.

Status before Lean check:

- Passed.

Lean result:

- Added `eventually_riemannXi_mem_slitPlane_one`.
- Added `eventually_deriv_log_riemannXi_eq_logDeriv`.
- Added `eventually_deriv_log_riemannXi_eq`.
- Added `eventually_productRule_eq_logDeriv` and
  `eventually_productRule_eq_logDeriv_fraction`.
- Added `liCoefficientCandidate_one_eq_deriv_logDeriv` and
  `liCoefficientCandidate_one_eq_deriv_logDeriv_fraction`.
- The only non-mathematical snag was that a direct simplification from `logDeriv riemannXi` to the
  pointwise fraction did not unfold function division; an explicit pointwise proof using
  `logDeriv_apply` solved it.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate now has a Lean-checked local representation as the derivative at
  `1` of `log ξ + s * ξ'/ξ`.
- This is closer to the classical Li-coefficient calculus, but it still does not compute
  `liCoefficientCandidate 1` explicitly, does not prove positivity, and does not establish Li's
  criterion or RH equivalence.

Next route:

- Try to expand `deriv riemannXi s` from the local definition of `riemannXi`, or investigate
  whether differentiating `s * (deriv riemannXi s / riemannXi s)` at `1` is tractable with the
  currently available analyticity facts.

## Loop 2026-07-08-18: expanding the derivative of the local xi function

Statement selected:

- `deriv_riemannXi_factor`:
  `deriv (fun z => z * (z - 1) / 2) s = s - 1 / 2`.
- `deriv_riemannXi`:
  `deriv riemannXi s =
    (s - 1 / 2) * completedRiemannZeta₀ s +
      (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s`.
- `logDeriv_riemannXi_eq`:
  `logDeriv riemannXi s` is the above numerator divided by `riemannXi s`.
- `liCoefficientCandidate_one_eq_deriv_expandedLogDeriv`:
  `liCoefficientCandidate 1` is the derivative at `1` of
  `log (riemannXi s) + s * (((s - 1 / 2) * completedRiemannZeta₀ s +
    (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s)`.

Reason:

- Loop 17 rewrote the second local Li candidate as the derivative of `log ξ + s * ξ'/ξ`.
- The next smallest useful step is exposing `ξ'` from the project-local definition of `riemannXi`.
- This prepares the later quotient/product derivative work without yet trying to compute the full
  second Li candidate.

Status before Lean check:

- Passed.

Lean result:

- Added `deriv_riemannXi_factor`.
- Added `deriv_riemannXi`.
- Added `logDeriv_riemannXi_eq`.
- Added `eventually_logDeriv_riemannXi_eq`.
- Added `liCoefficientCandidate_one_eq_deriv_expandedLogDeriv`.
- The main proof uses `deriv_fun_mul`, `deriv_add_const`,
  `differentiable_completedZeta₀.differentiableAt`, and the polynomial derivative fact.
- The only minor Lean snag was pointwise beta-reduction in the eventual equality; an explicit
  `change` exposed the term where `logDeriv_riemannXi_eq` applies.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate now has a Lean-checked expression involving
  `completedRiemannZeta₀`, its derivative, and the local `riemannXi` denominator.
- This still does not compute `liCoefficientCandidate 1`, prove positivity, or establish Li's
  criterion/RH equivalence.

Next route:

- Investigate whether mathlib has enough differentiability facts to differentiate
  `s * (((s - 1 / 2) * completedRiemannZeta₀ s +
    (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s)` at `1`, or first prove
  smaller local differentiability facts for this quotient expression.

## Loop 2026-07-08-19: differentiability of the logarithmic derivative layer

Statement selected:

- `analyticAt_deriv_riemannXi_one`:
  `deriv riemannXi` is analytic at `1`.
- `differentiableAt_deriv_riemannXi_one`:
  `deriv riemannXi` is differentiable at `1`.
- `differentiableAt_logDeriv_riemannXi_one`:
  `logDeriv riemannXi` is differentiable at `1`.
- `differentiableAt_id_mul_logDeriv_riemannXi_one`:
  `fun s => s * logDeriv riemannXi s` is differentiable at `1`.
- `deriv_id_mul_logDeriv_riemannXi_one`:
  the derivative of `s * logDeriv riemannXi s` at `1` is
  `logDeriv riemannXi 1 + deriv (logDeriv riemannXi) 1`.
- `liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv`:
  `liCoefficientCandidate 1 =
    logDeriv riemannXi 1 + (logDeriv riemannXi 1 + deriv (logDeriv riemannXi) 1)`.

Reason:

- Loop 18 exposed `ξ'` and moved the second local Li candidate to `log ξ + s * ξ'/ξ`.
- Before computing a quotient derivative explicitly, the project needs a Lean-checked
  differentiability interface for the logarithmic derivative layer.
- The final displayed identity is the local `n = 1` Li-candidate calculus formula in terms of
  `L = ξ'/ξ`: `λ₁ = L(1) + (L(1) + L'(1))`.

Status before Lean check:

- Passed.

Lean result:

- Added `analyticAt_deriv_riemannXi_one`.
- Added `differentiableAt_deriv_riemannXi_one`.
- Added `differentiableAt_logDeriv_riemannXi_one`.
- Added `differentiableAt_id_mul_logDeriv_riemannXi_one`.
- Added `deriv_id_mul_logDeriv_riemannXi_one`.
- Added `liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv`.
- The quotient differentiability proof uses `AnalyticAt.deriv`, `DifferentiableAt.div`, and
  `riemannXi_one_ne_zero`.
- The only Lean adjustment was replacing `deriv_add` with `deriv_fun_add`, because the target was
  syntactically a lambda of a sum.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate now has a Lean-checked formula in terms of the logarithmic
  derivative layer and its derivative at `1`.
- This still does not compute `deriv (logDeriv riemannXi) 1`, prove positivity, or establish
  Li's criterion/RH equivalence.

Next route:

- Try to compute or rewrite `logDeriv riemannXi 1` using the earlier `liCoefficientCandidate 0`
  facts, then investigate whether `deriv (logDeriv riemannXi) 1` can be expressed via a quotient
  rule.

## Loop 2026-07-08-20: identifying `L(1)` with the first Li candidate

Statement selected:

- `logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero`:
  `logDeriv riemannXi 1 = liCoefficientCandidate 0`.
- `liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv`:
  `liCoefficientCandidate 1 =
    liCoefficientCandidate 0 +
      (liCoefficientCandidate 0 + deriv (logDeriv riemannXi) 1)`.

Reason:

- Loop 19 expressed the second local Li candidate as `L(1) + (L(1) + L'(1))`,
  where `L = logDeriv riemannXi`.
- The project had already identified `liCoefficientCandidate 0` with
  `deriv riemannXi 1 / riemannXi 1`.
- This loop connects those two local layers, leaving `L'(1)` as the genuinely new term for the
  next stage.

Status before Lean check:

- Passed.

Lean result:

- Added `logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero`.
- Added `liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv`.
- The proof is a direct rewrite using `liCoefficientCandidate_zero_eq_logDeriv` and
  `logDeriv_apply`, followed by rewriting both occurrences of `logDeriv riemannXi 1` in the
  Loop 19 formula.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate is now reduced to the first local Li candidate plus the derivative
  of the logarithmic derivative layer at `1`.
- This still does not compute `deriv (logDeriv riemannXi) 1`, prove positivity, or establish
  Li's criterion/RH equivalence.

Next route:

- Try to express `deriv (logDeriv riemannXi) 1` by a quotient rule in terms of
  `deriv (deriv riemannXi) 1`, `deriv riemannXi 1`, and `riemannXi 1`.

## Loop 2026-07-08-21: quotient-rule expansion of `L'(1)`

Statement selected:

- `deriv_logDeriv_riemannXi_one`:
  `deriv (logDeriv riemannXi) 1 =
    (deriv (deriv riemannXi) 1 * riemannXi 1 -
      deriv riemannXi 1 * deriv riemannXi 1) / riemannXi 1 ^ 2`.
- `liCoefficientCandidate_one_eq_zero_add_logDeriv_quotient`:
  the Loop 20 formula with the quotient-rule expression substituted.
- `deriv_logDeriv_riemannXi_one_eq_secondDeriv`:
  after substituting `riemannXi 1 = 1 / 2` and
  `deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2`,
  `deriv (logDeriv riemannXi) 1 =
    2 * deriv (deriv riemannXi) 1 - completedRiemannZeta₀ 1 ^ 2`.
- `liCoefficientCandidate_one_eq_zero_add_secondDeriv`:
  the second local Li candidate reduced to `liCoefficientCandidate 0`, the second derivative of
  the local `riemannXi`, and `completedRiemannZeta₀ 1`.

Reason:

- Loop 20 reduced the second local Li candidate to the first local Li candidate plus `L'(1)`.
- The next smallest calculus step is to use the quotient rule for
  `L = logDeriv riemannXi = ξ'/ξ`.
- This isolates the new unresolved analytic quantity as `ξ''(1)`.

Status before Lean check:

- Passed.

Lean result:

- Added `deriv_logDeriv_riemannXi_one`.
- Added `liCoefficientCandidate_one_eq_zero_add_logDeriv_quotient`.
- Added `deriv_logDeriv_riemannXi_one_eq_secondDeriv`.
- Added `liCoefficientCandidate_one_eq_zero_add_secondDeriv`.
- The quotient-rule proof unfolds `logDeriv` and applies `deriv_div` using
  `differentiableAt_deriv_riemannXi_one`, `differentiable_riemannXi 1`, and
  `riemannXi_one_ne_zero`.
- The simplification to `2 * ξ''(1) - completedRiemannZeta₀ 1 ^ 2` uses
  `riemannXi_one`, `deriv_riemannXi_one`, and `ring`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project placeholder keyword scan passed with no matches.

Conclusion:

- The second local Li candidate is now reduced to the first local Li candidate plus a term
  involving `deriv (deriv riemannXi) 1`.
- This still does not compute `ξ''(1)`, prove positivity, or establish Li's criterion/RH
  equivalence.

Next route:

- Try to expand `deriv (deriv riemannXi) 1` from the already proved first-derivative formula, or
  inspect whether mathlib has a convenient way to express the second derivative of
  `completedRiemannZeta₀` at `1`.

## Loop 2026-07-09-22: expanding `ξ''(1)` from the first-derivative formula

Statement selected:

- `analyticAt_deriv_completedRiemannZeta₀_one`:
  `deriv completedRiemannZeta₀` is analytic at `1`.
- `differentiableAt_deriv_completedRiemannZeta₀_one`:
  `deriv completedRiemannZeta₀` is differentiable at `1`.
- `deriv_deriv_riemannXi_one`:
  `deriv (deriv riemannXi) 1 =
    completedRiemannZeta₀ 1 + deriv completedRiemannZeta₀ 1`.
- `liCoefficientCandidate_one_eq_completedZeta₀_deriv`:
  `liCoefficientCandidate 1 =
    4 * completedRiemannZeta₀ 1 +
      2 * deriv completedRiemannZeta₀ 1 - completedRiemannZeta₀ 1 ^ 2`.

Reason:

- Loop 21 isolated the only new local analytic term in the second Li candidate as `ξ''(1)`.
- The already proved formula for `ξ'` is differentiable at `1`, because
  `completedRiemannZeta₀` is analytic and therefore its derivative is analytic locally.
- Expanding `ξ''(1)` removes one layer of local xi notation and reduces the `n = 1` candidate to
  `completedRiemannZeta₀ 1` plus the first derivative of `completedRiemannZeta₀` at `1`.

Status before Lean check:

- Passed.

Lean result:

- Added `analyticAt_deriv_completedRiemannZeta₀_one`.
- Added `differentiableAt_deriv_completedRiemannZeta₀_one`.
- Added `deriv_deriv_riemannXi_one`.
- Added `liCoefficientCandidate_one_eq_completedZeta₀_deriv`.
- First direct rewrite left Lean with an unreduced `deriv (fun s => s) 1` term inside the product
  rule. The final proof splits the calculation into two local product-derivative facts:
  one for `(s - 1 / 2) * completedRiemannZeta₀ s`, and one for
  `(s * (s - 1) / 2) * deriv completedRiemannZeta₀ s`.
- The coefficient check exposed that the final `liCoefficientCandidate 1` formula has
  `4 * completedRiemannZeta₀ 1`, not `2 * completedRiemannZeta₀ 1`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The second local Li candidate is now reduced to the local completed-zeta value and its first
  derivative at `1`:
  `λ₁ = 4 * completedRiemannZeta₀ 1 +
    2 * deriv completedRiemannZeta₀ 1 - completedRiemannZeta₀ 1 ^ 2`.
- This still does not evaluate `deriv completedRiemannZeta₀ 1`, prove positivity of
  `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Inspect mathlib for special-value or Laurent-expansion support around
  `deriv completedRiemannZeta₀ 1`.
- If no such theorem exists, try to expose `completedRiemannZeta₀` near `1` from its definition
  and prove a smaller derivative identity involving the finite part of zeta/Gamma factors.

## Loop 2026-07-09-23: moving the remaining completed-zeta derivative to zero

Statement selected:

- `deriv_completedRiemannZeta₀_one_eq_neg_zero`:
  `deriv completedRiemannZeta₀ 1 = -deriv completedRiemannZeta₀ 0`.
- `liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero`:
  `liCoefficientCandidate 1 =
    4 * completedRiemannZeta₀ 1 -
      2 * deriv completedRiemannZeta₀ 0 - completedRiemannZeta₀ 1 ^ 2`.
- `liCoefficientCandidate_one_eq_eulerMascheroni_neg_deriv_zero`:
  the same formula with the known special value for `completedRiemannZeta₀ 1` substituted.

Reason:

- Loop 22 reduced the second local Li candidate to `completedRiemannZeta₀ 1` and
  `deriv completedRiemannZeta₀ 1`.
- Local search did not find a direct special-value theorem for
  `deriv completedRiemannZeta₀ 1`.
- mathlib does contain `completedRiemannZeta₀_one_sub` and several `0`-point calculations around
  `riemannZeta`, `Gamma`, and `completedRiemannZeta₀`; moving the derivative from `1` to `0`
  makes the next investigation better aligned with available material.

Status before Lean check:

- Passed.

Lean result:

- Added `deriv_completedRiemannZeta₀_one_eq_neg_zero`.
- Added `liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero`.
- Added `liCoefficientCandidate_one_eq_eulerMascheroni_neg_deriv_zero`.
- The derivative reflection proof differentiates the pointwise identity
  `completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s` at `s = 0`, then uses
  `deriv_comp_const_sub`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining unknown in the second local Li candidate can now be represented as
  `deriv completedRiemannZeta₀ 0` rather than a derivative at `1`.
- This still does not evaluate that derivative, prove positivity of `liCoefficientCandidate 1`,
  or establish Li's criterion/RH equivalence.

Next route:

- Inspect the definition of `completedRiemannZeta₀` and the proof of `deriv_riemannZeta_zero` to
  see whether a small identity can expose `deriv completedRiemannZeta₀ 0`.
- If that derivative remains inaccessible, switch to a structural theorem for real-valuedness or
  conjugation symmetry of the local Li-candidate expressions before attempting positivity.

## Loop 2026-07-09-24: numerator side of the `ζ'(0)` completed-zeta formula

Statement selected:

- `deriv_riemannZeta_zero_numerator`:
  `deriv (fun s : ℂ ↦ (s * completedRiemannZeta₀ s - 1) - s / (1 - s)) 0 =
    completedRiemannZeta₀ 0 - 1`.

Reason:

- Loop 23 moved the remaining derivative in the second local Li candidate to
  `deriv completedRiemannZeta₀ 0`.
- mathlib's proof of `deriv_riemannZeta_zero` starts from
  `riemannZeta_eq_mul_completedRiemannZeta₀`, whose numerator is
  `(s * completedRiemannZeta₀ s - 1) - s / (1 - s)`.
- Differentiating this numerator at `0` is the smallest check of whether the known
  `ζ'(0)` calculation exposes `deriv completedRiemannZeta₀ 0`.

Status before Lean check:

- Passed.

Lean result:

- Added `deriv_riemannZeta_zero_numerator`.
- The proof splits the derivative into:
  - `deriv (fun s => s * completedRiemannZeta₀ s - 1) 0 = completedRiemannZeta₀ 0`;
  - `deriv (fun s => s / (1 - s)) 0 = 1`.
- The product calculation shows why `deriv completedRiemannZeta₀ 0` disappears: it is multiplied
  by `s` and then evaluated at `s = 0`.
- I also tried to package the corresponding denominator derivative
  `deriv (fun s => 2 * π ^ (-s / 2) * Gamma (s / 2 + 1)) 0`, but did not retain it in the Lean
  file because the proof needed more careful handling of function multiplication under `deriv`
  and the Gamma pole-avoidance side condition. This was not needed for the selected numerator
  conclusion.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The first derivative calculation behind `ζ'(0)` does not expose
  `deriv completedRiemannZeta₀ 0`; the numerator side only depends on
  `completedRiemannZeta₀ 0`.
- Therefore, evaluating the remaining derivative in `liCoefficientCandidate 1` likely needs
  second-order/Laurent information about zeta/Gamma/completed zeta, or a different structural
  route.

Next route:

- Either return to the denominator derivative as a standalone Lean interface exercise, or move to
  a structural theorem about real-valuedness/conjugation symmetry of the local Li candidate before
  attempting positivity.

## Loop 2026-07-09-25: rewriting the second Li candidate through `λ₀`

Statement selected:

- `completedRiemannZeta₀_zero_eq_one`:
  `completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1`.
- `liCoefficientCandidate_zero_eq_completedZeta₀_zero`:
  `liCoefficientCandidate 0 = completedRiemannZeta₀ 0`.
- `liCoefficientCandidate_one_eq_completedZeta₀_zero_neg_deriv_zero`:
  `liCoefficientCandidate 1 =
    4 * completedRiemannZeta₀ 0 -
      2 * deriv completedRiemannZeta₀ 0 - completedRiemannZeta₀ 0 ^ 2`.
- `liCoefficientCandidate_one_eq_zero_neg_deriv_zero`:
  the same formula with `completedRiemannZeta₀ 0` replaced by `liCoefficientCandidate 0`.
- `liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero`:
  `liCoefficientCandidate 1 =
    liCoefficientCandidate 0 * (4 - liCoefficientCandidate 0) -
      2 * deriv completedRiemannZeta₀ 0`.

Reason:

- Loop 23 and Loop 24 pushed the remaining unknown for `liCoefficientCandidate 1` to
  `deriv completedRiemannZeta₀ 0`.
- Since `liCoefficientCandidate 0` already has a Lean-checked positive real part, rewriting
  `liCoefficientCandidate 1` directly through `liCoefficientCandidate 0` gives a cleaner target
  for future real-valuedness or positivity work.
- This is also a bookkeeping step: it removes unnecessary switching between the symmetric points
  `0` and `1`.

Status before Lean check:

- Passed.

Lean result:

- Added `completedRiemannZeta₀_zero_eq_one`.
- Added `liCoefficientCandidate_zero_eq_completedZeta₀_zero`.
- Added `liCoefficientCandidate_one_eq_completedZeta₀_zero_neg_deriv_zero`.
- Added `liCoefficientCandidate_one_eq_zero_neg_deriv_zero`.
- Added `liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero`.
- The proof uses `completedRiemannZeta₀_one_sub`, earlier `λ₀` and `λ₁` formulas, and `ring`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The second local Li candidate now has a compact Lean-checked expression in terms of the first
  local Li candidate and the remaining completed-zeta derivative:
  `λ₁ = λ₀ * (4 - λ₀) - 2 * Λ₀'(0)`.
- This still does not evaluate `Λ₀'(0)`, prove positivity of `liCoefficientCandidate 1`, or
  establish Li's criterion/RH equivalence.

Next route:

- Try to prove a structural statement about the remaining derivative, such as real-valuedness or
  conjugation compatibility, before attempting numerical positivity.
- Alternatively, revisit the denominator derivative wrapper from Loop 24 as a pure Lean interface
  exercise.

## Loop 2026-07-09-26: real and imaginary parts of the second Li candidate

Statement selected:

- `liCoefficientCandidate_zero_im_eq_zero`:
  `(liCoefficientCandidate 0).im = 0`.
- `liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im`:
  `(liCoefficientCandidate 1).im = -2 * (deriv completedRiemannZeta₀ 0).im`.
- `liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re`:
  `(liCoefficientCandidate 1).re =
    (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
      2 * (deriv completedRiemannZeta₀ 0).re`.

Reason:

- Loop 25 reduced the second local Li candidate to
  `λ₀ * (4 - λ₀) - 2 * deriv completedRiemannZeta₀ 0`.
- Local search found general derivative/conjugation tools in mathlib, but no direct
  conjugation theorem for `completedRiemannZeta₀` ready to apply.
- Since `λ₀` is already known to be a real-coerced complex number, the immediate Lean-checkable
  next step is to split the current `λ₁` formula into real and imaginary parts.

Status before Lean check:

- Passed.

Lean result:

- Added `liCoefficientCandidate_zero_im_eq_zero`.
- Added `liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im`.
- Added `liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re`.
- The proofs use `liCoefficientCandidate_zero_eq_ofReal`,
  `liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero`, and complex real/imaginary part
  simplification.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The imaginary part of `liCoefficientCandidate 1` is exactly controlled by the imaginary part of
  `deriv completedRiemannZeta₀ 0`.
- The real part of `liCoefficientCandidate 1` is reduced to a real expression in `λ₀.re` and
  `(deriv completedRiemannZeta₀ 0).re`.
- This still does not prove `deriv completedRiemannZeta₀ 0` is real, evaluate it, prove
  positivity of `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Try to prove a conjugation compatibility theorem for `completedRiemannZeta₀`, or at least a
  local statement sufficient to show `(deriv completedRiemannZeta₀ 0).im = 0`.
- If that remains too large, inspect `completedHurwitzZetaEven₀` for existing real-valuedness or
  conjugation lemmas.

## Loop 2026-07-09-27: conjugation bridge for the remaining derivative

Statement selected:

- `deriv_zero_im_eq_zero_of_conj_conj_eq_self`: for any `f : ℂ → ℂ`, if
  `((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) = f`, then `(deriv f 0).im = 0`.
- `deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj`: the same bridge specialized to
  `completedRiemannZeta₀`.
- `liCoefficientCandidate_one_im_eq_zero_of_completedZeta₀_conj_conj`: under that completed-zeta
  conjugation compatibility, `(liCoefficientCandidate 1).im = 0`.

Reason:

- Loop 26 showed that the only imaginary-part obstruction for the second local Li candidate is
  `(deriv completedRiemannZeta₀ 0).im`.
- Local search found `deriv_conj_conj` in `Mathlib.Analysis.Calculus.Deriv.Star`, but no direct
  theorem yet saying that `completedRiemannZeta₀` is compatible with complex conjugation.
- The smallest useful Lean-checked target is therefore a bridge theorem: once the function-level
  conjugation statement is proved, the derivative real-valuedness and `λ₁` real-valuedness follow
  immediately.

Status before Lean check:

- Passed after one interface adjustment.

Lean result:

- Imported `Mathlib.Analysis.Calculus.Deriv.Star`.
- Added the three bridge theorems listed above.
- The first proof attempt used an unqualified `conj`, which Lean treated as an unresolved name in
  this file. The final proof uses mathlib's canonical complex conjugation form `starRingEnd ℂ`,
  matching `deriv_conj_conj`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The project now has a Lean-checked conditional bridge from function-level conjugation symmetry to
  the real-valuedness of the remaining derivative at `0`.
- Combining this bridge with Loop 26 proves the second local Li candidate is real whenever
  `completedRiemannZeta₀` satisfies the expected conjugation compatibility.
- This still does not prove the function-level conjugation statement itself, evaluate
  `deriv completedRiemannZeta₀ 0`, prove positivity of `liCoefficientCandidate 1`, or establish
  Li's criterion/RH equivalence.

Next route:

- Try to prove the missing conjugation compatibility theorem for `completedRiemannZeta₀`, probably
  by descending to `completedHurwitzZetaEven₀` and its real-valued integral/kernel definitions.
- If that route is too large, inspect whether a local real-valuedness statement at real arguments
  suffices for `deriv completedRiemannZeta₀ 0`.

## Loop 2026-07-09-28: completed zeta conjugation and real-valuedness of the second candidate

Statement selected:

- `mellin_conj_of_forall_mem_Ioi`: if `f : ℝ → ℂ` is fixed by complex conjugation on `Ioi 0`,
  then `mellin f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mellin f s)`.
- `hurwitzEvenFEPair_zero_f_modif_conj`: the modified kernel
  `(hurwitzEvenFEPair 0).f_modif` is fixed by complex conjugation.
- `hurwitzEvenFEPair_zero_Λ₀_conj`: the `Λ₀` function of the zero-parameter even Hurwitz FE-pair
  is compatible with complex conjugation.
- `completedRiemannZeta₀_conj` and `completedRiemannZeta₀_conj_conj`: the completed Riemann
  zeta function with poles removed is compatible with complex conjugation.
- `deriv_completedRiemannZeta₀_zero_im_eq_zero`: `(deriv completedRiemannZeta₀ 0).im = 0`.
- `liCoefficientCandidate_one_im_eq_zero`: `(liCoefficientCandidate 1).im = 0`.

Reason:

- Loop 27 reduced the remaining imaginary-part obstruction to a function-level conjugation
  compatibility theorem for `completedRiemannZeta₀`.
- `completedRiemannZeta₀` unfolds to `completedHurwitzZetaEven₀ 0`, which unfolds to
  `((hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2`.
- The relevant `Λ₀` is a Mellin transform of `f_modif`; for the zero-parameter even Hurwitz pair,
  this modified kernel is built from real-valued kernels and real correction terms.

Status before Lean check:

- Passed after scope and normalization adjustments.

Lean result:

- Added `open Real Set MeasureTheory` because the proof uses `π`, `Ioi`, `Ioo`, and set-integral
  congruence lemmas.
- Added the seven theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The main Mellin proof uses `integral_conj`, `Complex.cpow_conj`, and the fact that a positive
  real number has argument `0`, hence is not on the negative real branch cut.
- The kernel proof expands `WeakFEPair.f_modif` and splits membership in `Ioi 1` and `Ioo 0 1`;
  each branch is reduced by simplification of real-coerced complex terms.
- The completed-zeta proof handles the `s / 2` argument and division by `2` explicitly using
  `map_div₀`, `starRingEnd_apply`, and `star_ofNat`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The missing function-level conjugation theorem for `completedRiemannZeta₀` is now
  Lean-checked.
- Consequently, the derivative `deriv completedRiemannZeta₀ 0` has zero imaginary part.
- Combining this with Loop 26 proves the second local Li candidate is real-valued:
  `(liCoefficientCandidate 1).im = 0`.
- This still does not evaluate `(deriv completedRiemannZeta₀ 0).re`, prove
  `(liCoefficientCandidate 1).re > 0`, or establish Li's criterion/RH equivalence.

Next route:

- Use the existing real-part formula
  `(liCoefficientCandidate 1).re =
    (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
      2 * (deriv completedRiemannZeta₀ 0).re`
  to decide whether the next Lean-checkable target is a structural formula for
  `(deriv completedRiemannZeta₀ 0).re` or a weaker inequality sufficient for `λ₁` positivity.
- If the derivative's real part remains inaccessible, inspect second-order/Laurent information
  around `riemannZeta_eq_mul_completedRiemannZeta₀`.

## Loop 2026-07-09-29: reducing the second Li candidate to a real inequality target

Statement selected:

- `deriv_completedRiemannZeta₀_zero_eq_ofReal_re`:
  `deriv completedRiemannZeta₀ 0 = ((deriv completedRiemannZeta₀ 0).re : ℂ)`.
- `liCoefficientCandidate_one_eq_ofReal_re`:
  `liCoefficientCandidate 1 = ((liCoefficientCandidate 1).re : ℂ)`.
- `liCoefficientCandidate_one_eq_ofReal_re_formula`:
  `liCoefficientCandidate 1 =
    (((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
      2 * (deriv completedRiemannZeta₀ 0).re : ℝ) : ℂ)`.
- `liCoefficientCandidate_one_re_pos_iff_re_formula`:
  positivity of `(liCoefficientCandidate 1).re` is equivalent to positivity of that explicit real
  expression.

Reason:

- Loop 28 proved `(liCoefficientCandidate 1).im = 0`, closing the real-valuedness part of the
  second local Li candidate.
- The next proof-search step should operate in real arithmetic. Packaging `λ₁` as a real-coerced
  expression avoids repeatedly carrying the imaginary-part side condition.
- This is a small proof-engineering step that turns the next positive-real-part target into a
  single real inequality involving `λ₀.re` and `(deriv completedRiemannZeta₀ 0).re`.

Status before Lean check:

- Passed.

Lean result:

- Added the four theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The proofs use explicit `Complex.ext` for real/imaginary parts, `liCoefficientCandidate_one_im_eq_zero`,
  `deriv_completedRiemannZeta₀_zero_im_eq_zero`, and the Loop 26 real-part formula.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The second local Li candidate is now available as an explicit real-coerced formula.
- Proving its positive real part is reduced to proving:
  `0 < (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
    2 * (deriv completedRiemannZeta₀ 0).re`.
- This still does not evaluate `(deriv completedRiemannZeta₀ 0).re`, prove positivity of
  `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Search mathlib for second-order or Laurent-style information that can expose
  `(deriv completedRiemannZeta₀ 0).re`.
- If no direct special value exists, try deriving a real-part identity from the
  `riemannZeta_eq_mul_completedRiemannZeta₀` expansion beyond first order.

## Loop 2026-07-09-30: center derivative vanishing from one-minus symmetry

Statement selected:

- `deriv_eq_zero_at_half_of_one_sub_eq_self`:
  if `f (1 - s) = f s` for every complex `s`, then `deriv f (1 / 2) = 0`.
- `deriv_riemannXi_half_eq_zero`:
  `deriv riemannXi (1 / 2) = 0`.
- `deriv_completedRiemannZeta₀_half_eq_zero`:
  `deriv completedRiemannZeta₀ (1 / 2) = 0`.

Reason:

- Loop 29 reduced the next Li-candidate positivity target to a real inequality, but local
  search did not reveal a direct special value or inequality for `(deriv completedRiemannZeta₀ 0).re`.
- The completed zeta and local xi function already have the functional equation symmetry
  `s ↦ 1 - s`. Its center consequence at `1 / 2` is small, reusable, and Lean-checkable.
- This gives a verified structural constraint for later Taylor-expansion or local-evenness
  arguments around the critical-line center.

Status before Lean check:

- Passed.

Lean result:

- Added the three theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The generic proof converts the pointwise symmetry into an eventual equality near `1 / 2`,
  differentiates both sides with `Filter.EventuallyEq.deriv_eq`, rewrites the left derivative
  via `deriv_comp_const_sub`, and finishes from `-f' = f'`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Any complex function satisfying exact `f (1 - s) = f s` symmetry has zero derivative at the
  center point `1 / 2`.
- Both the project-local `riemannXi` and mathlib's `completedRiemannZeta₀` satisfy this
  center-derivative vanishing property.
- This is a structural symmetry result; it does not evaluate `(deriv completedRiemannZeta₀ 0).re`,
  prove positivity of `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Try to lift the same symmetry into a local-evenness/Taylor-coefficient statement around
  `1 / 2`, or return to second-order/Laurent information if mathlib exposes enough API.
- Keep the `λ₁` positivity route gated on an actual formula or inequality for
  `(deriv completedRiemannZeta₀ 0).re`.

## Loop 2026-07-09-31: centered evenness from one-minus symmetry

Statement selected:

- `half_sub_eq_of_one_sub_eq_self`:
  if `f (1 - s) = f s`, then `f (1 / 2 - z) = f (1 / 2 + z)`.
- `centered_even_of_one_sub_eq_self`:
  the centered function `fun z => f (1 / 2 + z)` is even.
- `riemannXi_half_sub`, `centered_riemannXi_even`,
  `completedRiemannZeta₀_half_sub`, and `centered_completedRiemannZeta₀_even`:
  specializations to local `riemannXi` and `completedRiemannZeta₀`.
- `deriv_centered_zero_of_one_sub_eq_self`, `deriv_centered_riemannXi_zero`,
  and `deriv_centered_completedRiemannZeta₀_zero`:
  the centered functions have zero first derivative at `0`.

Reason:

- Loop 30 proved the center derivative vanishes at `1 / 2`; the next reusable form is the
  stronger centered-evenness statement.
- The centered form is closer to Taylor-series language: if `g z = f (1 / 2 + z)`, then the
  symmetry becomes `g (-z) = g z`.
- This stays fully within algebraic consequences of the function equation and mathlib derivative
  shift rules; it does not need any unverified zero-distribution claim.

Status before Lean check:

- Passed.

Lean result:

- Added the nine theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The centered-evenness proof applies the symmetry at `1 / 2 + z` and rewrites
  `1 - (1 / 2 + z)` to `1 / 2 - z`.
- The centered derivative proof uses `deriv_comp_const_add` and Loop 30's
  `deriv_eq_zero_at_half_of_one_sub_eq_self`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The local xi function and `completedRiemannZeta₀` are now available in centered even form:
  `z ↦ f (1 / 2 + z)` is unchanged by `z ↦ -z`.
- Their centered first derivatives at `0` are also Lean-checked to be zero.
- This is useful scaffolding for later Taylor-coefficient constraints, but it does not evaluate
  `(deriv completedRiemannZeta₀ 0).re`, prove positivity of `liCoefficientCandidate 1`, or
  establish Li's criterion/RH equivalence.

Next route:

- Search mathlib's `iteratedDeriv` and formal power series APIs for a small theorem that turns
  centered evenness into vanishing of an odd Taylor coefficient.
- If that API is too large for one loop, return to the `λ₁` real-part bottleneck and inspect
  second-order information around `riemannZeta_eq_mul_completedRiemannZeta₀`.

## Loop 2026-07-09-32: odd centered iterated derivatives vanish

Statement selected:

- `iteratedDeriv_odd_eq_zero_of_even`:
  if `g (-z) = g z`, then `iteratedDeriv (2 * k + 1) g 0 = 0`.
- `iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self`:
  if `f (1 - s) = f s`, then all odd centered derivatives of
  `fun z => f (1 / 2 + z)` vanish at `0`.
- `iteratedDeriv_centered_riemannXi_odd_eq_zero`.
- `iteratedDeriv_centered_completedRiemannZeta₀_odd_eq_zero`.

Reason:

- Loop 31 turned the functional equation into centered evenness. The natural Taylor-language
  consequence is that odd centered coefficients vanish.
- mathlib already provides `iteratedDeriv_comp_neg`, which gives the exact factor
  `(-1)^n` under `z ↦ -z`. This makes the all-odd statement small enough to prove in one loop.
- This is a structural consequence of the function equation, not a zero-distribution or
  positivity claim.

Status before Lean check:

- Passed.

Lean result:

- Added the four theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The proof compares `iteratedDeriv n (fun z => g (-z)) 0` with `iteratedDeriv n g 0` using
  function equality from evenness, rewrites the left side by `iteratedDeriv_comp_neg`, and uses
  `(-1 : ℂ) ^ (2 * k + 1) = -1` to conclude `-D = D`, hence `D = 0`.
- An initial proof compiled but produced a flexible-simp linter warning; it was tightened by
  introducing an explicit `hneg` equality.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The local xi function and `completedRiemannZeta₀` now have Lean-checked vanishing of every
  odd centered `iteratedDeriv` at `0`.
- This is precisely the Taylor-side structural consequence expected from the functional equation
  around the critical center `1 / 2`.
- It does not evaluate even centered derivatives, evaluate `(deriv completedRiemannZeta₀ 0).re`,
  prove positivity of `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Investigate whether the second centered derivative of `riemannXi` or `completedRiemannZeta₀`
  can be related cleanly to the existing `λ₁`/`Λ₀'(0)` formulas.
- Alternatively, use the odd-derivative vanishing theorem as a reusable local-evenness lemma and
  return to the `λ₁` real-part bottleneck.

## Loop 2026-07-09-33: centered second derivative of xi

Statement selected:

- `iteratedDeriv_centered_eq`:
  `iteratedDeriv n (fun z => f (1 / 2 + z)) 0 = iteratedDeriv n f (1 / 2)`.
- `iteratedDeriv_centered_riemannXi_eq` and
  `iteratedDeriv_centered_completedRiemannZeta₀_eq`.
- `iteratedDeriv_centered_riemannXi_two_eq_deriv_deriv` and
  `iteratedDeriv_centered_completedRiemannZeta₀_two_eq_deriv_deriv`.
- `analyticAt_deriv_completedRiemannZeta₀_half` and
  `differentiableAt_deriv_completedRiemannZeta₀_half`.
- `deriv_deriv_riemannXi_half`:
  `ξ''(1 / 2) = Λ₀(1 / 2) - (1 / 8) * Λ₀''(1 / 2)`, using project-local notation.
- `iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half`:
  the centered second `iteratedDeriv` of `riemannXi` at `0` has the same expression.

Reason:

- Loop 32 gave vanishing of all odd centered derivatives. The next useful Taylor-side object is
  the first even centered derivative beyond the value term.
- mathlib's `iteratedDeriv_comp_const_add` directly identifies centered derivatives with original
  derivatives at `1 / 2`.
- Expanding `ξ'` at `1 / 2` gives a concrete formula for the centered second derivative in terms
  of `completedRiemannZeta₀` and its second derivative at the center.

Status before Lean check:

- Passed.

Lean result:

- Added the eight theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The generic shift proof uses `iteratedDeriv_comp_const_add`.
- The half-point second-derivative proof reuses the existing `deriv_riemannXi` formula, product
  rules, `deriv_riemannXi_factor`, and differentiability of `deriv completedRiemannZeta₀` at
  `1 / 2`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Centered `iteratedDeriv` is now connected to original derivatives at `1 / 2` for arbitrary
  order.
- The first nontrivial even centered derivative of the local xi scaffold is:
  `Λ₀(1 / 2) - (1 / 8) * Λ₀''(1 / 2)`.
- This still does not evaluate `Λ₀(1 / 2)`, `Λ₀''(1 / 2)`, `(deriv completedRiemannZeta₀ 0).re`,
  prove positivity of `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Inspect whether mathlib has usable special values or sign/real-valuedness facts for
  `completedRiemannZeta₀ (1 / 2)` or the second derivative at `1 / 2`.
- If not, return to the `λ₁` formula and try to relate `Λ₀'(0)` to center-side even derivatives
  through the function equation.

## Loop 2026-07-09-34: real-valuedness of the centered second xi data

Statement selected:

- `value_im_eq_zero_of_conj_conj_eq_self_at_fixed`:
  a conjugation-compatible complex function takes real values at points fixed by conjugation.
- `deriv_conj_conj_eq_self`:
  conjugation compatibility is inherited by the derivative function.
- `complex_half_star`:
  `1 / 2` is fixed by complex conjugation.
- `deriv_completedRiemannZeta₀_conj_conj` and
  `deriv_deriv_completedRiemannZeta₀_conj_conj`.
- `completedRiemannZeta₀_half_im_eq_zero` and
  `deriv_deriv_completedRiemannZeta₀_half_im_eq_zero`.
- `completedRiemannZeta₀_half_eq_ofReal_re` and
  `deriv_deriv_completedRiemannZeta₀_half_eq_ofReal_re`.
- `iteratedDeriv_centered_riemannXi_two_im_eq_zero` and
  `iteratedDeriv_centered_riemannXi_two_eq_ofReal_re`.

Reason:

- Loop 33 expressed the centered second derivative of the local xi function as
  `Λ₀(1 / 2) - (1 / 8) * Λ₀''(1 / 2)`.
- Before any sign or positivity attempt, the center-side quantities should be packaged as real
  values.
- Loop 28 already proved conjugation compatibility for `completedRiemannZeta₀`; this loop lifts
  that compatibility through derivatives and applies it at the real center point.

Status before Lean check:

- Passed.

Lean result:

- Added the ten theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The proof of derivative conjugation compatibility uses mathlib's `deriv_conj_conj`.
- The center value and center second derivative real-valuedness follow by applying the generic
  fixed-point bridge at `1 / 2`.
- The centered second derivative of `riemannXi` is real-valued by Loop 33's formula and the two
  real-valuedness results for the completed zeta terms.
- One compile pass produced a flexible-simp linter warning in the final imaginary-part proof;
  it was replaced by an explicit `simp only` list.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- `completedRiemannZeta₀ (1 / 2)`, `Λ₀''(1 / 2)`, and the centered second derivative of local
  `riemannXi` are now Lean-checked to be real-valued.
- This makes the center-side second-derivative formula suitable for future real inequality or
  sign investigations.
- This still does not evaluate those real quantities, prove any sign, prove positivity of
  `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Search for sign, integral, or Mellin-kernel information about `completedRiemannZeta₀ (1 / 2)`
  or `deriv (deriv completedRiemannZeta₀) (1 / 2)`.
- If no sign route is available, return to the `λ₁` real-part bottleneck and try to relate it to
  center-side real quantities via the function equation.

## Loop 2026-07-09-35: centered second xi derivative as a real inequality target

Statement selected:

- `iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re`:
  the real part of the centered second derivative of `riemannXi` is
  `Λ₀(1 / 2).re - (1 / 8) * Λ₀''(1 / 2).re`.
- `iteratedDeriv_centered_riemannXi_two_eq_ofReal_re_formula`:
  the centered second derivative itself is the complex embedding of that real expression.
- `iteratedDeriv_centered_riemannXi_two_re_pos_iff`:
  positive real part is equivalent to positivity of the corresponding real expression.

Reason:

- A local search found special values for `completedRiemannZeta₀` at `0` and `1`, but no direct
  `1 / 2` special value, sign theorem, or sign-ready Mellin interface.
- Loop 34 proved the center-side second-derivative data is real-valued. The next safe move is to
  package the center-side formula as a pure real inequality target, mirroring the earlier `λ₁`
  real-part reduction.
- This keeps future sign attempts in real arithmetic without claiming a sign now.

Status before Lean check:

- Passed.

Lean result:

- Added the three theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The proof rewrites by Loop 33's center second-derivative formula and simplifies real parts of
  subtraction and scalar multiplication.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The sign target for the centered second derivative of local `riemannXi` is now a pure real
  inequality:
  `0 < (completedRiemannZeta₀ (1 / 2)).re -
    (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re`.
- This does not prove that inequality, evaluate the center terms, prove positivity of
  `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Search for a way to express `completedRiemannZeta₀ (1 / 2)` or
  `deriv (deriv completedRiemannZeta₀) (1 / 2)` through the Mellin kernel in a form usable for
  inequalities.
- If the center-side sign route stalls, return to the existing `λ₁` real inequality and compare
  which bottleneck has better mathlib support.

## Loop 2026-07-09-36: centered xi value as a real target

Statement selected:

- `riemannXi_half`:
  `riemannXi (1 / 2) = 1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2)`.
- `iteratedDeriv_centered_riemannXi_zero_eq_half`.
- `iteratedDeriv_centered_riemannXi_zero_eq_completedZeta₀_half`.
- `riemannXi_half_im_eq_zero` and `riemannXi_half_eq_ofReal_re`.
- `riemannXi_half_re_eq_completedZeta₀_half_re`.
- `riemannXi_half_eq_ofReal_re_formula`.
- `riemannXi_half_re_pos_iff`.

Reason:

- Loops 33-35 handled the first nontrivial even centered derivative. The Taylor expansion also
  needs the zero-order centered value.
- The value at the center is directly available from the local definition of `riemannXi`.
- Loop 34 already proves `completedRiemannZeta₀ (1 / 2)` is real-valued, so the center value can
  also be packaged as a pure real expression.

Status before Lean check:

- Passed.

Lean result:

- Added the seven theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The core identity unfolds `riemannXi` and is discharged by ring arithmetic.
- The real-valuedness proof rewrites by the center formula and uses the conjugation fixed-point
  bridge for `completedRiemannZeta₀ (1 / 2)`.
- An initial compile produced a flexible-simp warning in the imaginary-part proof; it was replaced
  by an explicit `simp only` list.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The centered zero-order Taylor datum is now Lean-packaged as:
  `riemannXi (1 / 2) = 1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2)`.
- Its real part and positivity target reduce to the pure real expression
  `1 / 2 - (1 / 8) * (completedRiemannZeta₀ (1 / 2)).re`.
- This still does not evaluate `completedRiemannZeta₀ (1 / 2)`, prove positivity of
  `riemannXi (1 / 2)` or `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Compare the zero-order and second-order center-side inequality targets:
  both now depend on real parts of `completedRiemannZeta₀` center data.
- Continue investigating whether the Mellin definition of `completedRiemannZeta₀` exposes enough
  positivity to attack either center-side inequality.

## Loop 2026-07-09-37: center value positivity as a completed-zeta upper bound

Statement selected:

- `completedRiemannZeta₀_half_eq_riemannXi_half`:
  `completedRiemannZeta₀ (1 / 2) = 4 - 8 * riemannXi (1 / 2)`.
- `completedRiemannZeta₀_half_re_eq_riemannXi_half_re`:
  `(completedRiemannZeta₀ (1 / 2)).re = 4 - 8 * (riemannXi (1 / 2)).re`.
- `riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four`:
  positivity of the center xi value is equivalent to
  `(completedRiemannZeta₀ (1 / 2)).re < 4`.
- `iteratedDeriv_centered_riemannXi_zero_re_pos_iff_completedZeta₀_half_re_lt_four`:
  the same equivalence for the centered zero-order `iteratedDeriv`.

Reason:

- Loop 36 wrote the center value of local `riemannXi` as
  `1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2)`.
- The inverse form turns a center-value positivity target into a single upper bound on the
  completed zeta center value.
- This is a clearer target for any later Mellin/integral bound attempt.

Status before Lean check:

- Passed.

Lean result:

- Added the four theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The complex inverse formula follows by rewriting with `riemannXi_half` and ring arithmetic.
- The real-part inverse and positivity equivalences use the Loop 36 real-part formula and
  `linarith`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Positivity of the local xi center value is now equivalent to the real upper bound
  `(completedRiemannZeta₀ (1 / 2)).re < 4`.
- This still does not prove the upper bound, evaluate `completedRiemannZeta₀ (1 / 2)`, prove
  positivity of `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Search for a way to express or bound `(completedRiemannZeta₀ (1 / 2)).re`, preferably from
  the Mellin definition or the zero-parameter Hurwitz kernel.
- If no direct upper-bound route appears, compare this center-value target with the center
  second-derivative target and the existing `λ₁` bottleneck.

## Loop 2026-07-09-38: center value upper bound as a Mellin real-part target

Statement selected:

- `completedRiemannZeta₀_half_eq_hurwitzEvenFEPair_Λ₀`:
  `completedRiemannZeta₀ (1 / 2) =
    (hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ) / 2`.
- `completedRiemannZeta₀_half_eq_mellin_hurwitzEvenFEPair_zero`:
  `completedRiemannZeta₀ (1 / 2) =
    mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ) / 2`.
- Real-part versions of both identities.
- `riemannXi_half_re_pos_iff_hurwitzEvenFEPair_Λ₀_re_lt_eight`.
- `riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight`.

Reason:

- Loop 37 reduced center-value positivity of local `riemannXi` to the upper bound
  `(completedRiemannZeta₀ (1 / 2)).re < 4`.
- Mathlib defines `completedRiemannZeta₀` through the zero-parameter even Hurwitz FE-pair, whose
  `Λ₀` is exactly a Mellin transform of the modified kernel.
- Expanding the center value through this definition turns the target into a Mellin real-part
  upper bound. This is a more concrete doorway for later kernel or integral estimates.

Status before Lean check:

- Passed.

Lean result:

- Added the six theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The complex identities are definitional unfoldings plus arithmetic normalization.
- The positivity equivalences reuse Loop 37's completed-zeta upper-bound target and clear the
  factor `2` with real linear arithmetic.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Positivity of the local xi center value is now also equivalent to the Mellin-side bound
  `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8`.
- This does not prove that bound, evaluate the Mellin transform, prove positivity of
  `liCoefficientCandidate 1`, or establish Li's criterion/RH equivalence.

Next route:

- Inspect the concrete zero-parameter Hurwitz modified kernel `f_modif` and mathlib's Mellin
  convergence/positivity API to see whether any usable upper bound can be stated without adding
  unverified assumptions.
- If the upper-bound route stalls, use the same Mellin expansion pattern on the center
  second-derivative target and compare which inequality has better local support.

## Loop 2026-07-09-39: zero-parameter modified kernel is nonnegative on the positive axis

Statement selected:

- `hurwitzEvenFEPair_zero_f_modif_of_one_lt`:
  for `1 < x`,
  `(hurwitzEvenFEPair 0).f_modif x = (evenKernel 0 x : ℂ) - 1`.
- `hasSum_int_hurwitzEvenFEPair_zero_f_modif_of_one_lt`:
  for `1 < x`, the real part of the modified kernel is the sum over `ℤ` with the zero term
  removed.
- `hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one` and
  `hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one_eq_scaled_cosKernel`:
  for `0 < x < 1`, the modified kernel equals the small-side branch and also the scaled
  `cosKernel 0 (1 / x) - 1` expression.
- `hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one`:
  for `0 < x < 1`, the real part is a positive scalar times the positive `cosKernel` tail.
- `hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos`:
  for all `0 < x`, `0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re`.

Reason:

- Loop 38 moved the center value target to the Mellin transform of
  `(hurwitzEvenFEPair 0).f_modif`.
- To use that representation for estimates, the first concrete question is what this modified
  kernel looks like on the Mellin integration domain `0 < x`.
- Mathlib already has theta-kernel sum formulae for both `evenKernel` and `cosKernel`, so a small
  Lean step can expose positivity of the modified kernel without adding new analytic estimates.

Status before Lean check:

- Passed after replacing one flexible simplification in the nonzero integer branch with an
  explicit `exp_pos` nonnegativity proof.

Lean result:

- Added nine kernel theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The large-side sum uses `hasSum_int_evenKernel₀`.
- The small-side sum uses the theta functional equation and `hasSum_nat_cosKernel₀`.
- Nonnegativity follows by rewriting the real part as a `tsum` of nonnegative terms.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin kernel appearing in the Loop 38 center-value expression has verified nonnegative real
  part on the positive real axis.
- This still does not prove the Mellin upper bound `< 8`; in fact nonnegativity alone gives no
  upper estimate. It also does not prove positivity of `liCoefficientCandidate 1` or establish
  Li's criterion/RH equivalence.

Next route:

- Try to express `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re` as an integral of a real
  nonnegative integrand, using the just-proved kernel realness and nonnegativity.
- Then investigate whether existing theta tail bounds can provide an actual finite upper bound,
  or whether the more realistic next step is only an integral nonnegativity theorem.

## Loop 2026-07-09-40: Mellin center integrand and transform are nonnegative

Statement selected:

- `ofReal_cpow_quarter_sub_one`:
  for `0 < x`,
  `(x : ℂ) ^ ((1 / 4 : ℂ) - 1) = (x ^ (-(3 / 4 : ℝ)) : ℂ)`.
- `mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_eq`:
  the real part of the Mellin integrand at `s = 1 / 4` equals
  `x ^ (-(3 / 4 : ℝ)) * ((hurwitzEvenFEPair 0).f_modif x).re`.
- `mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_nonneg`:
  the real part of that integrand is nonnegative for `0 < x`.
- `mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral`:
  the Mellin real part at `1 / 4` is the integral over `Ioi 0` of that real integrand.
- `mellin_hurwitzEvenFEPair_zero_quarter_re_nonneg`,
  `hurwitzEvenFEPair_zero_Λ₀_quarter_re_nonneg`,
  `completedRiemannZeta₀_half_re_nonneg`, and `riemannXi_half_re_le_one_half`.

Reason:

- Loop 39 proved the modified kernel has nonnegative real part on the positive real axis.
- At the center-value Mellin parameter `s = 1 / 4`, the weight `x ^ (s - 1)` is the positive real
  weight `x ^ (-3 / 4)`.
- Therefore the Mellin-side quantity from Loop 38 should at least be a nonnegative real integral.
  This is a necessary structural step before searching for any actual upper bound.

Status before Lean check:

- Passed.

Lean result:

- Added the eight theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The `cpow` conversion uses `Complex.ofReal_cpow` on positive real inputs.
- The integral real-part theorem uses the `HasMellin` convergence provided by the strong FE-pair
  associated to `(hurwitzEvenFEPair 0).f_modif`.
- Nonnegativity follows from `setIntegral_nonneg`, Loop 39's kernel nonnegativity, and
  nonnegativity of real powers.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin-side quantity in the center-value target now has a verified nonnegative real-part
  integral representation.
- This yields the lower bound
  `0 ≤ (completedRiemannZeta₀ (1 / 2)).re` and the upper bound
  `(riemannXi (1 / 2)).re ≤ 1 / 2`.
- This still does not prove the needed upper bound
  `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8`, nor center-value positivity,
  positivity of `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Search mathlib's Jacobi theta bound files for usable tail estimates on the large-side and
  small-side series in Loop 39.
- A realistic next Lean target is an explicit finite comparison bound for the nonnegative
  integrand, even if it is initially too weak to imply `< 8`.

## Loop 2026-07-09-41: two-sided theta-tail comparison bounds for the Mellin integrand

Statement selected:

- `hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_one_lt`:
  for `1 < x`, the large-side modified kernel real part is the positive natural-number theta tail
  `∑ n, 2 * exp (-π * (n + 1)^2 * x)`.
- `hurwitzEvenFEPair_zero_f_modif_re_eq_two_F_nat_one_of_one_lt`:
  for `1 < x`, this real part is `2 * HurwitzKernelBounds.F_nat 0 1 x`.
- `hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt` and
  `mellin_quarter_integrand_re_le_exp_tail_of_one_lt`:
  for `1 < x`, the kernel and Mellin integrand are bounded by the geometric theta-tail
  comparison `2 * exp (-π*x) / (1 - exp (-π*x))`, with the Mellin weight included for the
  integrand.
- `hurwitzEvenFEPair_zero_f_modif_re_eq_scaled_two_F_nat_one_of_pos_lt_one`,
  `hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_pos_lt_one`, and
  `mellin_quarter_integrand_re_le_exp_tail_of_pos_lt_one`:
  the analogous `0 < x < 1` comparison after the functional-equation change of variable
  `1 / x`.

Reason:

- Loop 40 showed the Mellin real part is an integral of a nonnegative integrand.
- To move from nonnegativity to an upper estimate, the integrand needs explicit comparison
  functions on both sides of the split at `x = 1`.
- Mathlib's `HurwitzKernelBounds.F_nat_zero_le` provides a ready geometric-series upper bound for
  the theta tail `F_nat 0 1`.

Status before Lean check:

- Passed.

Lean result:

- Added seven comparison theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The large side rewrites the zero-parameter kernel tail through `cosKernel` and
  `hasSum_nat_cosKernel₀`, then through `HurwitzKernelBounds.F_nat`.
- The small side reuses Loop 39's scaled `cosKernel 0 (1 / x) - 1` expression.
- Both bounds use `HurwitzKernelBounds.F_nat_zero_le`, `le_abs_self`, and nonnegativity of the
  Mellin real weight.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The nonnegative Mellin integrand from Loop 40 now has explicit comparison upper bounds on
  `1 < x` and `0 < x < 1`.
- This still does not integrate those comparison functions, does not prove the global Mellin
  upper bound `< 8`, and does not prove center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Try to split the Mellin real-part integral over `Ioi 0` into the intervals `(0, 1)` and
  `(1, ∞)`, so the two Loop 41 comparison bounds can be applied.
- If interval splitting is too heavy, first prove integrability or finiteness of the comparison
  functions using the existing exponential-decay infrastructure.

## Loop 2026-07-09-42: split the Mellin real-part integral into two nonnegative pieces

Statement selected:

- `mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral_split`:
  the real part of the Mellin transform at `1 / 4` is the sum of its integrals over
  `Ioo 0 1` and `Ioi 1`.
- `mellin_quarter_integral_Ioo_zero_one_nonneg`:
  the left interval contribution is nonnegative.
- `mellin_quarter_integral_Ioi_one_nonneg`:
  the right interval contribution is nonnegative.

Reason:

- Loop 41 produced different explicit comparison bounds on the two natural ranges
  `0 < x < 1` and `1 < x`.
- To use those bounds at the integral level, the Loop 40 integral over `Ioi 0` first needs a
  verified decomposition at `x = 1`.
- The split also gives a useful sanity check: both pieces are nonnegative because the underlying
  Mellin integrand has nonnegative real part for every positive `x`.

Status before Lean check:

- Passed.

Lean result:

- Added the three theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The split proof obtains integrability from the existing `HasMellin` witness for the
  zero-parameter Hurwitz FE-pair.
- The interval decomposition uses `Ioc_union_Ioi_eq_Ioi`, `setIntegral_union`, and
  `integral_Ioc_eq_integral_Ioo`.
- The two nonnegativity statements reuse the Loop 40 pointwise integrand nonnegativity theorem.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin real part from the center-value route is now decomposed into two verified
  nonnegative interval contributions.
- This prepares the ground for applying the Loop 41 large-side and small-side comparison bounds
  under the integral sign.
- This still does not integrate the comparison functions, prove the global Mellin upper bound
  `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`, or Li's
  criterion/RH equivalence.

Next route:

- Try to lift the Loop 41 pointwise comparison inequalities to integral inequalities on
  `(0, 1)` and `(1, ∞)`.
- If `setIntegral_mono` requires unavailable integrability facts for the explicit majorants,
  first formalize the needed integrability or finite-bound wrappers for the two exponential
  tail functions.

## Loop 2026-07-09-43: conditional integral comparison for the split Mellin pieces

Statement selected:

- `mellin_quarter_integral_Ioo_zero_one_le_exp_tail`:
  assuming the small-side explicit exponential-tail majorant is integrable on `Ioo 0 1`, the
  actual left Mellin contribution is bounded above by the integral of that majorant.
- `mellin_quarter_integral_Ioi_one_le_exp_tail`:
  assuming the large-side explicit exponential-tail majorant is integrable on `Ioi 1`, the actual
  right Mellin contribution is bounded above by the integral of that majorant.

Reason:

- Loop 42 split the Mellin real-part integral into left and right contributions.
- Loop 41 already proved pointwise comparison bounds on exactly those two regions.
- The natural bridge is `setIntegral_mono_on`, but it requires integrability of both the actual
  integrand and the chosen majorant. The actual integrand is integrable by the `HasMellin`
  witness; the majorant integrability is kept as an explicit hypothesis rather than assumed.

Status before Lean check:

- Passed after one local adjustment.

Lean result:

- Added the two conditional comparison theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The first proof attempt tried to chain `.mono_set` directly from `hM.1.re`; Lean needed that
  expression first typed as an `IntegrableOn` fact for the whole `Ioi 0` interval.
- After adding that intermediate fact, both comparisons close by restricting integrability to
  the relevant subinterval and applying `setIntegral_mono_on`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Loop 41 pointwise comparison bounds now have verified integral-level interfaces.
- The only remaining condition for using them unconditionally is integrability of the two
  explicit majorants.
- This still does not integrate those majorants, prove the global Mellin upper bound `< 8`,
  center-value positivity, positivity of `liCoefficientCandidate 1`, or Li's criterion/RH
  equivalence.

Next route:

- Prove the large-side majorant is integrable on `Ioi 1`; this should be approachable through
  exponential decay plus a denominator bounded away from zero.
- The small-side majorant on `Ioo 0 1` likely needs a substitution or a separate decay estimate
  involving `exp (-π / x)` near `0`.

## Loop 2026-07-09-44: uniform large-side denominator bound for the explicit tail majorant

Statement selected:

- `one_sub_rexp_neg_pi_mul_pos_of_pos`:
  for `0 < x`, the denominator `1 - exp (-π*x)` is positive.
- `one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_of_one_le`:
  for `1 ≤ x`, the denominator is bounded below by `1 - exp (-π)`.
- `rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le`:
  for `1 ≤ x`, the quotient `exp (-π*x) / (1 - exp (-π*x))` is bounded by the same exponential
  times the fixed reciprocal `(1 - exp (-π))⁻¹`.
- `mellin_quarter_right_exp_tail_le_const_mul_rexp`:
  for `1 ≤ x`, the large-side explicit majorant from Loop 41 is bounded by
  `(2 * (1 - exp (-π))⁻¹) * exp (-π*x)`.

Reason:

- Loop 43 isolated large-side majorant integrability as the next missing condition.
- The large-side denominator tends to `1`, so the expected proof is to bound it away from zero
  uniformly on `x ≥ 1`.
- Once the denominator is controlled and `x ^ (-3/4) ≤ 1` on `x ≥ 1`, the whole majorant is
  dominated by a constant multiple of a standard exponentially decaying function.

Status before Lean check:

- Passed after a small `mul_le_mul` nonnegativity-argument correction.

Lean result:

- Added the four theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The denominator positivity follows from `exp_lt_one_iff` and `π*x > 0`.
- The lower bound on the denominator uses monotonicity of `exp` and `x ≥ 1`.
- The quotient bound uses `inv_le_inv₀`.
- The final weighted bound uses `Real.rpow_le_rpow_of_exponent_le` to prove
  `x ^ (-3/4) ≤ 1`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The large-side explicit majorant is now pointwise dominated on `Ioi 1` by a constant multiple of
  `exp (-π*x)`.
- This is a direct bridge toward proving the large-side majorant integrability assumption used in
  Loop 43.
- This still does not prove that integrability statement, integrate the majorant, prove the
  global Mellin upper bound `< 8`, center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Use `exp_neg_integrableOn_Ioi` or `integrableOn_exp_mul_Ioi` plus the Loop 44 pointwise bound
  to prove the large-side majorant is integrable on `Ioi 1`.
- After that, instantiate `mellin_quarter_integral_Ioi_one_le_exp_tail` unconditionally for the
  right interval.

## Loop 2026-07-09-45: large-side explicit majorant is integrable

Statement selected:

- `integrableOn_mellin_quarter_right_exp_tail`:
  the large-side explicit majorant
  `x ^ (-3/4) * (2 * (exp (-π*x) / (1 - exp (-π*x))))`
  is integrable on `Ioi 1`.

Reason:

- Loop 43 needed majorant integrability to turn the pointwise large-side comparison into an
  integral comparison.
- Loop 44 proved that this majorant is pointwise bounded on `x ≥ 1` by a constant multiple of
  `exp (-π*x)`.
- Mathlib's `integrable_of_isBigO_exp_neg` is designed exactly for continuous functions with
  exponential decay at infinity.

Status before Lean check:

- Passed after importing `Mathlib.MeasureTheory.Integral.ExpDecay` and opening the `Filter` and
  `Asymptotics` namespaces.

Lean result:

- Added `integrableOn_mellin_quarter_right_exp_tail` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The continuity proof was made explicit: continuity of the rpow factor on `Ici 1`, continuity of
  the exponential factor, denominator nonvanishing from Loop 44, and then continuity of the
  quotient and product.
- The Big-O proof uses `Eventually.isBigO`, the Loop 44 pointwise bound, and a constant-multiple
  `isBigO_refl` step.
- `integrable_of_isBigO_exp_neg pi_pos` then gives integrability on `Ioi 1`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The large-side majorant integrability assumption from Loop 43 has now been discharged.
- This enables an unconditional integral comparison for the right interval.
- This still does not handle the small-side majorant, integrate either majorant explicitly, prove
  the global Mellin upper bound `< 8`, center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Instantiate `mellin_quarter_integral_Ioi_one_le_exp_tail` with
  `integrableOn_mellin_quarter_right_exp_tail` to get the unconditional right-interval integral
  comparison.
- Then turn to the small-side majorant on `Ioo 0 1`, where the likely route is a substitution
  `u = 1/x` or a separate near-zero exponential-decay estimate.

## Loop 2026-07-09-46: unconditional right-interval integral comparison

Statement selected:

- `mellin_quarter_integral_Ioi_one_le_integral_exp_tail`:
  the right Mellin contribution over `Ioi 1` is bounded above by the integral of the large-side
  explicit exponential-tail majorant, with no extra integrability hypothesis.

Reason:

- Loop 43 proved the right-interval integral comparison under an explicit majorant-integrability
  assumption.
- Loop 45 discharged exactly that assumption.
- Instantiating the conditional theorem gives the first unconditional integral comparison in the
  split Mellin-bound route.

Status before Lean check:

- Passed.

Lean result:

- Added `mellin_quarter_integral_Ioi_one_le_integral_exp_tail` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof is a direct application of `mellin_quarter_integral_Ioi_one_le_exp_tail` to
  `integrableOn_mellin_quarter_right_exp_tail`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The right side of the split Mellin integral now has an unconditional comparison with an
  explicit integrable majorant.
- This still does not handle the small-side majorant, evaluate the right majorant integral, prove
  the global Mellin upper bound `< 8`, center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Focus on the small-side majorant on `Ioo 0 1`.
- The most likely path is to transform or compare
  `x ^ (-3/4) * x ^ (-1/2) * exp (-π / x) / (1 - exp (-π / x))`
  to an integrable expression after the substitution `u = 1/x`, or first prove a simpler
  near-zero domination by `exp (-π / x)` times a power.

## Loop 2026-07-09-47: small-side explicit majorant has a uniform denominator bound

Statement selected:

- `one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_inv_of_pos_le_one`:
  for `0 < x ≤ 1`, the denominator `1 - exp (-π / x)` is bounded below by `1 - exp (-π)`.
- `rexp_neg_pi_mul_inv_div_one_sub_le_const_mul_rexp_neg_pi_mul_inv_of_pos_le_one`:
  for `0 < x ≤ 1`, the quotient
  `exp (-π / x) / (1 - exp (-π / x))`
  is bounded above by `(1 - exp (-π))⁻¹ * exp (-π / x)`.
- `mellin_quarter_left_exp_tail_le_const_mul_rexp_inv`:
  the small-side explicit majorant is bounded by
  `(2 * (1 - exp (-π))⁻¹) * (x ^ (-5/4) * exp (-π / x))`.

Reason:

- Loop 46 left only the small-side majorant as the next comparison/integrability gap.
- On `0 < x ≤ 1`, the substitution variable `1/x` lies in the large range `≥ 1`, so the same
  denominator control used on the right interval can be reused.
- Combining the two power weights `x ^ (-3/4)` and `x ^ (-1/2)` gives the natural near-zero
  comparison shape `x ^ (-5/4) * exp (-π / x)`.

Status before Lean check:

- Passed.

Lean result:

- Added the three theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The first two proofs reuse the large-side denominator and quotient bounds with
  `one_le_one_div h0 h1`.
- The weighted bound multiplies the quotient estimate by the nonnegative power weights and uses
  `Real.rpow_add` to combine `x ^ (-3/4) * x ^ (-1/2)` into `x ^ (-5/4)`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The small-side majorant now has a verified pointwise domination by a simpler near-zero
  exponential-decay expression.
- This is the left-interval analogue of the Loop 44 large-side domination step.
- This still does not prove the small-side majorant is integrable, instantiate the left
  conditional integral comparison, evaluate any majorant integral, prove the global Mellin upper
  bound `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`, or Li's
  criterion/RH equivalence.

Next route:

- Prove integrability of `x ^ (-5/4) * exp (-π / x)` on `Ioo 0 1`.
- The likely route is to use mathlib's `integrableOn_Ioi_comp_rpow_iff` or a dedicated change of
  variables with `u = 1/x`, reducing the near-zero estimate to exponential decay at infinity.

## Loop 2026-07-09-48: near-zero bound is integrable

Statement selected:

- `integrableOn_mellin_quarter_left_near_zero_bound`:
  the near-zero comparison function
  `x ^ (-5/4) * exp (-π / x)` is integrable on `Ioo 0 1`.

Reason:

- Loop 47 reduced the small-side majorant to a constant multiple of this simpler near-zero
  expression.
- Under the substitution `u = 1/x`, the expression corresponds to the standard integrable
  function `u ^ (-3/4) * exp (-π*u)` on `Ioi 0`, with the Jacobian power included.
- Mathlib already has both ingredients: `integrableOn_rpow_mul_exp_neg_mul_rpow` for the standard
  exponential-decay integral, and `integrableOn_Ioi_comp_rpow_iff'` for the rpow change of
  variables.

Status before Lean check:

- Passed after normalizing `x ^ (-1)` to `1 / x` with `one_div`.

Lean result:

- Imported `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`.
- Added `integrableOn_mellin_quarter_left_near_zero_bound` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof first shows `u ^ (-3/4) * exp (-π*u)` is integrable on `Ioi 0`.
- Then it applies `integrableOn_Ioi_comp_rpow_iff'` with exponent `-1`.
- The resulting transformed integrand is algebraically identified with
  `x ^ (-5/4) * exp (-π / x)` using `Real.rpow_mul`, `Real.rpow_add`, and `one_div`.
- Finally the whole-`Ioi 0` result is restricted to `Ioo 0 1`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The simplified near-zero function controlling the small-side majorant is now verified
  integrable.
- Together with Loop 47, this should make it possible to discharge the small-side majorant
  integrability assumption from Loop 43.
- This still does not directly prove the original small-side majorant is integrable, instantiate
  the left conditional integral comparison, evaluate any majorant integral, prove the global
  Mellin upper bound `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`,
  or Li's criterion/RH equivalence.

Next route:

- Use Loop 47's pointwise domination and Loop 48's integrability result to prove the original
  small-side explicit majorant is integrable on `Ioo 0 1`.
- Then instantiate `mellin_quarter_integral_Ioo_zero_one_le_exp_tail` unconditionally.

## Loop 2026-07-09-49: small-side explicit majorant is integrable

Statement selected:

- `integrableOn_mellin_quarter_left_exp_tail`:
  the original small-side explicit majorant
  `x ^ (-3/4) * (x ^ (-1/2) *
  (2 * (exp (-π / x) / (1 - exp (-π / x)))))`
  is integrable on `Ioo 0 1`.

Reason:

- Loop 47 gave the pointwise domination by a constant multiple of
  `x ^ (-5/4) * exp (-π / x)` on `0 < x ≤ 1`.
- Loop 48 proved that simpler near-zero comparison function is integrable on `Ioo 0 1`.
- This loop discharges the remaining small-side integrability hypothesis needed by the
  conditional left-interval comparison from Loop 43.

Status before Lean check:

- Passed.

Lean result:

- Added `integrableOn_mellin_quarter_left_exp_tail` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof first takes `integrableOn_mellin_quarter_left_near_zero_bound` and multiplies by the
  positive constant `2 * (1 - exp (-π))⁻¹`.
- It proves the original majorant is strongly measurable on `Ioo 0 1` by explicit continuity:
  rpow continuity for the two powers, quotient continuity for
  `exp (-π / x) / (1 - exp (-π / x))`, and denominator nonvanishing from the positive-denominator
  lemma.
- It then applies `Integrable.mono'` with the Loop 47 pointwise bound; the interval hypothesis
  `x < 1` is converted to `x ≤ 1`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The small-side explicit majorant integrability assumption from Loop 43 is now verified.
- Together with Loop 46, both split intervals now have their explicit majorant integrability
  available.
- This still does not instantiate the left conditional integral comparison, evaluate either
  majorant integral, prove the global Mellin upper bound `< 8`, center-value positivity,
  positivity of `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Instantiate `mellin_quarter_integral_Ioo_zero_one_le_exp_tail` with
  `integrableOn_mellin_quarter_left_exp_tail` to obtain the unconditional left-interval integral
  comparison.

## Loop 2026-07-09-50: unconditional left-interval integral comparison

Statement selected:

- `mellin_quarter_integral_Ioo_zero_one_le_integral_exp_tail`:
  the left split Mellin contribution over `Ioo 0 1` is bounded by the integral of the verified
  small-side explicit majorant.

Reason:

- Loop 43 already proved the left interval comparison under the single hypothesis that the
  small-side explicit majorant is integrable.
- Loop 49 discharged exactly that hypothesis.
- This is the left-interval analogue of Loop 46.

Status before Lean check:

- Passed.

Lean result:

- Added `mellin_quarter_integral_Ioo_zero_one_le_integral_exp_tail` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof is a direct application of
  `mellin_quarter_integral_Ioo_zero_one_le_exp_tail
  integrableOn_mellin_quarter_left_exp_tail`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Both split Mellin contributions now have unconditional integral comparisons against their
  explicit majorants:
  the right side from Loop 46 and the left side from this loop.
- This still does not evaluate either majorant integral, combine the two comparisons into a
  global upper bound, prove the target `< 8`, center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Combine the split identity from Loop 42 with the left and right comparison inequalities from
  Loop 50 and Loop 46 to obtain a global upper comparison by the sum of the two majorant
  integrals.

## Loop 2026-07-09-51: global Mellin upper comparison by split majorants

Statement selected:

- `mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_exp_tails`:
  the Mellin real part at `1 / 4` is bounded above by the sum of the small-side and large-side
  explicit majorant integrals.

Reason:

- Loop 42 already rewrote the Mellin real part as the sum of the left and right split integrals.
- Loop 46 bounds the right split integral by the large-side majorant integral.
- Loop 50 bounds the left split integral by the small-side majorant integral.
- The smallest remaining formal step was to combine these three facts with `add_le_add`.

Status before Lean check:

- Passed.

Lean result:

- Added `mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_exp_tails` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof rewrites by `mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral_split`, then applies
  `add_le_add` to the two interval comparison theorems.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The center-value route now has a verified global upper comparison:
  Mellin real part ≤ left explicit majorant integral + right explicit majorant integral.
- This still does not evaluate or numerically bound the two majorant integrals, prove the target
  `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`, or Li's
  criterion/RH equivalence.

Next route:

- Try to transform the left majorant integral under `u = 1/x` and compare it with a right-side
  exponential tail integral, or seek mathlib lemmas for integrating/bounding
  `x^a * exp (-π*x)` tails strongly enough to make the sum explicitly `< 8`.

## Loop 2026-07-09-52: simplify the global majorant integrals

Statement selected:

- `mellin_quarter_left_exp_tail_integral_le_const_integral_rexp_inv`:
  the small-side explicit majorant integral is bounded by the constant multiple of
  `x ^ (-5/4) * exp (-π / x)`.
- `mellin_quarter_right_exp_tail_integral_le_const_integral_rexp`:
  the large-side explicit majorant integral is bounded by the constant multiple of
  `exp (-π*x)`.
- `mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_const_exp_bounds`:
  the Mellin real part is bounded above by the sum of these two simpler integrals.

Reason:

- Loop 51 gave a global upper bound, but its integrands still had geometric-series denominators.
- Loop 47 and Loop 44 already supplied pointwise denominator removal on the small and large
  intervals.
- Integrating those bounds gives a cleaner target for later numerical or analytic estimation.

Status before Lean check:

- Passed.

Lean result:

- Added the three theorems listed above to `LeanLab/Riemann/LiScaffold.lean`.
- The left integral comparison uses `setIntegral_mono_on` with
  `integrableOn_mellin_quarter_left_exp_tail` and the constant multiple of
  `integrableOn_mellin_quarter_left_near_zero_bound`.
- The right integral comparison uses `exp_neg_integrableOn_Ioi 1 pi_pos` for the simpler
  exponential bound and applies the large-side pointwise inequality on `1 < x`.
- The global simplified comparison follows by transitivity from Loop 51 and `add_le_add`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin-side target is now reduced to estimating
  `C * ∫_(0,1) x^(-5/4) exp(-π/x) dx + C * ∫_(1,∞) exp(-π*x) dx`
  where `C = 2 * (1 - exp (-π))⁻¹`.
- This still does not evaluate those integrals, prove the target `< 8`, center-value positivity,
  positivity of `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Prove a change-of-variables inequality/equality that sends the left simplified integral to a
  tail integral involving `u ^ (-3/4) * exp (-π*u)` on `Ioi 1`, or first bound the left integrand
  by a cruder expression whose integral mathlib can evaluate or estimate.

## Loop 2026-07-09-53: rpow substitution for the near-zero model integral

Statement selected:

- `integral_Ioi_near_zero_bound_eq_integral_exp_tail`:
  over the whole positive half-line, the substitution `u = 1/x` rewrites
  `∫ x in Ioi 0, x^(-5/4) * exp (-π / x)` as
  `∫ u in Ioi 0, u^(-3/4) * exp (-π*u)`.

Reason:

- Loop 52 reduced the left simplified majorant to the near-zero model
  `x^(-5/4) * exp (-π / x)`.
- Mathlib has `integral_comp_rpow_Ioi`, a direct rpow change-of-variables theorem for integrals
  over `Ioi 0`.
- Proving the whole-positive-half-line identity is a smaller reliable step before trying the
  sharper interval mapping `(0,1) ↔ (1,∞)`.

Status before Lean check:

- Passed after reversing the pointwise congruence direction.

Lean result:

- Added `integral_Ioi_near_zero_bound_eq_integral_exp_tail` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof applies `integral_comp_rpow_Ioi` with exponent `-1` to
  `fun u => u ^ (-3/4) * exp (-π*u)`.
- It then normalizes the transformed integrand with
  `x ^ (-1) = 1 / x`, `Real.rpow_mul`, and `Real.rpow_add`, obtaining the power
  `x ^ (-5/4)`.
- The first Lean attempt had the pointwise equality in the wrong direction for
  `setIntegral_congr_fun`; adding `symm` fixed it.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The near-zero model integral is now formally connected to the standard exponential-tail model
  used in Loop 48.
- This still does not give the sharper `(0,1)` to `(1,∞)` interval identity, evaluate the integral,
  prove the target `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`, or
  Li's criterion/RH equivalence.

Next route:

- Either derive the sharper interval-restricted substitution for `(0,1)` and `(1,∞)`, or use
  `setIntegral_mono_set` to bound the `(0,1)` integral by the whole-positive-half-line integral
  and then seek a usable gamma/tail bound.

## Loop 2026-07-09-54: coarse left-interval bound by the full transformed tail

Statement selected:

- `integrableOn_mellin_quarter_left_near_zero_bound_Ioi`:
  the near-zero model `x^(-5/4) * exp (-π / x)` is integrable on the whole `Ioi 0`.
- `integral_Ioo_near_zero_bound_le_integral_Ioi_near_zero_bound`:
  the `(0,1)` integral of that model is bounded by its whole-positive-half-line integral.
- `integral_Ioo_near_zero_bound_le_integral_exp_tail_Ioi`:
  combining the previous inequality with Loop 53 bounds the `(0,1)` integral by
  `∫ u in Ioi 0, u^(-3/4) * exp (-π*u)`.

Reason:

- Loop 53 proved the whole-positive-half-line substitution identity.
- The actual small-side bound only needs the `(0,1)` part; enlarging the domain is a safe coarse
  upper bound because the model integrand is nonnegative.
- This gives a usable next target even before proving the sharper interval-restricted
  substitution.

Status before Lean check:

- Passed.

Lean result:

- Refactored the Loop 48 proof to expose
  `integrableOn_mellin_quarter_left_near_zero_bound_Ioi`; the original
  `integrableOn_mellin_quarter_left_near_zero_bound` is now its restriction to `Ioo 0 1`.
- Added the two integral comparison theorems listed above.
- The domain enlargement uses `setIntegral_mono_set`, nonnegativity of the integrand on
  `Ioi 0`, and `Ioo_subset_Ioi_self.eventuallyLE`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The left simplified integral can now be bounded by a standard full-half-line integral of
  `u^(-3/4) * exp (-π*u)`.
- This is coarser than the expected `(1,∞)` tail after the exact interval substitution, but it is
  fully Lean-verified and may still be enough for a rough numerical upper bound.
- This still does not evaluate that tail integral, prove the target `< 8`, center-value positivity,
  positivity of `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Search mathlib for Gamma/incomplete-Gamma style evaluations or inequalities for
  `∫ u in Ioi 0, u^(-3/4) * exp (-π*u)`, and for the explicit right tail
  `∫ x in Ioi 1, exp (-π*x)`.

## Loop 2026-07-09-55: exact evaluation of the right exponential tail

Statement selected:

- `integral_Ioi_one_rexp_neg_pi_mul_eq`:
  `∫ x in Ioi 1, exp (-π*x) = exp (-π) / π`.
- `integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq`:
  the same evaluation with the constant factor `2 * (1 - exp (-π))⁻¹` used in the global
  simplified majorant.

Reason:

- Loop 52 reduced the right side of the global majorant to a constant multiple of
  `∫ x in Ioi 1, exp (-π*x)`.
- Mathlib's `integral_exp_mul_Ioi` directly evaluates `∫ exp (a*x)` on a half-line when `a < 0`.
- This is the smallest fully determinate tail-integral evaluation before tackling the more
  delicate Gamma-type left integral.

Status before Lean check:

- Passed.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The first proof applies `integral_exp_mul_Ioi` with `a = -π` and `c = 1`.
- The second proof uses `integral_const_mul` and the first theorem.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The right simplified majorant integral from Loop 52 is now explicitly evaluated.
- This still does not evaluate or bound the left Gamma-type integral
  `∫ u in Ioi 0, u^(-3/4) * exp (-π*u)`, combine the evaluated right tail into a new global
  bound, prove the target `< 8`, center-value positivity, positivity of `liCoefficientCandidate 1`,
  or Li's criterion/RH equivalence.

Next route:

- Use `integral_rpow_mul_exp_neg_mul_Ioi` or related Gamma theorems to express the left full
  tail integral as a scaled Gamma value, then investigate whether a crude upper bound is already
  available or easy to prove.

## Loop 2026-07-09-56: Gamma expression for the left full tail

Statement selected:

- `integral_Ioi_exp_tail_eq_gamma_quarter`:
  `∫ u in Ioi 0, u^(-3/4) * exp (-π*u) =
  (1 / π)^(1/4) * Real.Gamma (1/4)`.
- `integral_Ioi_const_mul_exp_tail_eq_gamma_quarter`:
  the same identity with the constant factor `2 * (1 - exp (-π))⁻¹`.

Reason:

- Loop 54 bounded the actual left near-zero integral by the full standard tail integral.
- Mathlib's `Real.integral_rpow_mul_exp_neg_mul_Ioi` exactly evaluates
  `∫ t^(a-1) * exp (-(r*t))` in terms of `Real.Gamma a`.
- Taking `a = 1/4` and `r = π` matches the exponent `-3/4`.

Status before Lean check:

- Passed after explicitly normalizing `1/4 - 1 = -3/4`.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The proof applies `Real.integral_rpow_mul_exp_neg_mul_Ioi` with `a = 1/4` and `r = π`.
- The pointwise congruence rewrites the exponent and argument shapes, then `ring_nf` closes the
  algebraic normalization.
- The constant-multiple version follows by `integral_const_mul`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Both simplified tail integrals from Loop 52 now have explicit forms: the right one in elementary
  exponentials, and the left coarse one in terms of `Real.Gamma (1/4)`.
- This still does not prove a numerical bound for `Real.Gamma (1/4)`, combine these evaluations
  into a single global theorem, prove the target `< 8`, center-value positivity, positivity of
  `liCoefficientCandidate 1`, or Li's criterion/RH equivalence.

Next route:

- Combine Loop 52, Loop 54, Loop 55, and Loop 56 into one global bound involving only
  `Real.Gamma (1/4)`, `π`, and `exp (-π)`.

## Loop 2026-07-09-57: global Gamma/exponential upper bound

Statement selected:

- `integral_Ioo_const_near_zero_bound_le_gamma_quarter`:
  the constant-multiple left near-zero integral over `(0,1)` is bounded by the Gamma expression
  from Loop 56.
- `mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound`:
  the Mellin real part at `1/4` is bounded by
  `C * ((1 / π)^(1/4) * Real.Gamma (1/4)) + C * (exp (-π) / π)`,
  where `C = 2 * (1 - exp (-π))⁻¹`.

Reason:

- Loop 52 produced a global upper bound by two simplified integrals.
- Loop 54 bounds the left simplified integral by the full standard tail.
- Loop 55 evaluates the right simplified integral.
- Loop 56 evaluates the left full standard tail in terms of `Real.Gamma (1/4)`.

Status before Lean check:

- Passed.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The left bound rewrites the constant outside the integral with `integral_const_mul`, then
  applies `mul_le_mul_of_nonneg_left` to the Loop 54 inequality composed with the Loop 56
  equality.
- The global bound follows by transitivity from
  `mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_const_exp_bounds` and `add_le_add`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin-side upper-bound route is now reduced to a purely real explicit inequality involving
  `Real.Gamma (1/4)`, `π`, and `exp (-π)`.
- This still does not prove that this explicit expression is `< 8`, so it does not yet prove the
  center-value positivity target, positivity of `liCoefficientCandidate 1`, or Li's
  criterion/RH equivalence.

Next route:

- Search mathlib for existing bounds on `Real.Gamma (1/4)` and elementary bounds for
  `(1 - exp (-π))⁻¹`, or prove a coarse bound sufficient for the explicit expression to be `< 8`.

## Loop 2026-07-09-58: coarse Gamma bound at one quarter

Statement selected:

- `Real.gamma_five_quarter_le_one`:
  `Real.Gamma (5/4) ≤ 1`.
- `Real.gamma_one_quarter_le_four`:
  `Real.Gamma (1/4) ≤ 4`.

Reason:

- Loop 57 reduced the Mellin-side bound to an expression containing `Real.Gamma (1/4)`.
- Mathlib did not expose a direct theorem named as a `Gamma(1/4)` bound.
- However `Real.convexOn_Gamma` and the endpoint values `Γ(1)=Γ(2)=1` give
  `Γ(5/4)≤1`; the Gamma functional equation then gives `Γ(1/4)≤4`.

Status before Lean check:

- Passed.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The `5/4` bound uses the Jensen inequality from `Real.convexOn_Gamma` with weights `3/4` and
  `1/4` between `1` and `2`.
- The `1/4` bound rewrites `Γ(5/4)` as `(1/4) * Γ(1/4)` using
  `Real.Gamma_add_one`, then clears the positive factor.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- A verified coarse upper bound for `Real.Gamma (1/4)` is now available.
- This still does not by itself prove the Loop 57 expression `< 8`; the remaining work is to
  combine this with bounds for `(1 / π)^(1/4)`, `(1 - exp (-π))⁻¹`, and `exp (-π)/π`.
- It also does not prove center-value positivity, positivity of `liCoefficientCandidate 1`, or
  Li's criterion/RH equivalence.

Next route:

- Prove elementary inequalities such as `(1 / π)^(1/4) ≤ 4/5`,
  `exp (-π) / π < 1/20`, and `2 * (1 - exp (-π))⁻¹ < 17/8`, or find stronger existing
  mathlib bounds that make the Loop 57 expression `< 8`.

## Loop 2026-07-09-59: coarse fourth-root bound for `1 / π`

Statement selected:

- `Real.one_div_pi_rpow_quarter_le_four_fifths`:
  `(1 / π)^(1/4) ≤ 4/5`.

Reason:

- Loop 57's explicit upper bound contains the factor `(1 / π)^(1/4)`.
- The weak lower bound `3 < π` is already in mathlib as `Real.pi_gt_three`.
- Since `(5/4)^4 < 3 < π`, this gives `1/π ≤ (4/5)^4`, hence the desired fourth-root bound.

Status before Lean check:

- Passed after normalizing the fourth power/rpow interface.

Lean result:

- Added `Real.one_div_pi_rpow_quarter_le_four_fifths` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof raises both sides to the fourth power using `Real.rpow_le_rpow_iff`, simplifies
  `((1/π)^(1/4))^4` with `Real.rpow_inv_natCast_pow`, and closes the base inequality with
  `Real.pi_gt_three`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Another factor in the Loop 57 explicit expression is now bounded by a rational number.
- Together with Loop 58, the product
  `(1 / π)^(1/4) * Real.Gamma (1/4)` can later be bounded by `16/5`.
- This still does not bound the denominator factor `2 * (1 - exp (-π))⁻¹`, the right term
  `exp (-π)/π`, or prove the target `< 8`.

Next route:

- Prove an elementary exponential bound for `exp (-π)`, likely using `Real.pi_gt_three` and
  a rational upper bound for `exp (-3)`.

## Loop 2026-07-09-60: coarse exponential bound at `-π`

Statement selected:

- `Real.rexp_neg_pi_lt_one_twentieth`:
  `rexp (-π) < 1 / 20`.

Reason:

- Loop 57's explicit Mellin upper bound contains the right-tail term `exp (-π) / π`.
- The same small exponential bound will also control the denominator factor
  `2 * (1 - exp (-π))⁻¹`.
- Mathlib already has the lower bounds `Real.pi_gt_three` and `Real.exp_one_gt_d9`, which are
  strong enough for a fully elementary estimate.

Status before Lean check:

- Passed after adjusting the rational lower bound for `exp 1`.

Lean result:

- Added `Real.rexp_neg_pi_lt_one_twentieth` to `LeanLab/Riemann/LiScaffold.lean`.
- First proved `20 < exp 3` from `exp 1 > 1359 / 500`, using
  `Real.exp_nat_mul` and `pow_lt_pow_left₀`; the weaker trial bound `27 / 10` failed because its
  cube is below `20`.
- Then rewrote `exp (-3)` as the reciprocal of `exp 3`, used
  `one_div_lt_one_div_of_lt`, and transferred from `-3` to `-π` via `Real.pi_gt_three` and
  `Real.exp_lt_exp`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- A verified elementary bound `exp (-π) < 1 / 20` is now available for the explicit Mellin-bound
  route.
- This still does not by itself prove the Loop 57 expression `< 8`; the remaining numerical work
  is to convert it into bounds for `exp (-π) / π` and `2 * (1 - exp (-π))⁻¹`, then combine those
  with Loops 58 and 59.
- It also does not prove center-value positivity, positivity of `liCoefficientCandidate 1`, or
  Li's criterion/RH equivalence.

Next route:

- Prove `exp (-π) / π < 1 / 20` or a sharper convenient variant.
- Prove a denominator-factor bound such as `2 * (1 - exp (-π))⁻¹ < 17 / 8`.
- Combine the rational bounds to push the Loop 57 expression below `8`.

## Loop 2026-07-09-61: right-tail quotient bound

Statement selected:

- `Real.rexp_neg_pi_div_pi_lt_one_twentieth`:
  `rexp (-π) / π < 1 / 20`.

Reason:

- Loop 57's explicit bound contains the right-tail term `exp (-π) / π`.
- Loop 60 already gives `exp (-π) < 1 / 20`.
- Since `π > 1` and `exp (-π) > 0`, dividing by `π` only decreases the positive numerator.

Status before Lean check:

- Passed.

Lean result:

- Added `Real.rexp_neg_pi_div_pi_lt_one_twentieth` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof first shows `exp (-π) / π < exp (-π)` using `div_lt_iff₀`, `Real.pi_pos`,
  `Real.exp_pos`, and `Real.pi_gt_three`.
- It then composes this with Loop 60's `Real.rexp_neg_pi_lt_one_twentieth`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The right-tail contribution in the Loop 57 expression now has a verified rational upper bound.
- This still does not bound the denominator factor `2 * (1 - exp (-π))⁻¹`, and so does not yet
  prove the full Loop 57 expression `< 8`.

Next route:

- Prove a denominator-factor bound such as `2 * (1 - exp (-π))⁻¹ < 17 / 8`, using Loop 60.

## Loop 2026-07-09-62: denominator-factor bound

Statement selected:

- `Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths`:
  `2 * (1 - rexp (-π))⁻¹ < 17 / 8`.

Reason:

- Loop 57's explicit Mellin upper bound has the common factor
  `2 * (1 - exp (-π))⁻¹`.
- Loop 60 gives `exp (-π) < 1 / 20`, hence `1 - exp (-π) > 19 / 20`.
- This yields the inverse bound `(1 - exp (-π))⁻¹ < 20 / 19`, so the whole factor is
  `< 40 / 19 < 17 / 8`.

Status before Lean check:

- Passed after correcting a too-strong trial target.

Lean result:

- Added `Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The initially suggested `21 / 10` target was too strong for the Loop 60 input alone, since
  `40 / 19` is slightly larger than `21 / 10`.
- The successful proof uses `one_div_lt_one_div_of_lt` to invert the lower bound
  `19 / 20 < 1 - exp (-π)`, then multiplies by `2` and finishes with the rational comparison
  `40 / 19 < 17 / 8`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- All three elementary constants needed after Loop 57 now have verified rational bounds:
  `Gamma (1/4) ≤ 4`, `(1/π)^(1/4) ≤ 4/5`, `exp(-π)/π < 1/20`, and the common denominator
  factor `< 17/8`.
- These are strong enough arithmetically to make the Loop 57 expression `< 8`; that final
  combination still has to be formalized in Lean.

Next route:

- Combine Loops 57/58/59/61/62 to prove a global bound for the Mellin real part below `8`.

## Loop 2026-07-09-63: explicit Gamma/exponential bound below eight

Statement selected:

- `mellin_gamma_exp_bound_lt_eight`:
  the explicit Loop 57 upper-bound expression
  `C * ((1/π)^(1/4) * Gamma(1/4)) + C * (exp(-π)/π)` is `< 8`, where
  `C = 2 * (1 - exp(-π))⁻¹`.

Reason:

- Loop 57 reduced the Mellin real-part target to this explicit real expression.
- Loops 58/59 give the Gamma product bound:
  `(1/π)^(1/4) * Gamma(1/4) ≤ 16/5`.
- Loop 61 gives `exp(-π)/π < 1/20`.
- Loop 62 gives the common factor `C < 17/8`.
- The resulting rational upper bound is
  `(17/8)*(16/5) + (17/8)*(1/20) = 221/32 < 8`.

Status before Lean check:

- Passed after making positivity assumptions explicit for product inequalities.

Lean result:

- Added `mellin_gamma_exp_bound_lt_eight` to `LeanLab/Riemann/LiScaffold.lean`.
- The proof introduces local abbreviations `C`, `A`, and `B`; proves `A ≤ 16/5` using
  `mul_le_mul`, `Real.one_div_pi_rpow_quarter_le_four_fifths`, and
  `Real.gamma_one_quarter_le_four`; and proves the two product bounds using `mul_lt_mul`.
- The remaining rational comparison is discharged by `norm_num`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The purely real numerical part of the Loop 57 Mellin-side upper-bound route is now verified.
- This still does not yet state the Mellin real part itself is `< 8`; that should be a short
  transitivity step from `mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound`.

Next route:

- Use Loop 57 and `mellin_gamma_exp_bound_lt_eight` to prove
  `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8`.

## Loop 2026-07-09-64: Mellin real-part bound below eight

Statement selected:

- `mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight`:
  `(mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8`.

Reason:

- Loop 38 showed that center-value positivity of the project-local `riemannXi` is equivalent to
  this Mellin-side `< 8` bound.
- Loop 57 gave a verified upper bound of the Mellin real part by the explicit Gamma/exponential
  expression.
- Loop 63 proved that explicit expression is `< 8`.

Status before Lean check:

- Passed.

Lean result:

- Added `mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight` to
  `LeanLab/Riemann/LiScaffold.lean`.
- The proof is a direct `lt_of_le_of_lt` composition of
  `mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound` and
  `mellin_gamma_exp_bound_lt_eight`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The Mellin-side target `< 8` from Loop 38 is now verified.
- This still does not prove RH or Li's criterion, but it should allow a short derivation of
  project-local center-value positivity for `riemannXi (1/2)`.

Next route:

- Apply `riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight` or the nearest
  existing equivalence theorem to derive `0 < (riemannXi (1 / 2)).re`.

## Loop 2026-07-09-65: center-value positivity

Statement selected:

- `riemannXi_half_re_pos`:
  `0 < (riemannXi (1 / 2)).re`.

Reason:

- Loop 38 established the equivalence between this center-value positivity statement and the
  Mellin-side bound `< 8`.
- Loop 64 proved the Mellin-side bound.
- This gives a concrete, function-level consequence of the long Mellin/Gamma estimate chain.

Status before Lean check:

- Passed.

Lean result:

- Added `riemannXi_half_re_pos` to `LeanLab/Riemann/LiScaffold.lean`.
- The proof applies
  `riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight.2` to
  `mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The project now has a verified positive center-value result for its local `riemannXi` scaffold.
- This is still not RH, not Li's criterion, and not a zero-location theorem; it is a reusable
  analytic positivity lemma obtained through a fully checked chain.

Next route:

- Derive a nonvanishing statement for `riemannXi (1 / 2)`, or propagate the positivity to the
  centered zero-order `iteratedDeriv` statement already present in the scaffold.

## Loop 2026-07-09-66: center value in the slit plane

Statement selected:

- `riemannXi_half_mem_slitPlane`:
  `riemannXi (1 / 2) ∈ slitPlane`.

Reason:

- Loop 65 proves the center value has strictly positive real part.
- Membership in `slitPlane` is the local condition used by mathlib's complex logarithm analytic
  interface.
- This prepares a later center-log analytic theorem without adding any unverified zero-location
  assumptions.

Status before Lean check:

- Passed.

Lean result:

- Added `riemannXi_half_mem_slitPlane` to `LeanLab/Riemann/LiScaffold.lean`.
- The proof rewrites `mem_slitPlane_iff`, selects the positive-real-part branch, and applies
  `riemannXi_half_re_pos`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The project can now use the complex logarithm of `riemannXi` at the center point through the
  standard slit-plane interface.
- This still does not assert anything about all zeros, RH, or Li's criterion.

Next route:

- Prove `AnalyticAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2)` using
  `analyticAt_riemannXi` and `riemannXi_half_mem_slitPlane`.

## Loop 2026-07-09-67: center-point logarithmic analyticity

Statement selected:

- `analyticAt_log_riemannXi_half`:
  `AnalyticAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2)`.

Reason:

- Loop 66 established the exact slit-plane condition needed by mathlib's complex-log analytic
  interface.
- This gives a local analytic interface for `log ∘ riemannXi` at the center point, parallel to
  the earlier theorem at `1`.

Status before Lean check:

- Passed.

Lean result:

- Added `analyticAt_log_riemannXi_half` to `LeanLab/Riemann/LiScaffold.lean`.
- The proof is the direct application
  `(analyticAt_riemannXi (1 / 2)).clog riemannXi_half_mem_slitPlane`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The project can now differentiate and expand `log (riemannXi s)` locally at the center through
  mathlib's analytic APIs.
- This is still local analytic scaffolding, not a zero-location result.

Next route:

- Derive `DifferentiableAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2)` or a centered-log
  evenness/derivative lemma using the new analytic-at-center result.

## Loop 2026-07-09-68: center logarithmic derivative vanishes

Statements selected:

- `differentiableAt_log_riemannXi_half`:
  `DifferentiableAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2)`.
- `hasDerivAt_log_riemannXi_half`:
  the center logarithmic derivative is `deriv riemannXi (1 / 2) / riemannXi (1 / 2)`.
- `deriv_log_riemannXi_half`:
  the corresponding `deriv` equality.
- `deriv_log_riemannXi_half_eq_zero`:
  `deriv (fun s : ℂ ↦ log (riemannXi s)) (1 / 2) = 0`.

Reason:

- Loop 67 supplies analyticity of the center logarithm.
- Earlier symmetry work already proved `deriv_riemannXi_half_eq_zero`.
- Combining these gives a checked first-order vanishing result for the center logarithm, useful for
  centered Taylor scaffolding.

Status before Lean check:

- Passed.

Lean result:

- Added all four theorems to `LeanLab/Riemann/LiScaffold.lean`.
- The derivative formula uses
  `(differentiable_riemannXi (1 / 2)).hasDerivAt.clog riemannXi_half_mem_slitPlane`.
- The zero result rewrites by `deriv_log_riemannXi_half` and `deriv_riemannXi_half_eq_zero`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The center logarithm of the local xi scaffold now has a verified vanishing first derivative.
- This is still a local analytic consequence, not RH or Li's criterion.

Next route:

- Investigate whether centered `log ∘ riemannXi` can be shown even locally/global-formally, or use
  the zero derivative as a Taylor-coefficient scaffold around the center.

## Meta 2026-07-09-review: loop and goal revision

Review source:

- `/Users/karasuakamatsu/Downloads/review_rh_loop_goal_20260709.md`.

Review conclusion absorbed:

- The verified Lean work is not being rejected: definitions, logs, build verification, and the
  recent center-value chain are structurally meaningful.
- The weakness is the reward function: too many loops optimized for "one more compiling lemma"
  rather than a named milestone.
- Coefficient-by-coefficient Li computation should not become the long-term RH route.

Protocol changes:

- Added compiled target ledger `LeanLab/Riemann/Targets.lean`.
- Added loop protocol `research/rh_loop_protocol_20260709.md`.
- Added initial blueprint `research/blueprint.md`.
- Updated `research/riemann_hypothesis_scope.md` with a three-tier goal structure.

Important adaptation:

- The target ledger does not introduce unproved Lean facts. Planned statements are stored as data
  and text only. A target becomes usable mathematics only after it points to a theorem that already
  compiles.

Revised immediate route:

- Prefer Tier 1 bridge target `T1.xi.completed.bridge`.
- If theorem names are unclear, the next admissible loop is a bounded local mathlib inventory for
  `completedRiemannZeta`, `completedRiemannZeta₀`, and their relation.

Verification plan:

- Compile `LeanLab/Riemann/Targets.lean`.
- Run full `lake build`.
- Run the project proof-placeholder keyword scan.

## Loop 2026-07-09-69: T1 xi/completed-zeta bridge

Target:

- `T1.xi.completed.bridge` from `LeanLab/Riemann/Targets.lean`.

Pre-registered statement:

- `riemannXi_eq_mul_completedRiemannZeta`:
  for `s ≠ 0` and `s ≠ 1`,
  `riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s`.

Inventory:

- Local mathlib search found
  `completedRiemannZeta_eq`:
  `completedRiemannZeta s =
    completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)`.
- This was exactly the relation needed for the bridge.

Rejected route:

- Do not try to make the theorem unconditional. At `s = 0` or `s = 1`, the factor
  `s * (s - 1)` vanishes while the project-local `riemannXi` has value `1 / 2` at the
  pole-removal points, so the bridge requires explicit edge conditions.

Lean result:

- Added `riemannXi_eq_mul_completedRiemannZeta` to `LeanLab/Riemann/LiScaffold.lean`.
- Updated `LeanLab/Riemann/Targets.lean`: `T1.xi.completed.bridge` is now `.proven` and linked to
  `riemannXi_eq_mul_completedRiemannZeta`.
- Updated `research/blueprint.md` to mark the node proved.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The local `riemannXi` definition is now formally connected to mathlib's standard
  `completedRiemannZeta` away from `0` and `1`.
- This directly addresses the first Tier 1 bridge concern from the architectural review.

Next route:

- Move to `T1.xi.zero.bridge`: formulate the exact zero correspondence carefully, likely by first
  proving a one-direction bridge from `riemannXi s = 0` with `s ≠ 0,1` to a completed-zeta zero
  statement, then relating that to `riemannZeta` under Gamma-factor nonvanishing assumptions.

## Loop 2026-07-09-70: safe forward xi-zero to zeta-zero bridge

Blueprint node:

- `T1.xi.zero.bridge.forward.safe`.

Pre-registered statement:

- `isZetaZero_of_riemannXi_eq_zero`:
  if `s ≠ 0`, `s ≠ 1`, and `riemannXi s = 0`, then `IsZetaZero s`.

Inventory:

- `riemannZeta_def_of_ne_zero`:
  `riemannZeta s = completedRiemannZeta s / Gammaℝ s` when `s ≠ 0`.
- `riemannXi_eq_mul_completedRiemannZeta` from Loop 69:
  `riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s` when `s ≠ 0,1`.
- `Gammaℝ_eq_zero_iff` exists and will matter for the reverse direction, but is not needed for
  this forward direction because a zero numerator makes the quotient zero.

Rejected route:

- Do not state the full zero equivalence yet. The reverse direction from `riemannZeta s = 0` to
  `riemannXi s = 0` must handle Gamma-factor zeros and trivial-zero cancellation, so it belongs in
  a later subnode.

Lean result:

- Added `isZetaZero_of_riemannXi_eq_zero` to `LeanLab/Riemann/LiScaffold.lean`.
- Updated `research/blueprint.md` with subnodes under `T1.xi.zero.bridge`; the forward safe
  direction is marked as proved, while the reverse and nontrivial packaging subnodes remain open.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- A project-local xi zero away from the pole-removal points now formally implies a zeta zero.
- This is a useful bridge result but not the full correspondence with nontrivial zeta zeros.

Next route:

- Inventory and prove the reverse direction under an explicit `¬ IsTrivialZeroPoint s` assumption,
  or first prove a smaller lemma converting `IsZetaZero s` and Gamma-factor nonzero into
  `completedRiemannZeta s = 0`.

## Loop 2026-07-09-71: Gamma-conditional reverse xi-zero bridge

Blueprint node:

- `T1.xi.zero.bridge.reverse.gamma`.

Pre-registered statements:

- `completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`:
  if `s ≠ 0`, `Gammaℝ s ≠ 0`, and `IsZetaZero s`, then
  `completedRiemannZeta s = 0`.
- `riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`:
  if additionally `s ≠ 1`, then `riemannXi s = 0`.

Inventory:

- `riemannZeta_def_of_ne_zero` gives
  `riemannZeta s = completedRiemannZeta s / Gammaℝ s`.
- `div_eq_zero_iff` lets the zero quotient force a zero numerator when `Gammaℝ s ≠ 0`.
- Loop 69's bridge then converts `completedRiemannZeta s = 0` to `riemannXi s = 0`.

Rejected route:

- Do not derive `Gammaℝ s ≠ 0` from `¬ IsTrivialZeroPoint s` in this loop. That requires a
  separate edge-case lemma using `Gammaℝ_eq_zero_iff`, because `Gammaℝ` also vanishes at `s = 0`.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- Updated `research/blueprint.md`: the Gamma-conditional reverse subnode is proved, while the
  nontrivial packaging subnode remains open.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The reverse xi/zeta bridge is now proved under the exact analytic nonvanishing condition needed
  for the completed-zeta quotient.
- The remaining bridge work is arithmetic/edge-case packaging: show the nontrivial-zero predicate
  rules out Gamma-factor zeros in the required situations.

Next route:

- Prove a small Gamma-edge lemma:
  `Gammaℝ s = 0 → s = 0 ∨ IsTrivialZeroPoint s`, then combine it with `IsZetaZero s` and
  `riemannZeta_zero` to rule out `s = 0`.

## Loop 2026-07-09-72: Gamma-factor edge cases for nontrivial zeros

Blueprint node:

- `T1.xi.zero.bridge.gamma.edge`.

Pre-registered statements:

- `eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero`:
  `Gammaℝ s = 0 → s = 0 ∨ IsTrivialZeroPoint s`.
- `Gammaℝ_ne_zero_of_isNontrivialZero`:
  `IsNontrivialZero s → Gammaℝ s ≠ 0`.

Inventory:

- `Gammaℝ_eq_zero_iff` gives `Gammaℝ s = 0 ↔ ∃ n, s = -(2*n)`.
- The `n = 0` case is `s = 0`.
- The `n + 1` case is exactly the project trivial-zero shape `s = -2*(n+1)`.
- `riemannZeta_zero` gives `ζ(0) = -1/2`, so `s = 0` cannot satisfy `IsZetaZero`.

Rejected route:

- Do not fold this directly into the reverse bridge proof. Keeping the Gamma edge lemma separate
  makes the dependency on trivial-zero conventions explicit and reusable.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- Updated `research/blueprint.md`; the Gamma edge subnode is proved.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The nontrivial-zero predicate now formally rules out Gamma-factor zeros.
- Together with Loop 71, this should allow a short reverse bridge:
  `IsNontrivialZero s → riemannXi s = 0`.

Next route:

- Package the reverse nontrivial direction, then combine with Loop 70 for the full zero bridge.

## Loop 2026-07-09-73: reverse bridge for nontrivial zeta zeros

Blueprint node:

- `T1.xi.zero.bridge.reverse.nontrivial`.

Pre-registered statements:

- `ne_zero_of_isNontrivialZero`:
  `IsNontrivialZero s → s ≠ 0`.
- `riemannXi_eq_zero_of_isNontrivialZero`:
  `IsNontrivialZero s → riemannXi s = 0`.

Reason:

- Loop 71 proved the reverse bridge under `s ≠ 0`, `s ≠ 1`, and `Gammaℝ s ≠ 0`.
- Loop 72 proved that `IsNontrivialZero s` supplies the Gamma nonvanishing.
- The only remaining local edge condition is `s ≠ 0`, ruled out by `riemannZeta_zero`.

Rejected route:

- Do not declare the entire zero bridge target solved yet. The final packaged theorem should state
  a clean equivalence or pair of implications with all nontriviality assumptions visible.

Lean result:

- Added both theorems to `LeanLab/Riemann/LiScaffold.lean`.
- Updated `research/blueprint.md`; reverse nontrivial subnode is proved.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed with no warnings.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- Every project nontrivial zeta zero now formally gives a zero of the local `riemannXi`.
- Together with Loop 70, the ingredients for a clean zero bridge theorem are now present.

Next route:

- Package the bridge as an iff or pair of directional theorems, then update
  `T1.xi.zero.bridge` in `Targets.lean`.

## Loop 2026-07-09-74: packaged xi/nontrivial-zero bridge

Blueprint node:

- `T1.xi.zero.bridge.nontrivial`.

Pre-registered statement:

- `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`:
  `IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬ IsTrivialZeroPoint s`.

Reason:

- Loop 70 gives the safe forward direction from a xi zero to a zeta zero under `s ≠ 0,1`.
- Loop 73 gives the reverse direction from project nontrivial zeta zeros to xi zeros.
- The final theorem must keep `¬ IsTrivialZeroPoint s` explicit on the xi-zero side; xi zeros
  alone are not recorded as enough structure for `IsNontrivialZero`.

Inventory:

- `riemannXi 0 = 1 / 2` and `riemannXi 1 = 1 / 2` are both direct `norm_num` consequences of
  the project definition.
- These endpoint value lemmas discharge the `s ≠ 0` and `s ≠ 1` side conditions needed by
  `isZetaZero_of_riemannXi_eq_zero`.

Rejected route:

- Do not state an unconditional equivalence between `IsNontrivialZero s` and `riemannXi s = 0`.
  The project bridge intentionally packages the trivial-zero exclusion as visible data.

Lean result:

- Added `riemannXi_zero`, `riemannXi_zero_ne_zero`, `riemannXi_one`,
  `riemannXi_one_ne_zero`, and
  `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial` to
  `LeanLab/Riemann/LiScaffold.lean`.
- Updated `LeanLab/Riemann/Targets.lean`: `T1.xi.zero.bridge` is now linked to the compiled
  theorem and marked proved.
- Updated `research/blueprint.md` and `research/rh_loop_protocol_20260709.md`; the next Tier 1
  loop should be a bounded inventory for `T1.li1.positivity`, unless the result note is chosen
  first.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The project-local `riemannXi` now has a compiled bridge to the project predicate
  `IsNontrivialZero`:
  `IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬ IsTrivialZeroPoint s`.
- This closes the Tier 1 xi-zero bridge target without claiming any Li criterion or RH result.

Next route:

- Run the bounded inventory for `T1.li1.positivity`: search existing support for
  `deriv completedRiemannZeta₀ 0`, special values, and real-part estimates before attempting
  another numerical proof chain.

## Loop 2026-07-09-75: bounded inventory and derivative-bound reduction for the second Li candidate

Blueprint node:

- `T1.li1.positivity`.

Pre-registered inventory question:

- Does mathlib or the existing local scaffold already contain a usable special value or estimate
  for `(deriv completedRiemannZeta₀ 0).re`?

Pre-registered Lean statements:

- `liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt`:
  reduce `0 < (liCoefficientCandidate 1).re` to a single upper bound for
  `(deriv completedRiemannZeta₀ 0).re`.
- `liCoefficientCandidate_zero_re_lt_four` and
  `liCoefficientCandidate_zero_re_mul_four_sub_pos`: show the upper-bound threshold has a positive
  product term.

Inventory:

- mathlib has `completedRiemannZeta₀_one`, `completedRiemannZeta₀_zero`,
  `completedRiemannZeta₀_one_sub`, and `deriv_riemannZeta_zero`.
- Local scaffold already has
  `liCoefficientCandidate_one_re_pos_iff_re_formula`.
- Search did not find a direct theorem for `deriv completedRiemannZeta₀ 0`, its real part, or a
  Laurent/Taylor coefficient for `completedRiemannZeta₀` at `0`.
- The proof of mathlib's `deriv_riemannZeta_zero` differentiates
  `(s * completedRiemannZeta₀ s - 1) - s / (1 - s)` at `0`; the derivative of
  `completedRiemannZeta₀` is multiplied by `s`, so it disappears at this order.

Rejected route:

- Do not try to extract `(deriv completedRiemannZeta₀ 0).re` from `ζ'(0)`. The existing proof and
  the local Loop 24 calculation show that this first-order route structurally cannot expose the
  needed derivative.

Lean result:

- Added `liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt` to
  `LeanLab/Riemann/LiScaffold.lean`:
  `0 < (liCoefficientCandidate 1).re` iff
  `(deriv completedRiemannZeta₀ 0).re <
    ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) / 2`.
- Added `liCoefficientCandidate_zero_re_lt_four`.
- Added `liCoefficientCandidate_zero_re_mul_four_sub_pos`.
- Updated `LeanLab/Riemann/Targets.lean`: `T1.li1.positivity` is now marked in progress, not
  proved.
- Updated `research/blueprint.md` with inventory findings and the new subnodes.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The second Li candidate positivity target is now reduced to a single sharp derivative upper
  bound, and the threshold on the right is formally positive.
- No RH, Li criterion, or zero-location theorem is proved by this reduction.

Next route:

- Choose a route for `(deriv completedRiemannZeta₀ 0).re`: either derive a Mellin-side structural
  formula for this derivative or record a precise second-order/Laurent infrastructure gap.

## Loop 2026-07-09-76: move the second Li derivative target to the WeakFEPair Mellin layer

Blueprint node:

- `T1.li1.mellin.deriv.reduction`.

Pre-registered statement:

- Express `deriv completedRiemannZeta₀ 0` through the underlying
  `(hurwitzEvenFEPair 0).Λ₀` derivative, using the mathlib definition
  `completedRiemannZeta₀ s = ((hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2`.

Inventory:

- `completedRiemannZeta₀` unfolds to `completedHurwitzZetaEven₀ 0`.
- `completedHurwitzZetaEven₀ a s` unfolds to `((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2`.
- `WeakFEPair.Λ₀` is definitionally `mellin P.f_modif`.
- mathlib already proves `(hurwitzEvenFEPair 0).differentiable_Λ₀`, enough for a chain-rule
  reduction.

Rejected route:

- Do not attempt the full differentiating-under-the-integral formula in this loop. The minimal
  useful step is first to move the target from `completedRiemannZeta₀` syntax to the `WeakFEPair`
  `Λ₀` layer, where the Mellin definition is exposed.

Lean result:

- Added `deriv_completedRiemannZeta₀_zero_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero`:
  `deriv completedRiemannZeta₀ 0 = deriv (hurwitzEvenFEPair 0).Λ₀ 0 / 4`.
- Added `deriv_completedRiemannZeta₀_zero_re_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero_re`.
- Added `liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt`:
  `0 < (liCoefficientCandidate 1).re` iff
  `(deriv (hurwitzEvenFEPair 0).Λ₀ 0).re <
    2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`.
- Updated `Targets.lean` and `research/blueprint.md`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining `T1.li1.positivity` estimate has moved from a completed-zeta derivative to the
  Mellin-transform layer. Since `WeakFEPair.Λ₀ = mellin f_modif`, the next mathematical problem is
  now an integral/derivative estimate for `(hurwitzEvenFEPair 0).f_modif`.
- This is still only a reduction; no positivity of `liCoefficientCandidate 1`, Li criterion, or RH
  result has been proved.

Next route:

- Inventory mathlib support for differentiating Mellin transforms at `s = 0`, especially formulas
  of the shape `deriv (mellin f) s = ∫ x in Ioi 0, log x * x^(s-1) * f x`.

## Loop 2026-07-09-77: apply the Mellin derivative theorem to the modified theta kernel

Blueprint nodes:

- `T1.li1.mellin.log.deriv`.
- `T1.li1.mellin.log.bound.reduction`.

Pre-registered inventory question:

- Does mathlib already provide a theorem differentiating `mellin f` under Big-O hypotheses?

Pre-registered Lean statements:

- `mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero`:
  the log-weighted Mellin transform of `(hurwitzEvenFEPair 0).f_modif` converges at `0`, and it is
  the derivative of `mellin (hurwitzEvenFEPair 0).f_modif` at `0`.
- `deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero`:
  rewrite the `Λ₀` derivative as that log-weighted Mellin transform.
- `liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`:
  rewrite the second Li candidate positivity target as a single real upper bound for that
  log-weighted Mellin transform.

Inventory:

- mathlib has `mellin_hasDerivAt_of_isBigO_rpow`:
  under local integrability and two-sided Big-O strip hypotheses, it proves both convergence of
  `fun t => Real.log t • f t` and
  `HasDerivAt (mellin f) (mellin (fun t => Real.log t • f t) s) s`.
- `WeakFEPair.toStrongFEPair` supplies the needed `f_modif` asymptotics:
  `hf_top'` at infinity and `hf_zero'` near zero for arbitrary powers.

Rejected route:

- No need to build a new differentiating-under-the-integral theorem locally. The existing mathlib
  Mellin theorem is exactly the required infrastructure for this step.

Lean result:

- Added `mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero`.
- Added `deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero`.
- Added `liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`:
  `0 < (liCoefficientCandidate 1).re` iff
  `(mellin (fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re <
    2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`.
- Updated `Targets.lean` and `research/blueprint.md`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining `T1.li1.positivity` target is now an explicit upper-bound problem for a
  log-weighted Mellin integral of the modified theta kernel.
- This is still a reduction; no positivity of `liCoefficientCandidate 1`, Li criterion, or RH
  result has been proved.

Next route:

- Split the log-weighted Mellin integral over `(0,1)` and `(1,∞)`, unfold
  `(hurwitzEvenFEPair 0).f_modif` on each interval, and look for a comparison bound.

## Loop 2026-07-09-78: split the log-weighted Mellin integral at one

Blueprint node:

- `T1.li1.mellin.log.integral.split`.

Pre-registered Lean statements:

- `ofReal_cpow_zero_sub_one`:
  simplify `(x : ℂ) ^ ((0 : ℂ) - 1)` on `0 < x` to the real power `x ^ (-1)`.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq`:
  rewrite the raw log-weighted Mellin integrand's real part as
  `x ^ (-1) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re`.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real`:
  split the real part of the log-weighted Mellin integral into its `(0,1)` and `(1,∞)`
  contributions with that real integrand.

Rejected route:

- Do not try to prove the upper bound in the same loop. The sign of `Real.log x` changes at `1`,
  so the split and real-integrand normalization should be a separate checked node before any
  comparison estimate is attempted.

Lean result:

- Added `ofReal_cpow_zero_sub_one`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real`:
  the remaining Mellin term is the sum of the `(0,1)` and `(1,∞)` integrals of
  `x ^ (-1) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining `T1.li1.positivity` bound is now in a split real-integral form.
- This is still not a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Use the existing interval formulas for `(hurwitzEvenFEPair 0).f_modif` and the signs
  `Real.log x < 0` on `(0,1)`, `0 < Real.log x` on `(1,∞)` to search for a safe comparison bound.

## Loop 2026-07-09-79: discard the nonpositive small-side log contribution

Blueprint node:

- `T1.li1.mellin.log.left.nonpos`.

Pre-registered Lean statements:

- `mellin_log_integral_Ioo_zero_one_nonpos`:
  the `(0,1)` contribution in the split log-weighted Mellin integral is nonpositive.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one`:
  the whole log-weighted Mellin real part is bounded above by just the `(1,∞)` contribution.

Reason:

- On `(0,1)`, `x ^ (-1) ≥ 0`, `Real.log x ≤ 0`, and
  `((hurwitzEvenFEPair 0).f_modif x).re ≥ 0`.
- This sign pattern means the small-side integral cannot hurt the desired upper bound. It is
  better to eliminate it before attempting any numerical comparison on the large side.

Rejected route:

- Do not use absolute values on the small interval. That would throw away the helpful negative
  sign of `Real.log x` and likely recreate the long center-value majorant chain.

Lean result:

- Added `mellin_log_integral_Ioo_zero_one_nonpos`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one`:
  `(mellin (fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re` is at most
  `∫ x in Ioi 1, x ^ (-1) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining `T1.li1.positivity` upper-bound problem has been reduced to estimating only the
  large-side `(1,∞)` log-weighted theta-tail contribution.
- This is not yet a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Use `hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt` to bound the right-side integrand,
  then investigate integrability and explicit bounds for
  `x ^ (-1) * Real.log x * 2 * (exp (-π*x) / (1 - exp (-π*x)))`.

## Loop 2026-07-09-80: compare the right-side log integrand to an exponential tail

Blueprint node:

- `T1.li1.mellin.log.right.exp_tail`.

Pre-registered Lean statements:

- `mellin_log_right_integrand_re_le_exp_tail_of_one_lt`:
  for `1 < x`, bound the right-side log-weighted integrand by the existing exponential theta-tail
  majorant.
- `mellin_log_integral_Ioi_one_le_exp_tail`:
  assuming that majorant is integrable on `Ioi 1`, lift the pointwise comparison to the right-side
  integral.

Reason:

- Loop 79 reduced the remaining upper-bound problem to the `(1,∞)` integral.
- On this interval, `x ^ (-1) ≥ 0` and `Real.log x ≥ 0`, so multiplying the existing theorem
  `hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt` preserves the inequality.

Rejected route:

- Do not try to evaluate the log-weighted majorant integral in this same loop. First expose the
  exact majorant and the needed integrability hypothesis, matching the earlier center-value
  majorant pattern.

Lean result:

- Added `mellin_log_right_integrand_re_le_exp_tail_of_one_lt`.
- Added `mellin_log_integral_Ioi_one_le_exp_tail`:
  if `x ^ (-1) * Real.log x * (2 * (exp (-π*x) / (1 - exp (-π*x))))` is integrable on `Ioi 1`,
  then the right-side theta-kernel integral is bounded by the corresponding majorant integral.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project proof-gap keyword scan passed with no matches.

Conclusion:

- The remaining `T1.li1.positivity` estimate is now reduced to a log-weighted exponential-tail
  majorant integral on `(1,∞)`, plus its integrability.
- This is not yet a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Prove integrability of the log-weighted right-tail majorant, likely by bounding
  `Real.log x / x` on `x ≥ 1` with a mild power such as `x^(1/4)` or by reusing an existing
  exponential-decay theorem with polynomial/log factors.

## Loop 2026-07-09-81: prove integrability of the log-weighted right-tail majorant

Blueprint node:

- `T1.li1.mellin.log.right.exp_tail.integrable`.

Pre-registered Lean statements:

- `mellin_log_right_exp_tail_le_const_mul_rexp`:
  for `1 ≤ x`, dominate the log-weighted exponential majorant by a constant multiple of
  `exp (-π*x)`.
- `integrableOn_mellin_log_right_exp_tail`:
  prove that the log-weighted exponential majorant is integrable on `Ioi 1`.

Reason:

- Loop 80 left exactly one hypothesis before the right-side integral comparison could become
  unconditional: integrability of
  `x ^ (-1) * Real.log x * (2 * (exp (-π*x) / (1 - exp (-π*x))))`.
- On `x ≥ 1`, `Real.log x ≤ x`, so `x ^ (-1) * Real.log x ≤ 1`; the previous denominator bound
  then reduces the tail to a constant multiple of `exp (-π*x)`, matching the existing
  exponential-decay integrability theorem.

Rejected route:

- Do not compute or numerically bound the majorant integral in this loop. First discharge the
  integrability hypothesis exposed by Loop 80, then use a separate loop for the explicit integral
  estimate.

Lean result:

- Added `mellin_log_right_exp_tail_le_const_mul_rexp`.
- Added `integrableOn_mellin_log_right_exp_tail`, using continuity on `Ici 1`, the new constant
  multiple comparison, and `integrable_of_isBigO_exp_neg`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The Loop 80 right-side comparison can now be made unconditional by instantiating its
  integrability hypothesis.
- This is still not a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Instantiate `mellin_log_integral_Ioi_one_le_exp_tail` with
  `integrableOn_mellin_log_right_exp_tail`, then compare the resulting majorant integral with the
  already available constant-multiple exponential integral formula.

## Loop 2026-07-09-82: close the right-tail integral bound

Blueprint node:

- `T1.li1.mellin.log.right.exp_tail.closed_bound`.

Pre-registered Lean statements:

- `mellin_log_integral_Ioi_one_le_integral_exp_tail`:
  instantiate the Loop 80 conditional right-side comparison with Loop 81 integrability.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail`:
  compose the nonpositive left-side reduction with the right-side majorant comparison.
- `mellin_log_right_exp_tail_integral_le_const_integral_rexp`:
  compare the log-weighted exponential majorant integral with a constant multiple of
  `exp (-π*x)`.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound`:
  use the existing closed-form integral theorem for the constant exponential tail.

Reason:

- After Loop 81, the remaining hypothesis in `mellin_log_integral_Ioi_one_le_exp_tail` is available
  as a theorem. Instantiating it avoids carrying a removable assumption into the next numerical
  comparison.
- The previous pointwise bound
  `mellin_log_right_exp_tail_le_const_mul_rexp` matches the existing theorem
  `integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq`, so this loop can close the integral expression
  without new analytic infrastructure.

Rejected route:

- Do not attempt the final Li-candidate positivity comparison in this loop. That comparison needs
  a separate lower bound for `2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`,
  while this loop only closes the upper-bound side.

Lean result:

- Added `mellin_log_integral_Ioi_one_le_integral_exp_tail`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail`.
- Added `mellin_log_right_exp_tail_integral_le_const_integral_rexp`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_const_exp`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound`:
  `(mellin (fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re` is at most
  `(2 * (1 - exp (-π))⁻¹) * (exp (-π) / π)`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The log-weighted Mellin upper-bound side for `T1.li1.positivity` now has a compact explicit
  constant bound.
- This is still not a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Derive a rational upper bound for
  `(2 * (1 - exp (-π))⁻¹) * (exp (-π) / π)` from Loops 61-62, then seek a rational lower bound for
  `2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`.

## Loop 2026-07-09-83: rationalize the log-Mellin upper bound

Blueprint node:

- `T1.li1.mellin.log.right.exp_tail.rational_bound`.

Pre-registered Lean statements:

- `mellin_log_const_exp_bound_lt_seventeen_over_one_sixty`:
  prove `(2 * (1 - exp (-π))⁻¹) * (exp (-π) / π) < 17 / 160`.
- `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`:
  compose Loop 82's explicit constant bound with that rational estimate.

Reason:

- Loop 82 reduced the analytic upper-bound side to a compact explicit constant. Loops 61 and 62
  already provide exactly the two numerical estimates needed to bound that constant by
  `(17/8)*(1/20)`.
- A rational bound is easier to compare against a future rational lower bound for the Li-side
  threshold.

Rejected route:

- Do not try to prove the Li-side threshold lower bound in this same loop. It depends on a
  different quantity, `(liCoefficientCandidate 0).re`, and should be isolated so any gap is easier
  to diagnose.

Lean result:

- Added `mellin_log_const_exp_bound_lt_seventeen_over_one_sixty`.
- Added `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`:
  `(mellin (fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re < 17 / 160`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The remaining Mellin upper-bound side for `T1.li1.positivity` is now a small rational inequality.
- This is still not a proof of `0 < (liCoefficientCandidate 1).re`, nor any Li criterion or RH
  result.

Next route:

- Prove `17 / 160 < 2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`,
  likely by deriving coarse rational bounds for `(liCoefficientCandidate 0).re`.

## Loop 2026-07-09-84: close the second local Li-candidate positivity target

Blueprint nodes:

- `T1.li1.threshold.rational_lower`.
- `T1.li1.positivity`.

Pre-registered Lean statements:

- `Real.eulerMascheroniConstant_gt_571_over_1000`:
  prove a coarse lower bound for `γ` using `eulerMascheroniSeq 99`.
- `Real.log_four_mul_pi_lt_2533_over_1000`:
  prove a coarse upper bound for `log (4π)` from decimal bounds for `log 2`, `log 3`, and the
  existing decimal upper bound for `π`.
- `liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty` and
  `liCoefficientCandidate_zero_re_lt_one`:
  isolate the coarse interval for `(liCoefficientCandidate 0).re`.
- `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`:
  prove `17 / 160 < 2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`.
- `liCoefficientCandidate_one_re_pos`:
  close the target `0 < (liCoefficientCandidate 1).re`.

Reason:

- Loop 83 reduced the Mellin side to `< 17/160`.
- It remains to show that `17/160` is below the Li-side threshold. A robust way is to prove the
  coarse interval `17/960 < (liCoefficientCandidate 0).re < 1`, which is numerically weak but
  enough for the threshold comparison.

Rejected route:

- Do not rely on floating-point evaluation of `λ₀`. The proof instead uses rational decimal
  bounds already available in mathlib and the exact definition of `liCoefficientCandidate 0`.

Lean result:

- Added `Real.eulerMascheroniConstant_gt_571_over_1000`.
- Added `Real.log_four_mul_pi_lt_2533_over_1000`.
- Added `liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty`.
- Added `liCoefficientCandidate_zero_re_lt_one`.
- Added `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`.
- Added `liCoefficientCandidate_one_re_pos`, proving `0 < (liCoefficientCandidate 1).re`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T1.li1.positivity` as `.proven`.
- `lake env lean LeanLab/Riemann/LiScaffold.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- Tier 1 target `T1.li1.positivity` is closed for the project-local second Li candidate.
- This is not a Li criterion formalization, not a proof of RH, and not a statement about all Li
  coefficients.

Next route:

- Write `T1.note.li.scaffold`, making the verified xi bridge, local zero bridge, and first two
  local Li-candidate positivity results readable, while clearly stating the remaining global RH
  gap.

## Loop 2026-07-09-85: write the Tier 1 xi/Li scaffold note

Blueprint node:

- `T1.note.li.scaffold`.

Pre-registered artifact:

- `research/li_scaffold_note_20260709.md`:
  a concise result note listing only compiled theorem names for the local xi bridge, zero bridge,
  center scaffold, and first two local Li-candidate positivity results.

Reason:

- The architectural review asked for a readable Tier 1 deliverable rather than immediately starting
  another coefficient-by-coefficient numerical chain.
- After Loop 84, all Tier 1 proof targets in the ledger are closed, so the next useful step is to
  summarize exactly what has been verified and where the global RH gap remains.

Rejected route:

- Do not start a third local Li-candidate computation in this loop. The review explicitly warned
  that computing coefficients one by one is not a structural route to RH.

Result:

- Added `research/li_scaffold_note_20260709.md`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T1.note.li.scaffold` as `.proven` as a
  documentation target.
- Updated `research/blueprint.md` and `research/rh_loop_protocol_20260709.md` so the next loop is
  Tier 2 inventory rather than more Tier 1 coefficient work.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- Tier 1 now has a readable scaffold note tied to compiled theorem names.
- The note explicitly does not claim a Li criterion formalization, all-coefficients positivity, or
  RH.

Next route:

- Perform bounded Tier 2 inventory for `T2.inventory.li.hadamard`, then compare with the
  Nyman-Beurling/Báez-Duarte route before choosing `T2.pivot`.

## Loop 2026-07-09-86: inventory the Li/Hadamard Tier 2 route

Blueprint node:

- `T2.inventory.li.hadamard`.

Pre-registered inventory question:

- Does mathlib currently have enough entire-function, zero-multiset, Hadamard-product, and
  log-derivative infrastructure to state a useful Li-criterion direction?

Reason:

- The review asked for a Tier 2 structural choice before starting another long proof chain.
- The Li/Hadamard route is the closest continuation of the local xi and Li-candidate scaffold, but
  it depends on global product and zero-counting infrastructure that should be checked first.

Search result:

- Useful support was found for local analyticity, isolated zeros, meromorphic divisors, local
  canonical decomposition on balls, Jensen/log-counting, zeta-zero sets, completed zeta, and
  logarithmic derivatives.
- No direct Li-criterion theorem was found.
- `Analysis/Complex/Hadamard.lean` is a three-lines theorem file, not a global product theorem.
- No ready global xi Hadamard product, zero enumeration with multiplicity, or coefficient-to-zero
  sum bridge was found.

Rejected route:

- Do not start a direct Li/Hadamard proof chain yet. The current library support would first require
  building global entire packaging, local xi divisors on balls, support-to-nontrivial-zero bridges,
  and zero-counting statements.

Result:

- Added `research/tier2_li_hadamard_inventory_20260709.md`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.inventory.li.hadamard` as `.proven` as an
  inventory target.
- Updated `research/blueprint.md` and `research/rh_loop_protocol_20260709.md` to route the next
  loop to `T2.inventory.nyman.beurling`.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- Li/Hadamard remains a plausible long-run structural route, but it is not the immediate Tier 2
  choice until the missing global bridges are built.

Next route:

- Perform bounded inventory for `T2.inventory.nyman.beurling`, then choose `T2.pivot`.

## Loop 2026-07-09-87: inventory the Nyman-Beurling Tier 2 route

Blueprint node:

- `T2.inventory.nyman.beurling`.

Pre-registered inventory question:

- Does mathlib currently have enough `L2`, closure/density, step-function, and fractional-part
  infrastructure to state a useful Nyman-Beurling or Baez-Duarte route?

Reason:

- Loop 86 showed that Li/Hadamard would first require global product and zero-enumeration bridges.
- The alternative structural route should be checked before choosing `T2.pivot`.

Search result:

- Useful support was found for `Lp E p μ`, `L2.innerProductSpace`, `indicatorConstLp`,
  `Lp.simpleFunc.denseRange`, continuous functions dense in `Lp`, finite interval measures,
  `Int.fract`, `Measurable.fract`, and Hilbert-subspace closure/orthogonality criteria.
- No direct Nyman-Beurling or Baez-Duarte criterion statement was found.
- No project-local fractional-part basis functions, span submodule, or density-to-RH bridge exists
  yet.

Rejected route:

- Do not attempt to state the full Nyman-Beurling criterion immediately. First build one local
  fractional-part basis function as an `L2` element and prove its boundedness and measurability.
- Do not use the Baez-Duarte arithmetic sequence route as the first formal target; it appears to
  need more number-theoretic and asymptotic scaffolding than the Hilbert-space foundation.

Result:

- Added `research/tier2_nyman_beurling_inventory_20260709.md`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.inventory.nyman.beurling` as `.proven` as an
  inventory target.
- Updated `research/blueprint.md` and `research/rh_loop_protocol_20260709.md` to route the next
  loop to `T2.pivot`.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- Nyman-Beurling is the better immediate Tier 2 route, not because the criterion is already
  formalized, but because the first missing nodes are small Lean-sized `L2` and measurability
  lemmas.

Next route:

- Close `T2.pivot` by choosing the Nyman-Beurling foundation route.

## Loop 2026-07-09-88: pivot to Nyman-Beurling and prove the first L2 kernel node

Blueprint nodes:

- `T2.pivot`.
- `T2.nyman.kernel.l2`.

Pre-registered Lean statement:

- For every real `a`, the function `x ↦ Int.fract (a / x)` belongs to `L2` on
  `volume.restrict (Set.Ioo 0 1)`.

Reason:

- Loop 86 showed that the Li/Hadamard route first needs global product and zero-enumeration
  bridges.
- Loop 87 showed that the Nyman-Beurling route has small first missing nodes around measurable,
  bounded fractional-part kernels in `L2`.

Search result:

- `MemLp.of_bound` applies on finite-measure spaces after proving `AEStronglyMeasurable` and an
  almost-everywhere norm bound.
- `Measurable.fract`, `Measurable.div`, `Int.fract_nonneg`, and `Int.fract_lt_one` are enough for
  the measurability and bound.
- `volume.restrict (Set.Ioo 0 1)` has the needed finite-measure instance.

Rejected route:

- Do not state the Nyman-Beurling criterion or density-to-RH bridge yet.
- Do not switch to the Baez-Duarte arithmetic strengthening before the Hilbert-space foundation is
  in place.

Result:

- Added `LeanLab/Riemann/NymanBeurling.lean`.
- Added `fractionalPartKernel`, `measurable_fractionalPartKernel`,
  `fractionalPartKernel_nonneg`, `fractionalPartKernel_lt_one`,
  `norm_fractionalPartKernel_le_one`, `fractionalPartKernel_memLp_unitInterval`,
  `fractionalPartKernel_memLp_two_unitInterval`, `fractionalPartKernelL2`, and
  `fractionalPartKernelL2_coeFn`.
- Updated `LeanLab.lean` to import the new module.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.pivot` and `T2.nyman.kernel.l2` as
  `.proven`, and to add planned target `T2.nyman.span.scaffold`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The current proof route is now a Hilbert-space foundation for Nyman-Beurling: first kernels in
  `L2`, then their span, then closure/density formulations. No density criterion or RH implication
  has been claimed.

Next route:

- Fill `T2.nyman.span.scaffold`: define the real submodule generated by `fractionalPartKernelL2`
  and prove every packaged kernel lies in it.

## Loop 2026-07-09-89: define the Nyman-Beurling kernel span

Blueprint node:

- `T2.nyman.span.scaffold`.

Pre-registered Lean statement:

- Define the real submodule of `L2(0,1)` generated by the packaged fractional-part kernels, and
  prove `fractionalPartKernelL2 a` belongs to it for every real `a`.

Reason:

- Loop 88 produced individual `L2` kernels.
- The next Nyman-Beurling foundation object must be a linear span before any closure or density
  formulation can be stated.

Search result:

- `Submodule.span ℝ (Set.range fractionalPartKernelL2)` directly defines the desired real
  submodule.
- `Submodule.subset_span` proves generator membership.
- `Submodule.span_le` gives the useful minimality theorem for later closure or density work.

Rejected route:

- Do not define the topological closure in the same proof node before the basic span object is
  logged and ledgered.
- Do not state a density predicate or Nyman-Beurling criterion yet.

Result:

- Added `unitIntervalL2` as the local name for `L2(0,1)`.
- Added `nymanBeurlingKernelSpan`.
- Proved `fractionalPartKernelL2_mem_nymanBeurlingKernelSpan`.
- Proved `range_fractionalPartKernelL2_subset_nymanBeurlingKernelSpan`.
- Proved `nymanBeurlingKernelSpan_le`, the span minimality theorem.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.span.scaffold` as `.proven` and add
  planned target `T2.nyman.closure.scaffold`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The current Nyman-Beurling route now has a compiled `L2` kernel family and its generated real
  submodule. No closure, density, criterion, or RH implication has been claimed.

Next route:

- Fill `T2.nyman.closure.scaffold`: define the topological closure of
  `nymanBeurlingKernelSpan` and prove span-to-closure inclusion.

## Loop 2026-07-09-90: define the Nyman-Beurling kernel-span closure

Blueprint node:

- `T2.nyman.closure.scaffold`.

Pre-registered Lean statement:

- Define the topological closure of `nymanBeurlingKernelSpan` inside `L2(0,1)` and prove
  `nymanBeurlingKernelSpan ≤ nymanBeurlingKernelClosure`.

Reason:

- Loop 89 produced the linear span of the packaged kernels.
- A Nyman-Beurling-style density formulation needs a closure object before any density predicate
  or criterion bridge can be stated.

Search result:

- `Submodule.topologicalClosure` directly gives a submodule closure.
- `Submodule.le_topologicalClosure` proves the span-to-closure inclusion.
- `Submodule.isClosed_topologicalClosure` and `Submodule.topologicalClosure_coe` provide useful
  bookkeeping theorems for later density work.

Rejected route:

- Do not define or claim a density theorem in the same node.
- Do not connect the density side to `RiemannHypothesis` before the Hilbert-space predicate is
  explicitly packaged.

Result:

- Added `nymanBeurlingKernelClosure`.
- Proved `nymanBeurlingKernelSpan_le_closure`.
- Proved `isClosed_nymanBeurlingKernelClosure`.
- Proved `nymanBeurlingKernelClosure_coe`.
- Proved `fractionalPartKernelL2_mem_nymanBeurlingKernelClosure`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.closure.scaffold` as `.proven` and add
  planned target `T2.nyman.density.predicate`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The current Nyman-Beurling route now has a compiled kernel family, its real span, and the
  topological closure of that span. No density, criterion, or RH implication has been claimed.

Next route:

- Fill `T2.nyman.density.predicate`: package the Hilbert-space density statement and prove its
  equivalence with `nymanBeurlingKernelClosure = ⊤`.

## Loop 2026-07-09-91: package the Nyman-Beurling density predicate

Blueprint node:

- `T2.nyman.density.predicate`.

Pre-registered Lean statement:

- Define the project-local Hilbert-space density predicate for `nymanBeurlingKernelSpan` and prove
  it is equivalent to `nymanBeurlingKernelClosure = ⊤`.

Reason:

- Loop 90 produced the topological closure object.
- A future Nyman-Beurling criterion bridge needs a named density proposition, but this loop should
  only package the Hilbert-space side.

Search result:

- `Submodule.dense_iff_topologicalClosure_eq_top` directly proves the equivalence between
  `Dense (nymanBeurlingKernelSpan : Set unitIntervalL2)` and topological closure equal to `⊤`.
- `nymanBeurlingKernelClosure_coe` gives the pointwise closure formulation.

Rejected route:

- Do not assert the density predicate itself.
- Do not connect the predicate to `RiemannHypothesis` or to a Nyman-Beurling criterion statement in
  this loop.

Result:

- Added `nymanBeurlingKernelDense`.
- Proved `nymanBeurlingKernelDense_iff_closure_eq_top`.
- Proved `nymanBeurlingKernelDense_iff_forall_mem_closure`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.density.predicate` as `.proven` and add
  planned target `T2.nyman.orthogonal.reformulation`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The current Nyman-Beurling route now has a named, compiled Hilbert-space density predicate. The
  predicate is not assumed true and is not connected to RH in this loop.

Next route:

- Fill `T2.nyman.orthogonal.reformulation`: prove the density predicate is equivalent to the
  orthogonal complement of the kernel span being bottom.

## Loop 2026-07-09-92: reformulate Nyman-Beurling density by orthogonal complement

Blueprint node:

- `T2.nyman.orthogonal.reformulation`.

Pre-registered Lean statement:

- Prove `nymanBeurlingKernelDense ↔ nymanBeurlingKernelSpanᗮ = ⊥`.

Reason:

- Loop 91 packaged density as a named Hilbert-space predicate and related it to
  `nymanBeurlingKernelClosure = ⊤`.
- In a Hilbert-space route, a dense span can be studied by showing there is no nonzero vector
  orthogonal to every generator. This is a natural next reduction before any analytic criterion
  bridge.

Search result:

- mathlib provides `Submodule.topologicalClosure_eq_top_iff`, exactly matching the needed
  closure-top to orthogonal-bottom conversion.

Rejected route:

- Do not assert `nymanBeurlingKernelDense`.
- Do not connect the density predicate to `RiemannHypothesis` or to a Nyman-Beurling criterion in
  this loop.

Result:

- Proved `nymanBeurlingKernelDense_iff_orthogonal_eq_bot`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.orthogonal.reformulation` as `.proven`
  and add planned target `T2.nyman.orthogonal.pointwise`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The current Nyman-Beurling route has reached the standard Hilbert-space obstruction form:
  density is equivalent to the orthogonal complement being bottom. This is still a local
  Hilbert-space reformulation, not an RH implication.

Next route:

- Fill `T2.nyman.orthogonal.pointwise`: unpack membership in `nymanBeurlingKernelSpanᗮ` into
  vanishing inner products against every packaged kernel.

## Loop 2026-07-09-93: unpack orthogonality against the Nyman-Beurling generators

Blueprint node:

- `T2.nyman.orthogonal.pointwise`.

Pre-registered Lean statement:

- Prove `f ∈ nymanBeurlingKernelSpanᗮ ↔ ∀ a : ℝ, ⟪fractionalPartKernelL2 a, f⟫_ℝ = 0`.

Reason:

- Loop 92 turned density into the bottomness of the orthogonal complement.
- The next Hilbert-space reduction is to express an orthogonal-complement witness through scalar
  inner products against the original fractional-part generator family.

Search result:

- mathlib provides `Submodule.mem_orthogonal` and `Submodule.inner_right_of_mem_orthogonal`.
- The reverse direction is handled by `Submodule.span_induction` over the range of
  `fractionalPartKernelL2`.

Rejected route:

- Do not introduce an analytic integral formula for the inner products yet.
- Do not assert density, a Nyman-Beurling criterion, or an RH bridge in this loop.

Result:

- Opened the `InnerProductSpace` notation scope in `LeanLab.Riemann.NymanBeurling`.
- Proved `mem_nymanBeurlingKernelSpan_orthogonal_iff`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.orthogonal.pointwise` as `.proven`
  and add planned target `T2.nyman.density.pointwise`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- A vector is now formally known to be an orthogonal obstruction to the kernel span exactly when
  all packaged fractional-part kernels have zero inner product with it. This is still a local
  Hilbert-space statement and does not assert density.

Next route:

- Fill `T2.nyman.density.pointwise`: combine the orthogonal-bottom density theorem with the
  pointwise orthogonality theorem.

## Loop 2026-07-09-94: express density by absence of generator-orthogonal vectors

Blueprint node:

- `T2.nyman.density.pointwise`.

Pre-registered Lean statement:

- Prove that `nymanBeurlingKernelDense` is equivalent to every `f : unitIntervalL2` being zero
  whenever `⟪fractionalPartKernelL2 a, f⟫_ℝ = 0` for all real `a`.

Reason:

- Loop 92 proved density is equivalent to `nymanBeurlingKernelSpanᗮ = ⊥`.
- Loop 93 proved membership in that orthogonal complement is equivalent to vanishing inner
  products against all packaged fractional-part kernels.
- Combining these two facts gives the natural final Hilbert-space obstruction statement.

Search result:

- `Submodule.eq_bot_iff` converts bottomness of a submodule into the statement that all its
  members are zero.
- `mem_nymanBeurlingKernelSpan_orthogonal_iff` supplies the pointwise inner-product condition.

Rejected route:

- Do not add another equivalent Hilbert-space-only reformulation after this loop.
- Do not assert the density predicate itself, a Nyman-Beurling criterion, or an RH bridge.

Result:

- Proved `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.density.pointwise` as `.proven`
  and add planned target `T2.nyman.inner.integral.inventory`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The Nyman-Beurling foundation route now has a compiled equivalence between density and the
  absence of nonzero vectors orthogonal to every packaged fractional-part kernel. This is still a
  conditional reformulation, not a proof of density.

Next route:

- Fill `T2.nyman.inner.integral.inventory`: inspect `Lp` inner-product formulas and decide the
  next formal theorem that can rewrite the scalar inner products as integrals.

## Loop 2026-07-10-95: inventory and bridge L2 inner products to integrals

Blueprint node:

- `T2.nyman.inner.integral.inventory`.

Pre-registered question:

- Inspect mathlib support for rewriting `⟪fractionalPartKernelL2 a, f⟫_ℝ` as an integral over
  `volume.restrict (Set.Ioo 0 1)`.

Reason:

- Loop 94 closed the pure Hilbert-space obstruction form.
- To move toward an analytic Nyman-Beurling condition, the scalar inner products need to become
  concrete integrals against the fractional-part kernels.

Search result:

- `Mathlib/MeasureTheory/Function/L2Space.lean` provides `L2.inner_def`.
- The same file provides `L2.integrable_inner`.
- The existing local theorem `fractionalPartKernelL2_coeFn` identifies the packaged kernel with
  `fractionalPartKernel a` almost everywhere.

Rejected route:

- Do not attempt the full Nyman-Beurling criterion bridge yet.
- Do not continue with another purely abstract Hilbert-space equivalence after this loop.

Result:

- Added `research/tier2_nyman_inner_integral_inventory_20260710.md`.
- Proved `inner_fractionalPartKernelL2_eq_integral`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.inner.integral.inventory` as `.proven`
  and add planned target `T2.nyman.density.integral`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The scalar orthogonality condition can now be rewritten as an integral against the concrete
  fractional-part kernel. This is still not a proof of density.

Next route:

- Fill `T2.nyman.density.integral`: combine the integral bridge with
  `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`.

## Loop 2026-07-10-96: express the density obstruction by integrals

Blueprint node:

- `T2.nyman.density.integral`.

Pre-registered Lean statement:

- Prove that `nymanBeurlingKernelDense` is equivalent to every `f : unitIntervalL2` being zero
  whenever all integrals
  `∫ x, fractionalPartKernel a x * f x ∂(volume.restrict (Set.Ioo 0 1))`
  vanish.

Reason:

- Loop 94 reduced density to absence of nonzero vectors with all generator inner products equal to
  zero.
- Loop 95 rewrote the generator inner product as an integral against the concrete fractional-part
  kernel.

Search result:

- No new library theorem was needed beyond `inner_fractionalPartKernelL2_eq_integral`.
- The proof is a direct bidirectional substitution into
  `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`.

Rejected route:

- Do not assert the density predicate itself.
- Do not state the full Nyman-Beurling criterion before the target function and parameter
  restrictions are packaged.

Result:

- Proved `nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.density.integral` as `.proven`
  and add planned target `T2.nyman.constant.one.l2`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The Nyman-Beurling foundation route now has a compiled integral form of the density obstruction.
  This is still an equivalence, not a proof of density.

Next route:

- Fill `T2.nyman.constant.one.l2`: package the constant-one function in `unitIntervalL2` and prove
  its almost-everywhere representative theorem.

## Loop 2026-07-10-97: package constant one in the unit-interval L2 space

Blueprint node:

- `T2.nyman.constant.one.l2`.

Pre-registered Lean statement:

- Define the constant-one function, package it as `unitIntervalOneL2 : unitIntervalL2`, and prove
  an almost-everywhere representative theorem.

Reason:

- The Nyman-Beurling closure formulation needs a concrete target vector in the same Hilbert space
  as the fractional-part kernel span.
- Loop 96 produced the integral obstruction form for density, but it did not yet name the
  constant-one vector that the classical closure formulation targets.

Search result:

- `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` provides constant-function `MemLp`
  support and bounded-function `MemLp.of_bound`.
- The existing local kernel packaging pattern already used `MemLp.of_bound` and
  `MemLp.coeFn_toLp`, so the constant-one packaging can follow the same route.

Rejected route:

- Do not state the full Nyman-Beurling criterion yet.
- Do not assert that `unitIntervalOneL2` belongs to the closure unconditionally.

Result:

- Defined `unitIntervalOne`.
- Proved `measurable_unitIntervalOne` and `unitIntervalOne_memLp_two_unitInterval`.
- Defined `unitIntervalOneL2`.
- Proved `unitIntervalOneL2_coeFn` and `unitIntervalOneL2_coeFn_const`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.constant.one.l2` as `.proven`
  and add planned target `T2.nyman.density.one.closure`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The local Nyman-Beurling route now has both the generator family and the classical target vector
  living in the same compiled `L²(0,1)` space. This is still only setup for a closure statement.

Next route:

- Fill `T2.nyman.density.one.closure`: prove that `nymanBeurlingKernelDense` implies
  `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure`.

## Loop 2026-07-10-98: derive constant-one closure membership from density

Blueprint node:

- `T2.nyman.density.one.closure`.

Pre-registered Lean statement:

- Prove that `nymanBeurlingKernelDense` implies
  `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure`.

Reason:

- Loop 97 packaged the constant-one vector in `unitIntervalL2`.
- The local density predicate already has a pointwise closure form, so the next safe bridge is to
  instantiate that theorem at `unitIntervalOneL2`.

Search result:

- No new mathlib API was needed.
- Existing local theorem `nymanBeurlingKernelDense_iff_forall_mem_closure` directly provides the
  pointwise closure statement under density.

Rejected route:

- Do not assert `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure` without the density hypothesis.
- Do not state the full Nyman-Beurling criterion or RH implication.

Result:

- Proved `unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.density.one.closure` as `.proven`
  and add planned target `T2.nyman.one.closure.epsilon`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The route now connects the abstract density predicate to the concrete constant-one target vector
  as a compiled conditional theorem. This is still not a proof of density.

Next route:

- Fill `T2.nyman.one.closure.epsilon`: inspect mathlib closure API and reformulate the target
  closure membership as epsilon-distance approximation by vectors in `nymanBeurlingKernelSpan`.

## Loop 2026-07-10-99: reformulate constant-one closure as epsilon approximation

Blueprint node:

- `T2.nyman.one.closure.epsilon`.

Pre-registered Lean statement:

- Prove that `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure` is equivalent to: for every
  `0 < ε`, there exists `g ∈ nymanBeurlingKernelSpan` with
  `dist unitIntervalOneL2 g < ε`.

Reason:

- Loop 98 connected density to constant-one closure membership.
- The next classical approximation shape should expose actual approximants, not just abstract
  closure membership.

Search result:

- Local mathlib search found `Metric.mem_closure_iff` in
  `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`, with the needed
  `∀ ε > 0, ∃ y ∈ s, dist x y < ε` formulation.

Rejected route:

- Do not try to expand span membership into finite combinations in the same step.
- Do not assert that the approximants exist without either closure membership or the density
  hypothesis.

Result:

- Proved `unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt`.
- Proved `exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.one.closure.epsilon` as `.proven`
  and add planned target `T2.nyman.span.finite.approx`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The constant-one closure target is now available as an epsilon-distance approximation statement
  over the kernel span. The approximants are still abstract span elements.

Next route:

- Fill `T2.nyman.span.finite.approx`: inspect span-membership API and unpack `g ∈
  nymanBeurlingKernelSpan` into finite real linear combinations of packaged fractional-part
  kernels.

## Loop 2026-07-10-100: unpack span approximants as finite kernel combinations

Blueprint node:

- `T2.nyman.span.finite.approx`.

Pre-registered Lean statement:

- Reformulate the epsilon approximants from `nymanBeurlingKernelSpan` as finite-support real
  coefficient sums of the packaged kernels `fractionalPartKernelL2 a`.

Reason:

- Loop 99 produced abstract approximants `g ∈ nymanBeurlingKernelSpan`.
- To approach the classical Nyman-Beurling approximation statement, those span elements must be
  exposed as finite linear combinations.

Search result:

- Local mathlib search found `Finsupp.mem_span_range_iff_exists_finsupp` in
  `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`.
- This theorem exactly rewrites membership in `Submodule.span ℝ (Set.range fractionalPartKernelL2)`
  as existence of a finitely supported coefficient function.

Rejected route:

- Do not attempt the norm-form or integral-form approximation in the same loop.
- Do not introduce unrestricted infinite sums.

Result:

- Proved `mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum`.
- Proved `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`.
- Proved `exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.span.finite.approx` as `.proven`
  and add planned target `T2.nyman.finite.approx.norm`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The constant-one closure target now has a finite-combination epsilon approximation formulation.
  This is still conditional on the density statement when used as an existence theorem.

Next route:

- Fill `T2.nyman.finite.approx.norm`: rewrite the finite-combination distance bound as a norm
  inequality for `unitIntervalOneL2` minus the finite kernel combination.

## Loop 2026-07-10-101: rewrite finite-combination approximation in norm form

Blueprint node:

- `T2.nyman.finite.approx.norm`.

Pre-registered Lean statement:

- Reformulate the finite-combination epsilon approximation using
  `‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ < ε`.

Reason:

- Loop 100 exposed approximants as finite `Finsupp` coefficient sums.
- The classical Nyman-Beurling approximation is stated in a Hilbert/L2 norm form before being
  pushed down to an integral expression.

Search result:

- Local mathlib search confirmed `dist_eq_norm` is available for normed additive groups and is
  used throughout normed-space files.

Rejected route:

- Do not rewrite the `L²` norm as an integral in the same loop.
- Do not assert any integral-square formula before inventorying the available `Lp` norm API.

Result:

- Proved `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt`.
- Proved `exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark `T2.nyman.finite.approx.norm` as `.proven`
  and add planned target `T2.nyman.finite.approx.integral.inventory`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The finite-combination approximation target now has a compiled norm form. It remains conditional
  on density when used as an existence theorem.

Next route:

- Fill `T2.nyman.finite.approx.integral.inventory`: inspect `L²` norm-square-to-integral API and
  either prove a local bridge theorem or record the exact dependency gap.

## Loop 2026-07-10-102: inventory L2 norm-square integral support

Blueprint node:

- `T2.nyman.finite.approx.integral.inventory`.

Pre-registered inventory question:

- Inspect mathlib support for rewriting
  `‖unitIntervalOneL2 - finiteKernelCombination‖ ^ 2`
  as an integral over `volume.restrict (Set.Ioo 0 1)`.

Reason:

- Loop 101 put the finite-kernel approximation into norm form.
- The classical Nyman-Beurling approximation uses a square-integral norm, so the next safe step is
  to bridge Hilbert norm-square syntax to an integral of representatives.

Search result:

- `MeasureTheory.L2.inner_def` rewrites the `L²` inner product as an integral.
- `InnerProductSpace.norm_sq_eq_re_inner` rewrites norm-square as the real part of the self-inner
  product.
- `MeasureTheory.L2.integral_inner_eq_sq_eLpNorm` and `MeasureTheory.Lp.norm_def` are also
  available, but the self-inner-product route was the shortest compiled bridge.

Rejected route:

- Do not immediately assert the fully expanded integral
  `∫ x, (1 - finite_sum_of_fractional_part_kernels x)^2`.
- First prove the almost-everywhere representative theorem for finite kernel sums.

Result:

- Added `research/tier2_nyman_finite_approx_integral_inventory_20260710.md`.
- Proved `unitIntervalL2_norm_sq_eq_integral_mul_self`.
- Proved `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.finite.approx.integral.inventory` as `.proven` and add planned target
  `T2.nyman.finite.approx.representatives`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The finite-combination norm-square target is now connected to an integral of the chosen `Lp`
  representative. The concrete pointwise representative remains the next gap.

Next route:

- Fill `T2.nyman.finite.approx.representatives`: identify finite sums of packaged kernels almost
  everywhere with finite pointwise sums of `fractionalPartKernel`.

## Loop 2026-07-10-103: identify finite-kernel representatives and concrete squared integral

Blueprint node:

- `T2.nyman.finite.approx.representatives`.

Pre-registered Lean statement:

- For `c : ℝ →₀ ℝ`, prove that
  `c.sum fun a r => r • fractionalPartKernelL2 a` agrees almost everywhere with
  `fun x => c.sum fun a r => r * fractionalPartKernel a x`.
- Also prove the corresponding representative theorem for
  `unitIntervalOneL2 - finiteCombination`.

Reason:

- Loop 102 rewrote the norm square as an integral of the chosen `Lp` representative.
- Before using the classical finite fractional-part expression, Lean must identify that
  representative almost everywhere.

Search result:

- Local mathlib search found `Lp.coeFn_smul`, `Lp.coeFn_sub`, `Lp.coeFn_fun_finsetSum`, and
  `eventuallyEq_sum`.
- These are enough to combine packaged-kernel representative theorems through scalar multiples,
  finite sums, and subtraction from the constant-one representative.

Rejected route:

- Do not expand the square algebraically yet.
- Do not replace the `Lp` representative by a concrete function inside an integral without an
  almost-everywhere bridge.

Result:

- Proved `finsupp_sum_fractionalPartKernelL2_coeFn`.
- Proved `unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn`.
- Proved `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`, rewriting the
  norm-square integral as
  `∫ x, (1 - c.sum fun a r => r * fractionalPartKernel a x) *
    (1 - c.sum fun a r => r * fractionalPartKernel a x)`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.finite.approx.representatives` as `.proven` and add planned target
  `T2.nyman.finite.approx.integral.epsilon`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The finite-combination norm-square approximation has reached a concrete squared-error integral
  form. This remains conditional on `nymanBeurlingKernelDense` when used to produce approximants.

Next route:

- Fill `T2.nyman.finite.approx.integral.epsilon`: combine the density-conditioned norm
  approximation with the concrete norm-square identity to derive a finite concrete integral bound
  below `ε ^ 2`.

## Loop 2026-07-10-104: derive concrete squared-error bound under density

Blueprint node:

- `T2.nyman.finite.approx.integral.epsilon`.

Pre-registered Lean statement:

- Assuming `nymanBeurlingKernelDense` and `0 < ε`, prove the existence of finite coefficients
  `c : ℝ →₀ ℝ` such that the concrete squared-error integral
  `∫ x, (1 - c.sum fun a r => r * fractionalPartKernel a x) *
    (1 - c.sum fun a r => r * fractionalPartKernel a x)`
  is below `ε ^ 2`.

Reason:

- Loop 103 supplied the concrete integral identity.
- Loop 101 supplied the density-conditioned norm approximation.
- The remaining bridge is the elementary conversion from a norm bound to a squared norm bound.

Search result:

- Local mathlib search found `sq_lt_sq₀`, which states square is strictly monotone on nonnegative
  inputs.
- `norm_nonneg` and `hε.le` provide the nonnegativity hypotheses.

Rejected route:

- Do not try to remove the squared tolerance in the same loop.
- Do not expand the square algebraically into constant, linear, and quadratic finite-sum terms yet.

Result:

- Proved `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.finite.approx.integral.epsilon` as `.proven` and add planned target
  `T2.nyman.finite.approx.integral.tolerance`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The density predicate now yields finite concrete squared-error approximants with an `ε ^ 2`
  bound.

Next route:

- Fill `T2.nyman.finite.approx.integral.tolerance`: instantiate the squared-bound theorem with
  `Real.sqrt δ` to obtain the usual arbitrary positive tolerance form.

## Loop 2026-07-10-105: remove squared tolerance from concrete integral bound

Blueprint node:

- `T2.nyman.finite.approx.integral.tolerance`.

Pre-registered Lean statement:

- Assuming `nymanBeurlingKernelDense` and `0 < δ`, prove the existence of finite coefficients
  `c : ℝ →₀ ℝ` such that the concrete squared-error integral is below `δ`.

Reason:

- Loop 104 produced a bound below `ε ^ 2`.
- The usual approximation shape quantifies over an arbitrary positive tolerance, so the next safe
  bridge is to substitute `ε = Real.sqrt δ`.

Search result:

- Local mathlib search found `Real.sqrt_pos_of_pos` and `Real.sq_sqrt`.
- These exactly provide positivity of `Real.sqrt δ` and the simplification
  `(Real.sqrt δ) ^ 2 = δ` under `0 ≤ δ`.

Rejected route:

- Do not introduce a new approximation predicate in the same loop.
- Do not start the RH criterion bridge from Nyman-Beurling; this loop only normalizes the
  tolerance parameter.

Result:

- Proved `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.finite.approx.integral.tolerance` as `.proven` and add planned target
  `T2.nyman.concrete.approx.predicate`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The density predicate now yields the standard arbitrary-positive-tolerance concrete
  approximation statement.

Next route:

- Fill `T2.nyman.concrete.approx.predicate`: define a short project-local predicate for this
  concrete finite-approximation property and prove `nymanBeurlingKernelDense` implies it.

## Loop 2026-07-10-106: package the concrete approximation predicate

Blueprint node:

- `T2.nyman.concrete.approx.predicate`.

Pre-registered Lean statement:

- Define `nymanBeurlingConcreteApprox : Prop`, saying every positive tolerance has a finite
  real coefficient family whose concrete squared-error integral is below that tolerance.
- Prove `nymanBeurlingConcreteApprox_of_dense`.

Reason:

- Loop 105 produced the useful positive-tolerance theorem, but its statement repeats a long
  integral expression.
- A short predicate makes later comparison with classical Nyman-Beurling/Baez-Duarte statements
  easier and reduces statement churn.

Search result:

- No new mathlib API was needed; this loop uses the theorem from Loop 105 directly.

Rejected route:

- Do not claim equivalence with RH or a classical criterion in this loop.
- Do not change the kernel definition or coefficient domain before doing a bounded comparison
  inventory.

Result:

- Defined `nymanBeurlingConcreteApprox`.
- Proved `nymanBeurlingConcreteApprox_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.concrete.approx.predicate` as `.proven` and add planned target
  `T2.nyman.classical.criterion.inventory`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Conclusion:

- The local Nyman-Beurling foundation route now has a reusable concrete approximation predicate
  derived from Hilbert-space density.

Next route:

- Fill `T2.nyman.classical.criterion.inventory`: compare `nymanBeurlingConcreteApprox` with the
  exact classical criterion statement and record the formal gaps before any RH bridge attempt.

## Loop 2026-07-10-107: inventory the classical Nyman-Beurling criterion gap

Blueprint node:

- `T2.nyman.classical.criterion.inventory`.

Pre-registered output:

- Compare `nymanBeurlingConcreteApprox` with classical Nyman-Beurling/Baez-Duarte statement
  shapes.
- Record formal gaps before any criterion-to-RH bridge.
- Choose one Lean-sized next node.

Sources checked:

- ESI preprint, "The Nyman-Beurling Equivalent Form for the Riemann Hypothesis".
- Baez-Duarte 2002, "A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis".
- Baez-Duarte 2005, "A general strong Nyman-Beurling Criterion for the Riemann Hypothesis".

Result:

- Added `research/tier2_nyman_classical_criterion_inventory_20260710.md`.
- Marked `T2.nyman.classical.criterion.inventory` as `.proven` in
  `LeanLab/Riemann/Targets.lean`.
- Added planned target `T2.nyman.restricted.concrete.approx.predicate`.

Formal gaps recorded:

- Current predicate uses arbitrary real parameters; classical unit-interval forms restrict the
  parameter to a positive unit interval.
- Baez-Duarte's strong form points to natural parameters, requiring a later `ℕ+` or positive
  natural finite-support formulation.
- The project approximates the constant-one representative on the restricted unit interval,
  while Baez-Duarte also uses an `L²(0,∞)` indicator-target shape.
- The project has an integral-tolerance predicate, while classical criteria are usually phrased
  as closure or density statements for a restricted generating family.
- No local theorem currently connects such a closure criterion to mathlib's
  `RiemannHypothesis`.

Rejected route:

- Do not try a direct RH bridge from the current unrestricted predicate.
- Do not use the classical criterion as a premise until the restricted generator and closure
  statements are formalized locally.

Verification:

- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.concrete.approx.predicate`: define a restricted-support concrete
  approximation predicate with support contained in `0 < a ∧ a ≤ 1`, then prove it implies
  `nymanBeurlingConcreteApprox`.

## Loop 2026-07-10-108: package the restricted concrete approximation predicate

Blueprint node:

- `T2.nyman.restricted.concrete.approx.predicate`.

Pre-registered Lean statement:

- Define `nymanBeurlingRestrictedConcreteApprox : Prop`, saying every positive tolerance has a
  finite coefficient family whose active parameters all satisfy `0 < a ∧ a ≤ 1` and whose
  concrete squared-error integral is below that tolerance.
- Prove `nymanBeurlingConcreteApprox_of_restricted`.

Reason:

- Loop 107 identified parameter restriction as the first formal gap between the project predicate
  and the classical unit-interval Nyman-Beurling shape.
- A restricted predicate gives later closure or density statements a precise local target without
  claiming an RH bridge.

Search result:

- No new mathlib API was needed beyond ordinary `Finsupp.support` membership in the statement.

Rejected route:

- Do not try to derive the restricted predicate from `nymanBeurlingKernelDense`; the current dense
  route still uses unrestricted real parameters.
- Do not switch to natural parameters until the unit-interval restricted family has its own span
  and closure scaffold.

Result:

- Defined `nymanBeurlingRestrictedConcreteApprox`.
- Proved `nymanBeurlingConcreteApprox_of_restricted`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.concrete.approx.predicate` as `.proven` and add planned target
  `T2.nyman.restricted.span.scaffold`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.span.scaffold`: define the span of the restricted kernel family and
  prove it is contained in `nymanBeurlingKernelSpan`.

## Loop 2026-07-10-109: scaffold the restricted kernel span

Blueprint node:

- `T2.nyman.restricted.span.scaffold`.

Pre-registered Lean statement:

- Define the restricted parameter set `0 < a ∧ a ≤ 1`.
- Define the corresponding packaged kernel set and its real span in `unitIntervalL2`.
- Prove restricted generator membership and prove the restricted span is contained in
  `nymanBeurlingKernelSpan`.

Reason:

- Loop 108 packaged the restricted concrete approximation predicate, but the Hilbert-space side
  still only had the unrestricted span.
- A restricted span is the minimal structural object needed before attempting restricted closure
  or density statements.

Search result:

- Local code already used `Submodule.span` and `Submodule.span_le`; no new mathlib import was
  needed.

Rejected route:

- Do not claim the restricted span is dense.
- Do not derive restricted concrete approximation from unrestricted density.

Result:

- Defined `nymanBeurlingRestrictedParameterSet`.
- Defined `nymanBeurlingRestrictedKernelSet`.
- Defined `nymanBeurlingRestrictedKernelSpan`.
- Proved `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSet`.
- Proved `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan`.
- Proved `nymanBeurlingRestrictedKernelSpan_le`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.span.scaffold` as `.proven` and add planned target
  `T2.nyman.restricted.closure.scaffold`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.closure.scaffold`: define the restricted closure and prove its basic
  relation to `nymanBeurlingKernelClosure`.

## Loop 2026-07-10-110: scaffold the restricted kernel closure

Blueprint node:

- `T2.nyman.restricted.closure.scaffold`.

Pre-registered Lean statement:

- Define `nymanBeurlingRestrictedKernelClosure`.
- Prove the restricted span is contained in this closure.
- Prove the restricted closure is closed and has the expected set-level closure formula.
- Prove the restricted closure is contained in `nymanBeurlingKernelClosure`.

Reason:

- Loop 109 produced the restricted span, but closure-style Nyman-Beurling criteria need a closure
  object rather than only a span.
- The inclusion into the unrestricted closure is a useful sanity check and prevents the restricted
  branch from drifting away from the existing Hilbert-space scaffold.

Search result:

- Local mathlib search found `Submodule.topologicalClosure_mono`, matching the needed closure
  inclusion proof.

Rejected route:

- Do not assert restricted density yet.
- Do not turn closure membership into concrete approximation until the restricted density
  predicate and closure epsilon form exist.

Result:

- Defined `nymanBeurlingRestrictedKernelClosure`.
- Proved `nymanBeurlingRestrictedKernelSpan_le_closure`.
- Proved `isClosed_nymanBeurlingRestrictedKernelClosure`.
- Proved `nymanBeurlingRestrictedKernelClosure_coe`.
- Proved `nymanBeurlingRestrictedKernelClosure_le`.
- Proved `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelClosure`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.closure.scaffold` as `.proven` and add planned target
  `T2.nyman.restricted.density.predicate`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.density.predicate`: define restricted density and prove its
  closure-top and pointwise-closure forms.

## Loop 2026-07-10-111: package the restricted density predicate

Blueprint node:

- `T2.nyman.restricted.density.predicate`.

Pre-registered Lean statement:

- Define `nymanBeurlingRestrictedKernelDense : Prop`.
- Prove `nymanBeurlingRestrictedKernelDense ↔ nymanBeurlingRestrictedKernelClosure = ⊤`.
- Prove `nymanBeurlingRestrictedKernelDense ↔ ∀ f : unitIntervalL2,
  f ∈ nymanBeurlingRestrictedKernelClosure`.

Reason:

- Loop 110 produced the restricted closure object.
- Closure-style Nyman-Beurling statements need a named restricted density predicate before they
  can be related to unrestricted density or concrete approximation forms.

Search result:

- No new import was needed; the proof reuses the same `Submodule.dense_iff_topologicalClosure_eq_top`
  and closure-coercion pattern used by the unrestricted density predicate.

Rejected route:

- Do not claim restricted density is true.
- Do not turn restricted density into concrete approximation in the same loop; first record the
  bridge to unrestricted density and then build the restricted concrete chain separately.

Result:

- Defined `nymanBeurlingRestrictedKernelDense`.
- Proved `nymanBeurlingRestrictedKernelDense_iff_closure_eq_top`.
- Proved `nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.density.predicate` as `.proven` and add planned target
  `T2.nyman.restricted.density.implies.unrestricted`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.density.implies.unrestricted`: prove
  `nymanBeurlingRestrictedKernelDense → nymanBeurlingKernelDense`.

## Loop 2026-07-10-112: bridge restricted density to unrestricted density

Blueprint node:

- `T2.nyman.restricted.density.implies.unrestricted`.

Pre-registered Lean statement:

- Prove `nymanBeurlingKernelDense_of_restricted :
  nymanBeurlingRestrictedKernelDense → nymanBeurlingKernelDense`.

Reason:

- The restricted closure is contained in the unrestricted closure.
- Therefore, if every `unitIntervalL2` vector lies in the restricted closure, every vector also
  lies in the unrestricted closure.

Search result:

- No new import was needed; the proof uses the pointwise closure equivalences already compiled in
  previous loops.

Rejected route:

- Do not claim restricted density is true.
- Do not claim the finite approximants have restricted support in this bridge; it only recovers
  the existing unrestricted density predicate.

Result:

- Proved `nymanBeurlingKernelDense_of_restricted`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.density.implies.unrestricted` as `.proven` and add planned target
  `T2.nyman.restricted.density.concrete.approx`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.density.concrete.approx`: prove
  `nymanBeurlingRestrictedKernelDense → nymanBeurlingConcreteApprox`.

## Loop 2026-07-10-113: derive concrete approximation from restricted density

Blueprint node:

- `T2.nyman.restricted.density.concrete.approx`.

Pre-registered Lean statement:

- Prove `nymanBeurlingConcreteApprox_of_restrictedKernelDense :
  nymanBeurlingRestrictedKernelDense → nymanBeurlingConcreteApprox`.

Reason:

- Loop 112 proves restricted density implies unrestricted density.
- Loop 106 proves unrestricted density implies the project concrete approximation predicate.
- Their composition is a useful conditional bridge and a check that the restricted branch connects
  back to the existing concrete theorem chain.

Search result:

- No new API was needed; this loop composes existing project theorems.

Rejected route:

- Do not claim the finite coefficient support is restricted in this theorem.
- Do not use this as a classical Nyman-Beurling criterion-to-RH bridge.

Result:

- Proved `nymanBeurlingConcreteApprox_of_restrictedKernelDense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.density.concrete.approx` as `.proven` and add planned target
  `T2.nyman.restricted.density.one.closure`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.density.one.closure`: prove restricted density places
  `unitIntervalOneL2` in `nymanBeurlingRestrictedKernelClosure`.

## Loop 2026-07-10-114: place constant one in the restricted closure

Blueprint node:

- `T2.nyman.restricted.density.one.closure`.

Pre-registered Lean statement:

- Prove `unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense :
  nymanBeurlingRestrictedKernelDense →
    unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure`.

Reason:

- Loop 111 packaged the pointwise restricted-closure form of restricted density.
- A restricted-support approximation chain needs the constant-one target in the restricted
  closure before applying an epsilon-approximation theorem.

Search result:

- No new API was needed; the proof is direct instantiation of
  `nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`.

Rejected route:

- Do not use the unrestricted closure theorem here.
- Do not yet claim a finite restricted-support approximation; that requires a restricted
  closure-to-epsilon and restricted span-to-finite-sum chain.

Result:

- Proved `unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.density.one.closure` as `.proven` and add planned target
  `T2.nyman.restricted.one.closure.epsilon`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.one.closure.epsilon`: rewrite restricted closure membership as
  epsilon-distance approximation by restricted-span elements.

## Loop 2026-07-10-115: restricted closure epsilon approximation

Blueprint node:

- `T2.nyman.restricted.one.closure.epsilon`.

Pre-registered Lean statement:

- Prove `unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt`.
- Prove the restricted-density corollary
  `exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense`.

Reason:

- Loop 114 placed the constant-one target in the restricted closure under restricted density.
- The next formal bridge toward finite approximants is the metric closure characterization.

Search result:

- No new import was needed; the proof reuses `Metric.mem_closure_iff` and the restricted closure
  coercion theorem.

Rejected route:

- Do not unpack restricted-span elements into finite sums in this loop.
- Do not yet claim a concrete integral approximation with restricted finite support.

Result:

- Proved `unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt`.
- Proved `exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.one.closure.epsilon` as `.proven` and add planned target
  `T2.nyman.restricted.span.finite.approx`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.span.finite.approx`: unpack restricted-span membership into finite
  sums indexed by restricted parameters.

## Loop 2026-07-10-116: unpack restricted span as subtype-indexed finite sums

Blueprint node:

- `T2.nyman.restricted.span.finite.approx`.

Pre-registered Lean statement:

- Define `restrictedFractionalPartKernelL2`.
- Prove `nymanBeurlingRestrictedKernelSet = Set.range restrictedFractionalPartKernelL2`.
- Prove `mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum`.

Reason:

- Loop 115 produced restricted-span approximants, but a concrete approximation chain needs finite
  coefficient families.
- Indexing coefficients by the restricted-parameter subtype keeps the parameter restriction in
  the type before later mapping to ordinary real-indexed coefficients.

Search result:

- Reused mathlib's `Finsupp.mem_span_range_iff_exists_finsupp`, as in the unrestricted span
  finite-sum node.

Rejected route:

- Do not yet map subtype-indexed coefficients into `ℝ →₀ ℝ`.
- Do not yet rewrite finite sums into concrete representatives or integrals.

Result:

- Defined `restrictedFractionalPartKernelL2`.
- Proved `nymanBeurlingRestrictedKernelSet_eq_range`.
- Proved `mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.span.finite.approx` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.dist`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.dist`: derive subtype-indexed finite-sum distance
  approximants from restricted density.

## Loop 2026-07-10-117: derive subtype-indexed finite-sum distance approximants

Blueprint node:

- `T2.nyman.restricted.finite.approx.dist`.

Pre-registered Lean statement:

- Prove
  `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`.

Reason:

- Loop 115 gives a restricted-span approximant.
- Loop 116 unpacks restricted-span membership into subtype-indexed finite sums.
- Combining them gives the first finite coefficient approximation statement on the restricted
  branch.

Search result:

- No new API was needed; the proof combines existing project theorems.

Rejected route:

- Do not yet rewrite to norm or integrals in this loop.
- Do not yet map subtype-indexed coefficients to ordinary real-indexed coefficients.

Result:

- Proved `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.dist` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.norm`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.norm`: rewrite the finite-sum distance approximation
  as a norm inequality.

## Loop 2026-07-10-118: rewrite restricted finite-sum approximation in norm form

Blueprint node:

- `T2.nyman.restricted.finite.approx.norm`.

Pre-registered Lean statement:

- Prove `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`.

Reason:

- Loop 117 gives a restricted finite-sum approximation in distance form.
- The unrestricted branch already uses `dist_eq_norm` for the corresponding norm statement.
- The norm form is the bridge needed before norm-square and concrete-integral rewrites.

Search result:

- Reused the existing project pattern from
  `exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`.
- No additional mathlib API was needed beyond `dist_eq_norm`.

Rejected route:

- Do not yet rewrite the norm square as an integral in this loop.
- Do not yet identify subtype-indexed finite sums with concrete representatives.

Result:

- Proved `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.norm` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.integral.inventory`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.integral.inventory`: check whether the generic
  norm-square-to-integral bridge applies to subtype-indexed restricted finite sums.

## Loop 2026-07-10-119: inventory restricted norm-square integral bridge

Blueprint node:

- `T2.nyman.restricted.finite.approx.integral.inventory`.

Pre-registered Lean statement:

- Prove `norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`.

Reason:

- Loop 118 gives restricted finite-sum approximation in norm form.
- The unrestricted branch already has a generic `unitIntervalL2` norm-square-to-integral bridge.
- Before expanding concrete fractional-part functions, check whether the generic bridge applies to
  the subtype-indexed finite sum.

Search result:

- Reused `unitIntervalL2_norm_sq_eq_integral_mul_self`.
- The restricted finite sum is already a `unitIntervalL2` element, so no new measure-theoretic API
  was needed for this bridge.

Rejected route:

- Do not yet rewrite to the concrete squared-error integral.
- Do not yet map restricted subtype coefficients into ordinary real-indexed coefficients.

Result:

- Added `research/tier2_nyman_restricted_finite_approx_integral_inventory_20260710.md`.
- Proved `norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.integral.inventory` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.representatives`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.representatives`: identify subtype-indexed restricted
  finite sums with concrete representatives.

## Loop 2026-07-10-120: identify restricted finite-sum representatives

Blueprint node:

- `T2.nyman.restricted.finite.approx.representatives`.

Pre-registered Lean statements:

- Prove `restricted_finsupp_sum_fractionalPartKernelL2_coeFn`.
- Prove `unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn`.
- Prove `norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`.

Reason:

- Loop 119 rewrote the restricted finite-sum norm square as an integral of the selected `Lp`
  representative.
- To move toward the classical squared-error integral, that representative must be identified
  with concrete finite sums of fractional-part kernels.

Search result:

- Reused the unrestricted finite-sum representative proof pattern.
- `Lp.coeFn_sub` exposes a sum of coerced terms, so the restricted difference theorem needed an
  explicit `Finsupp.sum` expansion instead of only composing the finite-sum AE theorem.

Rejected route:

- Do not yet derive the density-conditioned integral bound in this loop.
- Do not yet map restricted subtype coefficients into ordinary real-indexed coefficients.

Result:

- Proved `restricted_finsupp_sum_fractionalPartKernelL2_coeFn`.
- Proved `unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn`.
- Proved `norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.representatives` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.integral.epsilon`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.integral.epsilon`: combine the restricted norm
  approximant with the concrete norm-square integral theorem.

## Loop 2026-07-10-121: derive restricted concrete integral epsilon-square bound

Blueprint node:

- `T2.nyman.restricted.finite.approx.integral.epsilon`.

Pre-registered Lean statement:

- Prove `exists_restricted_finsupp_integral_sq_lt_of_dense`.

Reason:

- Loop 118 gives subtype-indexed restricted finite sums within norm `ε`.
- Loop 120 rewrites the corresponding restricted norm square as a concrete squared-error integral.
- Combining those facts gives the restricted finite-sum concrete integral bound below `ε ^ 2`.

Search result:

- Reused the unrestricted proof pattern from
  `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`.
- No additional mathlib API was needed beyond `sq_lt_sq₀`.

Rejected route:

- Do not yet remove the squared tolerance in this loop.
- Do not yet package the restricted concrete approximation predicate.

Result:

- Proved `exists_restricted_finsupp_integral_sq_lt_of_dense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.integral.epsilon` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.integral.tolerance`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.integral.tolerance`: use `Real.sqrt` to replace the
  squared tolerance with an arbitrary positive tolerance.

## Loop 2026-07-10-122: remove squared tolerance from restricted concrete integral bound

Blueprint node:

- `T2.nyman.restricted.finite.approx.integral.tolerance`.

Pre-registered Lean statement:

- Prove `exists_restricted_finsupp_integral_lt_of_dense_tolerance`.

Reason:

- Loop 121 gives a restricted concrete squared-error integral bound below `ε ^ 2`.
- The unrestricted branch already removes the squared tolerance by instantiating with
  `Real.sqrt δ`.
- This gives the positive-tolerance form needed before aligning with the existing restricted
  concrete approximation predicate.

Search result:

- Reused the unrestricted proof pattern from
  `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`.
- No additional mathlib API was needed beyond `Real.sqrt_pos_of_pos` and `Real.sq_sqrt`.

Rejected route:

- Do not yet claim `nymanBeurlingRestrictedConcreteApprox` follows from restricted density.
- Do not yet erase the subtype index without a compiled finite-sum reindexing bridge.

Result:

- Proved `exists_restricted_finsupp_integral_lt_of_dense_tolerance`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.integral.tolerance` as `.proven` and add planned target
  `T2.nyman.restricted.finite.approx.real.support`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.finite.approx.real.support`: convert subtype-indexed coefficients
  into real-indexed coefficients with explicit restricted support.

## Loop 2026-07-10-123: push restricted subtype coefficients to real-indexed support

Blueprint node:

- `T2.nyman.restricted.finite.approx.real.support`.

Pre-registered Lean statements:

- Prove `exists_real_finsupp_of_restricted_finsupp`.
- Prove `exists_real_finsupp_integral_lt_of_restricted`.

Reason:

- Loop 122 gives the positive-tolerance concrete approximation with coefficients indexed by
  `nymanBeurlingRestrictedParameterSet`.
- The existing reusable predicate `nymanBeurlingRestrictedConcreteApprox` is indexed by `ℝ` and
  carries the support restriction as an explicit condition.
- A compiled reindexing bridge is needed before packaging the predicate.

Search result:

- Reused `Finsupp.embDomain` along `Function.Embedding.subtype`.
- Used `Finsupp.support_embDomain` through the `support.map` representation.
- Used `Finsupp.sum_embDomain` to preserve the concrete finite sum.

Rejected route:

- Do not yet package `nymanBeurlingRestrictedConcreteApprox` in this loop.
- Do not manually rebuild a real-indexed finitely supported function.

Result:

- Proved `exists_real_finsupp_of_restricted_finsupp`.
- Proved `exists_real_finsupp_integral_lt_of_restricted`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.finite.approx.real.support` as `.proven` and add planned target
  `T2.nyman.restricted.concrete.approx.of.dense`.

Proof note:

- Lean did not unfold the subtype property automatically in the support proof; the proof changes
  the goal to the property of `(b : ℝ)` before applying `b.property`.
- The finite-sum proof changes the target to `emb a` form before applying `Finsupp.sum_embDomain`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.concrete.approx.of.dense`: combine the positive-tolerance subtype
  approximation with the real-support bridge to prove `nymanBeurlingRestrictedConcreteApprox`.

## Loop 2026-07-10-124: package restricted concrete approximation from restricted density

Blueprint node:

- `T2.nyman.restricted.concrete.approx.of.dense`.

Pre-registered Lean statement:

- Prove `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`.

Reason:

- Loop 122 gives positive-tolerance subtype-indexed concrete approximants from restricted
  density.
- Loop 123 pushes those approximants to real-indexed coefficients with explicit restricted
  support.
- The project-local predicate `nymanBeurlingRestrictedConcreteApprox` is exactly this packaged
  statement.

Search result:

- No new API was needed; the proof composes the positive-tolerance subtype theorem with the
  real-support bridge.

Rejected route:

- Do not yet claim the classical Báez-Duarte/Nyman-Beurling criterion.
- Do not yet proceed to another structural bridge before summarizing this completed restricted
  branch and its remaining gaps.

Result:

- Proved `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.concrete.approx.of.dense` as `.proven` and add planned target
  `T2.nyman.restricted.route.summary`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.restricted.route.summary`: record the compiled restricted-density to
  restricted-concrete chain and the remaining classical criterion gaps.

## Loop 2026-07-10-125: summarize the completed restricted route

Blueprint node:

- `T2.nyman.restricted.route.summary`.

Pre-registered output:

- Add `research/tier2_nyman_restricted_route_summary_20260710.md`.

Reason:

- Loop 124 closed the project-local restricted density to restricted concrete approximation chain.
- The route should be summarized before choosing the next structural bridge, so later loops do not
  confuse the local predicate with a classical criterion.

Search result:

- Reused the compiled theorem list in `LeanLab.Riemann.NymanBeurling`.
- Reused the earlier classical-gap inventory
  `research/tier2_nyman_classical_criterion_inventory_20260710.md`.

Rejected route:

- Do not yet claim a Baez-Duarte natural-parameter theorem.
- Do not yet attempt an implication to `RiemannHypothesis`.

Result:

- Added `research/tier2_nyman_restricted_route_summary_20260710.md`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.restricted.route.summary` as `.proven` and add planned target
  `T2.nyman.baez.duarte.natural.index.inventory`.

Verification:

- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Fill `T2.nyman.baez.duarte.natural.index.inventory`: choose a Lean indexing shape and reciprocal
  map for Baez-Duarte natural-parameter approximants.

## Loop 2026-07-10-126: inventory Baez-Duarte natural indexing

Blueprint node:

- `T2.nyman.baez.duarte.natural.index.inventory`.

Pre-registered output:

- Add `research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md`.
- Mark the inventory target complete and add the next small formal bridge target.

Reason:

- The arch review asks each loop to discharge a target, fill a blueprint node, or record a bounded
  inventory/failure route.
- After the restricted concrete branch, the next classical gap is the Baez-Duarte strengthening from
  restricted real parameters to positive natural parameters.
- Before proving finite-sum transport, the Lean index type and reciprocal map should be fixed.

Search result:

- Primary literature search confirms the Baez-Duarte strengthening is about restricting the
  Nyman-Beurling generating parameters to positive natural dilations.
- Local Lean search found `PNat`/`ℕ+` as `{n : Nat // 0 < n}`.
- Local Lean search found the expected reciprocal-bound tools: `Nat.cast_pos`, `inv_pos`, and
  `inv_le_one_of_one_le₀`.
- Existing project code already transports restricted subtype coefficients with
  `Function.Embedding.subtype` and `Finsupp.embDomain`.

Rejected route:

- Do not state a classical Baez-Duarte criterion or connect it to `RiemannHypothesis` in this loop.
- Do not index coefficients by plain `Nat`; zero would create a recurring side condition.
- Do not keep the next bridge indexed by arbitrary restricted real parameters; that would miss the
  natural-parameter strengthening.

Result:

- Added `research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.baez.duarte.natural.index.inventory` as `.proven` and add planned target
  `T2.nyman.baez.duarte.reciprocal.map`.
- Updated `research/blueprint.md` with the completed inventory result and next bridge node.

Verification:

- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Close `T2.nyman.baez.duarte.reciprocal.map`: define or verify the reciprocal map from positive
  natural indices into `nymanBeurlingRestrictedParameterSet`, preferably in a form usable by
  `Finsupp.embDomain`.

## Loop 2026-07-10-127: formalize the Baez-Duarte reciprocal map

Blueprint node:

- `T2.nyman.baez.duarte.reciprocal.map`.

Pre-registered Lean output:

- Add a positive-natural index type alias.
- Prove the reciprocal parameter lies in `nymanBeurlingRestrictedParameterSet`.
- Package the map as an embedding if injectivity is small.

Reason:

- Loop 126 selected `{n : Nat // 0 < n}` and `n ↦ ((n : Real)⁻¹)` as the next bridge shape.
- The finite-sum transport should not be attempted until the reciprocal map is a compiled Lean
  object.

Search result:

- `Nat.cast_pos` gives positivity of the real cast of a positive natural.
- `Nat.succ_le_of_lt` plus `exact_mod_cast` gives `(1 : Real) <= (n : Real)`.
- `inv_pos` and `inv_le_one_of_one_le₀` discharge the restricted-parameter membership.
- Injectivity is proved by applying inverse twice and then casting equality of real natural casts
  back to natural equality.

Rejected route:

- Do not yet transport finite coefficients; keep that as the next standalone target.
- Do not introduce a classical Baez-Duarte approximation predicate until finite-sum transport is
  compiled.

Result:

- Added `baezDuartePositiveNatIndex`.
- Added `baezDuarte_reciprocal_mem_restricted`.
- Added `baezDuarteReciprocalParameter`.
- Added `baezDuarteReciprocalEmbedding`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.baez.duarte.reciprocal.map` as `.proven` and add planned target
  `T2.nyman.baez.duarte.natural.finsupp.bridge`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Close `T2.nyman.baez.duarte.natural.finsupp.bridge`: use `Finsupp.embDomain` along
  `baezDuarteReciprocalEmbedding` and prove the concrete finite reciprocal-parameter sum is
  preserved.

## Loop 2026-07-10-128: transport Baez-Duarte finite coefficients

Blueprint node:

- `T2.nyman.baez.duarte.natural.finsupp.bridge`.

Pre-registered Lean output:

- Prove that every finite coefficient function indexed by `baezDuartePositiveNatIndex` can be
  transported to a finite coefficient function indexed by `nymanBeurlingRestrictedParameterSet`.
- Preserve the concrete reciprocal-parameter finite sum pointwise in `x`.

Reason:

- Loop 127 produced the embedding needed by `Finsupp.embDomain`.
- This bridge is the exact finite-support mechanism needed before moving to integral bounds or a
  natural-parameter approximation predicate.

Search result:

- Reused the existing project pattern from `exists_real_finsupp_of_restricted_finsupp`.
- `Finsupp.sum_embDomain` gives the sum-preservation statement after unfolding
  `baezDuarteReciprocalEmbedding` and `baezDuarteReciprocalParameter`.

Rejected route:

- Do not yet state a Baez-Duarte natural approximation predicate.
- Do not yet push the result through the squared-error integral; that is the next bounded corollary.

Result:

- Added `exists_restricted_finsupp_of_baezDuarte_finsupp`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.baez.duarte.natural.finsupp.bridge` as `.proven` and add planned target
  `T2.nyman.baez.duarte.natural.integral.bridge`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Close `T2.nyman.baez.duarte.natural.integral.bridge`: transport a positive-natural-indexed
  concrete squared-error integral bound to a restricted-parameter integral bound.

## Loop 2026-07-10-129: transport Baez-Duarte integral bounds

Blueprint node:

- `T2.nyman.baez.duarte.natural.integral.bridge`.

Pre-registered Lean output:

- Prove that an existential squared-error integral bound with positive-natural reciprocal
  parameters implies the corresponding existential restricted-parameter integral bound.

Reason:

- Loop 128 gave pointwise preservation of the finite reciprocal-parameter sum.
- The next reusable bridge is to lift that pointwise equality through the concrete squared-error
  integral.

Search result:

- Reused the existing project pattern from `exists_real_finsupp_integral_lt_of_restricted`.
- `integral_congr_ae` and `ae_of_all` were sufficient after rewriting with
  `exists_restricted_finsupp_of_baezDuarte_finsupp`.

Rejected route:

- Do not yet define the full positive-natural approximation predicate inside this loop.
- Do not claim a Baez-Duarte criterion or implication to `RiemannHypothesis`.

Result:

- Added `exists_restricted_finsupp_integral_lt_of_baezDuarte`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.baez.duarte.natural.integral.bridge` as `.proven` and add planned target
  `T2.nyman.baez.duarte.natural.concrete.approx.predicate`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- Close `T2.nyman.baez.duarte.natural.concrete.approx.predicate`: define the positive-natural
  reciprocal approximation predicate and prove it implies `nymanBeurlingRestrictedConcreteApprox`.

## Loop 2026-07-10-130: package Baez-Duarte natural concrete approximation

Blueprint node:

- `T2.nyman.baez.duarte.natural.concrete.approx.predicate`.

Pre-registered Lean output:

- Define a positive-natural reciprocal concrete approximation predicate.
- Prove that this predicate implies `nymanBeurlingRestrictedConcreteApprox`.

Reason:

- Loops 127-129 built the reciprocal map, finite-support bridge, and integral bridge.
- The next reusable object is the predicate itself, so later loops can compose with it without
  restating the existential integral shape.

Search result:

- Reused `exists_restricted_finsupp_integral_lt_of_baezDuarte`.
- Reused `exists_real_finsupp_integral_lt_of_restricted` to move from restricted subtype
  coefficients to the existing real-support restricted predicate.

Rejected route:

- Do not claim the classical Baez-Duarte/Nyman-Beurling criterion.
- Do not claim any implication to `RiemannHypothesis`.
- Do not add the unrestricted concrete corollary in the same loop; keep it as the next small target.

Result:

- Added `nymanBeurlingBaezDuarteConcreteApprox`.
- Added `nymanBeurlingRestrictedConcreteApprox_of_baezDuarte`.
- Updated `LeanLab/Riemann/Targets.lean` to mark
  `T2.nyman.baez.duarte.natural.concrete.approx.predicate` as `.proven` and add planned target
  `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted`.

Verification:

- `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- `lake env lean LeanLab/Riemann/Targets.lean` passed.
- `lake build` passed.
- Full project keyword scan passed with no matches.

Next route:

- V2 protocol reclassifies `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` as a
  mechanical batch item: compose
  `nymanBeurlingRestrictedConcreteApprox_of_baezDuarte` with
  `nymanBeurlingConcreteApprox_of_restricted`.

## Governance checkpoint 2026-07-10: Loop Protocol V2

Source:

- `/Users/karasuakamatsu/Downloads/rh_loop_protocol_v2_20260710.md`
- `/Users/karasuakamatsu/.codex/attachments/fb68cde6-ceb8-4986-9180-fbceb69fae28/pasted-text.txt`

Result:

- Do not resume the RH proof loop from the old target-selection rule.
- Added fixed hard-gap tracking in `research/hard_gap_dag.md` and `research/hard_gaps.md`.
- Classified loops 1-130 in `research/loop_classification_20260710.md`.
- Replaced the operating section of `research/rh_loop_protocol_20260709.md` with protocol v2.
- Hardened `LeanLab/Riemann/Targets.lean` by changing `leanName` entries to checked
  double-backtick identifiers.
- Added `LeanLab/Riemann/TargetChecks.lean` and imported it from `LeanLab.lean`.
- Marked the would-be loop-131 corollary as a mechanical batch item, not standalone RH progress.

Future attempt records must include:

- `node_id`, `work_class`, `result_class`
- `assumption_frontier_before`, `assumption_frontier_after`
- `hard_gap_before`, `hard_gap_after`, `hard_gap_delta`
- Lean verification commands and results
- theorem names and nearest known literature
- model, reasoning effort, budget, compaction state, and commit SHA

## Audit 2026-07-10-M0-01: unrestricted-parameter falsification test

- `loop_id`: `AUDIT-20260710-M0-01`
- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `BRANCH_FALSIFIED`
- exact mathematical statement: allowing both `a` and `-a` makes the unrestricted concrete
  approximation predicate unconditional, because their fractional-part kernels sum to one away
  from a countable exceptional set.
- exact Lean statement: `nymanBeurlingConcreteApprox_unconditional :
  nymanBeurlingConcreteApprox`
- published source: this is a statement-alignment audit against the restricted parameter domains
  in Balazard-Saias (1998) and Baez-Duarte (2002), not a new criterion claim.
- `assumption_frontier_before`: the project treats `nymanBeurlingConcreteApprox` as a possible
  local approximation shape but has no criterion bridge.
- `hard_gap_before`: M0 is open; the unrestricted predicate has not been tested for accidental
  triviality.
- `assumption_frontier_after`: the unrestricted predicate is proved without RH and is excluded
  from future criterion work; only restricted continuous and positive-natural statements remain.
- `hard_gap_after`: M0 remains in progress with the unrestricted branch formally rejected.
- `hard_gap_delta`: one candidate statement branch eliminated.
- standalone justification: this is not a rename or one-step transport; it can falsify a candidate
  statement by proving it without RH.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: clean-context audit started after reading the source DAG, protocol, handoff,
  target ledger, attempt tail, and exact Lean definitions
- theorem name: `nymanBeurlingConcreteApprox_unconditional`
- nearest known literature: Balazard-Saias (1998) restricts to positive unit-interval parameters;
  Baez-Duarte (2002) restricts to positive natural dilations.
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs.
- full project proof-gap keyword scan: passed with no matches.
- detailed alignment record: `research/m0_statement_alignment_20260710.md`
- audit decision: `PIVOT`
- commit SHA: resolve the commit titled `research: falsify unrestricted Nyman predicate`; the exact
  SHA is recorded in the external task ledger after the commit is created.

## Batch 2026-07-10-M0-02: restricted closure/tolerance alignment

- `loop_id`: `BATCH-20260710-M0-02`
- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- exact mathematical statement: the constant-one vector belongs to the closure of the span of
  kernels with `0 < a` and `a <= 1` if and only if finite combinations with the same support
  restriction have arbitrarily small positive squared-error integral.
- exact Lean statement: `unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox :
  unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
    nymanBeurlingRestrictedConcreteApprox`
- published source: Balazard-Saias (1998), unit-interval Nyman-Beurling closure formulation; this
  batch only aligns the project tolerance predicate with its closure shape.
- `assumption_frontier_before`: restricted density implies the concrete predicate, but no converse
  or exact closure-membership equivalence is compiled.
- `hard_gap_before`: M0 closure-versus-tolerance alignment is open.
- expected `hard_gap_delta`: close the closure/tolerance representation mismatch inside M0; do not
  claim G1, M1, D, or RH progress.
- `assumption_frontier_after`: the project restricted closure and tolerance predicate are exactly
  equivalent, but neither is the published Beurling space because both omit the zero-moment
  condition. The positive-natural local predicate likewise omits the Baez-Duarte full-line tail.
- `hard_gap_after`: M0 closure/tolerance representation is closed; the missing moment/tail
  dependency is isolated and Lean-validated.
- `hard_gap_delta`: one internal mismatch closed and one previously hidden published-statement
  dependency identified; G1, M1, D, and RH are unchanged.
- batch justification: support membership, finite-sum span membership, norm-square transport, and
  the final iff are one representation-alignment batch.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: source DAG, protocol, handoff, exact Lean definitions, and previous M0 audit
  were re-read before starting
- theorem names: `finsupp_sum_mem_nymanBeurlingRestrictedKernelSpan`,
  `unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox`,
  `restricted_finsupp_sum_eq_moment_div_of_one_lt`,
  `integral_Ioi_moment_div_mul_self`, and
  `restricted_finsupp_tail_error_eq_moment_sq`
- nearest known literature: Beurling (1955) imposes `sum c_k * theta_k = 0`; Balazard-Saias
  (2000) use modified generators encoding that condition; Baez-Duarte (2003) retains the
  equivalent tail through the full `L2(0,infinity)` norm.
- detailed alignment record: `research/m0_restricted_closure_alignment_20260710.md`
- audit decision: `PIVOT` to a positive-natural finite-error statement with the squared reciprocal
  moment restored
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs.
- full project proof-gap keyword scan: passed with no matches.
- commit SHA: resolve the commit titled `research: isolate Nyman moment tail gap`; the exact SHA is
  recorded in the external task ledger after the commit is created.

## Batch 2026-07-10-M0-03: positive-natural full-line split error

- `loop_id`: `BATCH-20260710-M0-03`
- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `FORMALIZATION_ONLY`
- exact mathematical statement: for positive-natural reciprocal kernels, the published
  `L2(0,infinity)` finite approximation error is the `(0,1)` constant-one error plus the
  `(1,infinity)` zero-target tail, and the tail equals the squared reciprocal coefficient moment.
- exact Lean outputs: define `baezDuarteSplitFullLineError` and
  `nymanBeurlingBaezDuarteFullLineConcreteApprox`; prove the split error normal form and the safe
  implication from the full-line predicate to `nymanBeurlingBaezDuarteConcreteApprox`.
- published source: Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann
  Hypothesis* (2003), Theorem 1.1, `H = L2(0,infinity)` and positive-natural generators.
- `assumption_frontier_before`: reciprocal natural indexing is compiled, but the only packaged
  natural predicate drops the full-line tail and is not the published statement.
- `hard_gap_before`: M0 has isolated but not restored the natural-criterion domain/target mismatch.
- expected `hard_gap_delta`: produce a Lean statement with the correct split full-line finite
  error; do not claim the published RH equivalence or any G1/D progress.
- `assumption_frontier_after`: the source-faithful positive-natural split full-line finite-error
  predicate is compiled; the old local predicate is only a weak consequence.
- `hard_gap_after`: positive-natural parameters, target values, and finite full-line error are
  aligned in split form. Whole-space `Lp` closure packaging, endpoint/field bridges, and M1 remain.
- `hard_gap_delta`: the missing tail is restored in the formal statement, but G1, M1, D, and RH are
  unchanged.
- batch justification: reciprocal moment, natural tail, split error, normal form, and safe local
  implication are one external-statement alignment batch.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: M0 source audit, fixed DAG, exact natural-index definitions, and Batch 02 tail
  theorem were re-read before starting
- theorem names: `baezDuarteReciprocalMoment`, `baezDuarteUnitIntervalError`,
  `baezDuarteSplitFullLineError`,
  `baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt`,
  `baezDuarte_finsupp_tail_error_eq_reciprocalMoment_sq`,
  `baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq`,
  `nymanBeurlingBaezDuarteFullLineConcreteApprox`,
  `nymanBeurlingBaezDuarteFullLineConcreteApprox_iff`, and
  `nymanBeurlingBaezDuarteConcreteApprox_of_fullLine`
- nearest known literature: Baez-Duarte (2003), Theorem 1.1, positive-natural generators in
  `L2(0,infinity)` with target `chi_(0,1]`.
- detailed alignment record: `research/m0_baez_duarte_full_line_alignment_20260710.md`
- decision: `CONTINUE` M0 with whole-space `Lp` closure packaging
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs.
- commit SHA: resolve the commit titled `research: restore Baez-Duarte full-line error`; the exact
  SHA is recorded in the external task ledger after the commit is created.

## Batch 2026-07-10-M0-04: positive-half-line L2 closure alignment

- `loop_id`: `BATCH-20260710-M0-04`
- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- expected `result_class`: `FORMALIZATION_ONLY`
- exact mathematical target: package the target indicator and positive-natural fractional-part
  kernels in the actual real Hilbert space `L2((0, infinity), dx)`, then prove that target
  membership in the closure of their real finite span is equivalent to
  `nymanBeurlingBaezDuarteFullLineConcreteApprox`.
- published source: Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann
  Hypothesis* (2003), Theorem 1.1, with `H = L2(0, infinity)`, target `chi_(0,1]`, and generators
  indexed by positive natural reciprocals.
- `assumption_frontier_before`: the source-faithful finite error is available only as two split
  integrals; no whole-space `Lp` objects, span, closure, or closure/tolerance equivalence exist.
- `hard_gap_before`: M0 whole-space closure packaging, endpoint alignment, and coefficient-field
  comparison remain; M1/G1 is open.
- expected `hard_gap_delta`: close the real whole-space closure/tolerance representation mismatch
  and absorb the endpoint difference as a null-set fact; do not claim M1, G1, D, or RH progress.
- batch justification: `MemLp` packaging, representative formulas, norm-square integration,
  interval splitting, finite-span membership, and closure/tolerance conversion are one external
  statement-alignment batch.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: resumed from a generated context summary, then re-read the worktree, fixed DAG,
  attempts tail, external memory protocol, and exact Lean definitions before registration
- planned Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean`, relevant target
  checks, full `lake build`, full project proof-gap keyword scan, and diff checks.
- `result_class`: `FORMALIZATION_ONLY`
- `assumption_frontier_after`: `chi_(0,1]` and every positive-natural reciprocal kernel are
  packaged in real `L2(0,infinity)`; the whole-space norm error equals the Batch 03 split error,
  and target closure membership is exactly the source-faithful positive-tolerance predicate.
- `hard_gap_after`: M0 whole-space packaging and endpoint alignment are closed. The bounded
  coefficient-field/source-convention audit remains; M1/G1, D, and RH are unchanged.
- `hard_gap_delta`: two M0 representation mismatches closed; no published criterion-to-RH theorem
  was proved.
- theorem names: `fractionalPartKernel_memLp_two_positiveHalfLine`,
  `baezDuarteTargetFunction_memLp_two_positiveHalfLine`, `baezDuarteKernelL2`,
  `baezDuarteKernelSpan`, `baezDuarteKernelClosure`,
  `norm_sub_baezDuarte_sum_sq_eq_wholeLineError`, `baezDuarteWholeLineError_eq_split`, and
  `baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox`.
- endpoint result: `(0,1]` and `(0,1)` give the same local volume integral by
  `integral_Ioc_eq_integral_Ioo`.
- detailed alignment record: `research/m0_baez_duarte_l2_closure_alignment_20260710.md`
- decision: `CONTINUE` M0 only for the coefficient-field/source-convention audit, then decide
  whether M0 can close and M1 can begin.
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed without warnings.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs; the only style warning was removed and the
  affected file was recompiled cleanly.
- full project proof-gap keyword scan: passed with no matches.
- `git diff --check`: passed.
- commit SHA: resolve the commit titled `research: align Baez-Duarte L2 closure`; the exact SHA is
  recorded in the external task ledger after the commit is created.

## Batch 2026-07-10-M0-05: coefficient-field closure audit

- `loop_id`: `BATCH-20260710-M0-05`
- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- expected `result_class`: `HARD_GAP_REDUCED`
- exact mathematical target: define the complex `L2(0,infinity)` closure of the same real-valued
  positive-natural kernels and prove that the real target belongs to it if and only if
  `baezDuarteTargetL2` belongs to the real closure from Batch 04.
- primary source: Baez-Duarte (2002/2003), *A Strengthening of the Nyman-Beurling Criterion for the
  Riemann Hypothesis*, abstract, Section 1, Theorem 1.1, and Section 2.2. The paper sets
  `H = L2(0,infinity)`, defines `Bnat` as the linear hull of the real-valued kernels, and in the RH
  direction constructs finite approximants with coefficients `mu(a) / a^epsilon` for real
  positive `epsilon`.
- source audit conclusion before Lean work: the paper's proof already supplies real coefficients,
  but the scalar convention behind the phrase linear hull is not explicit enough to leave
  unaudited. A real-part bridge will make either convention equivalent for this real target and
  real generating family.
- `assumption_frontier_before`: the source-faithful real closure statement is compiled; a possible
  complex-Hilbert-space reading has not been connected to it.
- `hard_gap_before`: M0 has one remaining coefficient-field/source-convention item; M1/G1 is open.
- expected `hard_gap_delta`: close M0 if and only if the complex/real closure bridge compiles and a
  final requirement-by-requirement M0 audit finds no remaining statement mismatch. M1, G1, D, and
  RH remain unproved.
- batch justification: complex `Lp` packaging, pointwise real-part transport of finite spans,
  continuity through closure, and the final M0 audit are one coefficient-field alignment batch.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: clean continuation after Batch 04; current worktree, fixed DAG, task ledger,
  primary-source PDF, and mathlib `ContinuousLinearMap.compLpL` APIs were checked before
  registration.
- `result_class`: `HARD_GAP_REDUCED`
- source artifact: `https://arxiv.org/pdf/math/0202141`, SHA-256
  `3ce4aff466443c71094affc1f8b6f5f0dd36cb4377dc5d2ceddbd2537c1d1819`.
- source audit result: the paper uses `H = L2(0,infinity)`, target `chi_(0,1]`, positive-natural
  kernels `rho(1/(a*x))`, and a generated subspace that is closed under the Hilbert-space limits
  used in Section 2.2. Its RH-direction approximants have real coefficients for real positive
  `epsilon`.
- Lean theorem names: `baezDuarteKernel_source_formula`, `baezDuarteRealPartLp_ofReal`,
  `baezDuarteRealPartLp_complex_smul_kernel`, `baezDuarteOfRealLp_maps_real_span`,
  `baezDuarteRealPartLp_maps_complex_span`,
  `baezDuarteComplexTarget_mem_closure_iff_real`, and
  `baezDuarteComplexTarget_mem_closure_iff_fullLineConcreteApprox`.
- `assumption_frontier_after`: the published positive-natural closure side is represented exactly
  in both real and complex `L2(0,infinity)`, and both are equivalent to the source-aligned
  positive-tolerance predicate.
- `hard_gap_after`: fixed node M0 is complete. M1/G1, D, and RH remain open.
- `hard_gap_delta`: M0 closed after all parameter, domain, target, generated-closure, endpoint,
  tolerance, kernel-formula, and coefficient-field requirements received direct source and Lean
  evidence.
- detailed completion record: `research/m0_completion_audit_20260710.md`
- decision: `ADVANCE` to fixed node M1. The only eligible criterion carrier is
  `baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure`, with the real closure and
  full-line concrete predicate available as compiled equivalents.
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed without warnings.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs.
- full project proof-gap keyword scan: passed with no matches.
- `git diff --check`: passed.
- commit SHA: resolve the commit titled `research: complete Baez-Duarte statement alignment`; the
  exact SHA is recorded in the external task ledger after the commit is created.

## Audit 2026-07-10-M1-01: Baez-Duarte proof dependency boundary

- `loop_id`: `AUDIT-20260710-M1-01`
- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- expected `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- exact mathematical target: connect `Mathlib.RiemannHypothesis` to the zero-free-half-plane
  hypothesis used by Baez-Duarte's quoted Balazard-Saias lemma, and audit every remaining theorem
  dependency in both directions of Theorem 1.1 against current mathlib APIs.
- primary source: Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann
  Hypothesis*, arXiv `math/0202141`, Theorem 1.1 and Section 2. The proof uses a quantitative
  Mobius partial-sum estimate, a Fourier-Mellin isometry, the Mellin transform of the
  fractional-part kernel, dominated convergence, and the base Nyman-Beurling criterion.
- `assumption_frontier_before`: the exact complex closure side is compiled, but no implication in
  either direction with `Mathlib.RiemannHypothesis` is formalized.
- `hard_gap_before`: G1 and G2 are open; it is not yet known which paper dependencies are already
  available in mathlib and which require new theorem-level formalization.
- expected `hard_gap_delta`: replace the broad G2 inventory with an evidence-backed dependency
  boundary and compile the RH-to-zero-free-half-plane interface. Do not claim G1 or RH progress.
- batch justification: the RH assumption conversion and complete proof-dependency inventory are
  one clean-context entry audit for fixed node M1.
- model: GPT-5 Codex
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: clean continuation after M0 completion; current worktree, fixed DAG, primary
  paper, exact RH definition, Mellin/Fourier files, and Mobius L-series files were inspected before
  registration.
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- compiled theorem: `RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re`; for
  `1/2 <= alpha < re(s)`, RH implies `riemannZeta s != 0`.
- available infrastructure: `mellin`, `mellin_eq_fourier`, Fourier `Lp` Plancherel,
  `Lp.compMeasurePreserving`, the Mobius arithmetic function, and Mobius L-series inversion on
  `re(s) > 1`.
- missing forward blocks: the Balazard-Saias quantitative Mobius estimate near `re(s)=1/2`, the
  RH-to-Lindelof bound used after equation (2.8), the fractional-kernel Mellin identity, a packaged
  weighted-log Fourier-Mellin `L2` isometry, and the two source-specific convergence arguments.
- missing reverse block: the base Nyman-Beurling criterion; the classical proof uses a half-plane
  Hardy space and inner/outer invariant-subspace factorization not found in the pinned mathlib
  tree.
- `assumption_frontier_after`: the RH premise now reaches the exact zero-free premise of the quoted
  estimate, but the estimate itself and the base criterion remain unavailable.
- `hard_gap_after`: G2 is in progress with explicit forward and reverse theorem boundaries. G1,
  D, and RH remain open.
- `hard_gap_delta`: dependency uncertainty reduced; no criterion implication was proved.
- detailed audit: `research/m1_baez_duarte_dependency_audit_20260710.md`
- decision: search external Lean projects for the two heavy dependencies. If absent, batch the
  literature-stable fractional-kernel Mellin identity with the weighted-log `L2` isometry before
  attempting the quantitative Mobius estimate.
- Lean verification: `lake env lean LeanLab/Riemann/Basic.lean` passed without warnings.
- Lean verification: `lake env lean LeanLab/Riemann/NymanBeurling.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/Targets.lean` passed.
- Lean verification: `lake env lean LeanLab/Riemann/TargetChecks.lean` passed.
- Lean verification: `lake build` passed with 8566 jobs.
- full project proof-gap keyword scan: passed with no matches.
- `git diff --check`: passed.
- commit SHA: resolve the commit titled `research: audit Baez-Duarte proof dependencies`; the exact
  SHA is recorded in the external task ledger after the commit is created.

## Batch 2026-07-10-M1-02: fractional-kernel Mellin identity

- `loop_id`: `BATCH-20260710-M1-02`
- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- expected `result_class`: `HARD_GAP_REDUCED`
- exact mathematical target: for `0 < re(s) < 1`, prove as a convergent Mellin transform that
  `M[rho(1/x)](s) = -zeta(s)/s`, then include the adjacent scaling to every kernel
  `rho(1/(n*x))` with positive natural `n`.
- primary source: Baez-Duarte, arXiv `math/0202141v2`, source lines 226-245; the paper attributes
  the identity to Titchmarsh (2.1.5).
- source artifact: `https://export.arxiv.org/e-print/math/0202141`, SHA-256
  `3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.
- `assumption_frontier_before`: Audit M1-01 listed the kernel Mellin identity as one of five
  missing forward blocks. No implication of the published criterion was available.
- `hard_gap_before`: G2 lacked the source transform needed to convert finite kernel sums into zeta
  and Dirichlet-polynomial expressions on vertical lines.
- expected `hard_gap_delta`: remove exactly the fractional-kernel Mellin block if the full
  `HasMellin` statement and trusted-dependency audit pass.
- batch justification: Abel continuation, the split at one, reciprocal change of variables,
  convergence, and positive-natural scaling are one source analytic edge. The weighted-log `L2`
  isometry remains a separate batch.
- model: GPT-5 Codex family; exact backend identifier not exposed
- reasoning effort: not exposed by the current runtime
- budget: no explicit per-round token budget
- compaction state: resumed from a generated context summary and re-audited the fixed DAG, current
  worktree, primary source, mathlib APIs, external repositories, and attempt ledger.
- external search result: no Lean implementation was found for Nyman-Beurling, Baez-Duarte,
  Balazard-Saias, or the critical-strip Mobius estimate. `EulerProducts` stops in the absolute
  convergence region. `PrimeNumberTheoremAnd` contains an Abel-continuation implementation but
  its full repository also contains unrelated unfinished files.
- dependency decision: vendor only the 13-module Apache-2.0 Abel-continuation source subset from
  `PrimeNumberTheoremAnd` commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`; do not add the full
  repository as a package dependency.
- compatibility result: all 13 modules compile individually and as a Lake library against this
  project's pinned Lean 4.31/mathlib `v4.31.0`.
- theorem names: `riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos`,
  `mellinConvergent_complexFractionalPart_neg`, `mellin_complexFractionalPart_neg_eq`,
  `hasMellin_fractionalPartKernel_one`, and `hasMellin_baezDuarteKernel`.
- trusted-dependency result: the upstream Abel theorem, the positive-half-plane extension, and
  both final kernel theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- `result_class`: `HARD_GAP_REDUCED`
- `assumption_frontier_after`: the transform identity and all positive-natural scalings are
  unconditional compiled theorems; no unproved analytic statement is used as a premise.
- `hard_gap_after`: G2 no longer lists the fractional-kernel Mellin identity. The quantitative
  Mobius estimate, RH-to-Lindelof bound, weighted-log `L2` isometry, source convergence, and base
  reverse criterion remain open.
- `hard_gap_delta`: one fixed external analytic block closed; neither direction of the full
  criterion, G1, D, nor RH is proved.
- detailed record: `research/m1_fractional_kernel_mellin_20260710.md`
- Lean verification: `LeanLab.Riemann.BaezDuarteMellin`, exact typed witnesses, and
  `LeanLab.Riemann.AxiomsAudit` pass; full `lake build` passes with 8581 jobs.
- source audit: incomplete-proof keyword and explicit `axiom` declaration scans have no matches;
  all 13 vendored Lean modules are byte-identical to the audited upstream commit.
- `git diff --check`: passed.
- commit SHA: resolve the commit titled `research: formalize Baez-Duarte Mellin identity`; the
  exact SHA is recorded in the external task ledger after creation.

## Batch 2026-07-11-M1-03: weighted-log Fourier-Mellin L2 isometry

- `loop_id`: `BATCH-20260711-M1-03`
- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- exact target: package `U(f)(u) = exp(-u/2) f(exp(-u))` as an invertible complex-linear isometry
  `L2(0,infinity) -> L2(real line)`, expose the inverse representative
  `x^(-1/2) g(-log x)`, compose with Fourier Plancherel, and verify frequency `tau/(2*pi)`.
- source: Baez-Duarte, arXiv `math/0202141v2`, source lines 226-245; inspected source SHA-256
  `3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.
- first design finding: equality of the two square-norm integrals alone was insufficient because
  `Lp` is a quotient by almost-everywhere equality. Linearity also required proving that
  `u -> exp(-u)` pulls positive-half-line null sets back to real-line null sets.
- successful measure route: prove `expNeg_quasiMeasurePreserving` from the one-dimensional
  Jacobian formula applied to indicators. This allowed `Lp.coeFn_add` and `Lp.coeFn_smul` to be
  pulled through the logarithmic parametrization without selecting unchecked representatives.
- automation failure: `fun_prop` did not unfold the new `expNeg` definition and initially timed
  out inside the zero-integral proof. Explicit derivative, measurability, and indicator-product
  proofs compiled quickly and were retained.
- inverse design: internally use `exp(-log(x)/2)` because both inverse laws simplify directly by
  `log_exp` and `exp_add`; convert to the source-facing `x^(-1/2)` only in the final positive-axis
  representative theorem via `Real.rpow_def_of_pos`.
- packaging route: construct `weightedLogForwardLinearIsometry`, prove surjectivity with the
  explicit inverse candidate, then use `LinearIsometryEquiv.ofSurjective`. This avoids assuming an
  inverse linear map before its quotient-level well-definedness is established.
- theorem names: `expNeg_quasiMeasurePreserving`, `eLpNorm_weightedLogForwardFun`,
  `eLpNorm_weightedLogInverseFun`, `weightedLogForwardLinearIsometry`,
  `weightedLogForward_inverse`, `weightedLogPullback`, `weightedLogPullback_coeFn`,
  `weightedLogPullback_symm_coeFn`, `baezDuarteFourierMellinL2`, and
  `mellin_criticalLine_eq_fourier`.
- `result_class`: `HARD_GAP_REDUCED`
- `assumption_frontier_after`: the full weighted-log equivalence and Fourier composition are
  unconditional Lean objects; no theorem about Mobius growth, Lindelof, convergence of the paper's
  approximants, the base criterion, or RH was assumed.
- `hard_gap_after`: remove the packaged weighted-log Fourier-Mellin `L2` isometry from G2. Keep the
  Balazard-Saias quantitative Mobius estimate, RH-to-Lindelof bound, source-specific convergence,
  and reverse base Nyman-Beurling criterion open.
- verification: full `lake build` passed with 8582 jobs; exact `TargetChecks` witnesses passed;
  trusted dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; incomplete-proof
  keyword scan, explicit `axiom` scan, and `git diff --check` passed.
- compaction state: this batch resumed from a compacted summary and rechecked the fixed DAG,
  source formula, current worktree, and relevant mathlib APIs before preregistration.
- model: GPT-5 Codex family; exact backend identifier and reasoning effort are not exposed.
- budget: no explicit per-round token budget.
- detailed record: `research/m1_weighted_log_fourier_mellin_20260711.md`.

## Batch 2026-07-11-M1-04: source convergence boundary

- `loop_id`: `BATCH-20260711-M1-04`
- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- exact target: prove `L2(R)` membership of the source power majorant for exponent below `1/2`,
  then audit both Section 2.2 convergence passages down to their exact source dependencies.
- source: Baez-Duarte, arXiv `math/0202141v2`, Section 2.2; source-export SHA-256
  `3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.
- compiled majorant result: `baezDuarteVerticalMajorant_memLp`; the specialization
  `baezDuarteFirstConvergenceMajorant_memLp` gives the source range `epsilon < 1/4`.
- compiled exceptional-set results: critical-line zeta-zero ordinates are countable and have
  volume zero, using mathlib's discreteness theorem for `riemannZetaZeros`.
- compiled pointwise result: away from those ordinates, continuity of `riemannZeta` proves the
  epsilon-dependent zeta ratio tends to one; hence `ae_tendsto_baezDuarteZetaRatio_one`.
- failed full-convergence route: a generic dominated-convergence invocation cannot start without
  the source's uniform estimates. For fixed epsilon these require the Balazard-Saias Mobius
  estimate and RH-to-Lindelof growth; for epsilon tending to zero they require Lemma 2.2's uniform
  zeta-ratio estimate and a complex-Gamma vertical-strip ratio bound not found in mathlib.
- remaining shared edge: the weighted-to-unweighted full-line `L2` transfer on `(0,1)` and
  `(1,infinity)` is source-specific and not yet formalized.
- source-risk finding: the TeX proof of Lemma 2.2 displays an identical Gamma numerator and
  denominator; the tail passage also has an exponent inconsistent with the surrounding
  `f_(2*epsilon,n)` indexing. Neither printed expression was assumed.
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `assumption_frontier_after`: majorant integrability and almost-everywhere ratio convergence are
  unconditional Lean theorems; all remaining quantitative premises are explicit and unchecked.
- `hard_gap_after`: G2 and both directions of Theorem 1.1 remain open; the broad convergence block
  is replaced by named dependencies F1-F3 in `research/hard_gap_dag.md`.
- trusted dependencies: representative final theorems use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- detailed record: `research/m1_source_convergence_boundary_20260711.md`.

## Batch 2026-07-11-M1-05: weighted-to-unweighted tail transfer

- `loop_id`: `BATCH-20260711-M1-05`
- `node_id`: `M1`
- `gap_id`: `G2/F3`
- `work_class`: `FORMALIZATION`
- source reconstruction: from the definition of `f_(delta,n)`, every kernel equals `1/(a*x)` for
  `x>1`, so the tail coefficient exponent is `1+delta`. Lean theorem
  `baezDuarteMobiusApprox_two_mul_eq_dirichletTail_of_one_lt` verifies `1+2*epsilon` for
  `f_(2*epsilon,n)`; the source's printed `1+epsilon` is a typo.
- exact analytic result: for actual real `L2(0,infinity)` elements satisfying
  `w(x)=x^(-epsilon)f(x)` almost everywhere and `f(x)=m/x` above one,
  `baezDuarte_weightedTail_norm_sq_le` proves
  `norm(f)^2 <= (1+2*epsilon)*norm(w)^2`.
- proof route: split the positive half-line into `Ioc 0 1` and `Ioi 1`; on the first interval the
  weight is at least one; on the second interval compute the weighted tail integral exactly as
  `m^2/(1+2*epsilon)` and the unweighted tail integral as `m^2`.
- convergence result: `tendsto_norm_zero_of_baezDuarte_weightedTail` handles varying
  `epsilon_i -> 0`; fixed epsilon is the constant-family case.
- source instantiation: `baezDuarte_finsupp_norm_sq_le_of_weighted` applies the theorem to the
  project's actual positive-natural finite kernel sum and compiled reciprocal-moment tail.
- rejected weaker stopping point: the batch did not stop after the tail integral or a generic raw
  function lemma; it reached quotient-level `Lp`, convergence, and source finite-sum witnesses as
  required by preregistration.
- `result_class`: `HARD_GAP_REDUCED`
- `assumption_frontier_after`: no independent tail-transfer premise remains. F1/F2 must still
  provide weighted convergence; the transfer back to ordinary `L2` is compiled.
- `hard_gap_after`: remove F3 from G2. F1, F2, the reverse base criterion, G1, D, and RH remain open.
- trusted dependencies: representative final theorems use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- detailed record: `research/m1_weighted_tail_transfer_20260711.md`.

## Batch 2026-07-11-M1-06: Baez-Duarte zeta-ratio bound

- `loop_id`: `BATCH-20260711-M1-06`
- `node_id`: `M1`
- `gap_id`: `G2/F2`
- `work_class`: `FORMALIZATION`
- exact target: reconstruct Baez-Duarte Lemma 2.2's malformed Gamma display, prove a uniform
  zeta-ratio bound on a fixed positive epsilon interval, and expose one epsilon-independent `L2`
  majorant for the transformed quotients.
- source correction: the functional equation requires
  `pi^(-epsilon) * |Gamma(1/4+epsilon/2+i*tau/2) /
  Gamma(1/4-epsilon/2+i*tau/2)|`; the source display with identical numerator and denominator was
  not assumed.
- external audit: `PrimeNumberTheoremAnd` commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393` contains an Apache-2.0 digamma-series theorem giving
  logarithmic vertical-strip growth. The exact file was vendored unchanged; SHA-256
  `815c1f1507058efbef756eb955e055267d5c78eb577d3a6a45d52da3ad6778a4`.
- rejected alternative: AINTLIB commit `f190f93db1b51b73a99051f358eb0b45ea45ad80` has compatible
  Gamma strip bounds, but the repository exposes no license and its polynomial losses are too
  large for this convergence argument. No AINTLIB code was copied or imported.
- proof route: apply continuous Gronwall to
  `u -> Gamma(z+u)/Gamma(z)` using the digamma bound; prove zeta and completed-Gamma conjugation;
  use the completed-zeta functional equation; isolate the `pi^(-epsilon)` factor; and handle zeta
  denominator zeros separately, where Lean division is zero.
- sharpness decision: Gronwall yields exponent `C*epsilon`, not the source's sharp coefficient one.
  Set `epsilon0 = 1/(8*(C+1))`; Lean verifies `C*epsilon0 < 1/2`, so the weaker estimate still
  supplies the required `L2` domination.
- compiled final theorems: `exists_norm_Gamma_div_le_rpow_of_re_mem_Icc`,
  `exists_norm_baezDuarteZetaRatio_le_rpow`, `exists_baezDuarteZetaRatio_bound`, and
  `exists_baezDuarteZetaRatioIntegrand_majorant`.
- `result_class`: `HARD_GAP_REDUCED`
- `assumption_frontier_after`: F2 is unconditional Lean code, including the uniform ratio bound
  and a fixed `MemLp` majorant. No unproved Gamma asymptotic or malformed source statement remains
  as a premise.
- `hard_gap_after`: remove F2 from G2. F1, the reverse base criterion, G1, D, and RH remain open.
- verification: the source module, exact target witnesses, and axiom audit pass; full `lake build`
  passes with 8586 jobs; incomplete-proof and explicit-declaration scans, upstream identity check,
  and `git diff --check` pass. Trusted dependencies are only `propext`, `Classical.choice`, and
  `Quot.sound`.
- model: Codex, GPT-5 family; exact backend identifier and reasoning effort are not exposed.
- budget: unbounded persistent-goal budget; no explicit per-round token budget.
- compaction state: this batch resumed from a generated context summary after the Gamma-ratio
  theorem and conjugation lemmas had compiled; the fixed DAG, preregistration, worktree, and exact
  file state were rechecked before continuing.
- detailed record: `research/m1_zeta_ratio_digamma_20260711.md`.

## Audit 2026-07-11-M1-07: corrected F1 route

- `loop_id`: `AUDIT-20260711-M1-07`
- `node_id`: `M1`
- `gap_id`: `G2/F1`
- `work_class`: `AUDIT`
- exact target: determine the weakest published dependency chain for the remaining fixed-epsilon
  convergence block and select the first honest theorem target.
- source comparison: Baez-Duarte `math/0202141v2` uses Balazard-Saias plus RH-to-Lindelof; Burnol
  `math/0202166v1`, Theorem 1.4 and Section 2, replaces Lindelof by the unconditional critical-line
  bound `|zeta(1/2+it)|=O(|t|^(1/4))`.
- integrability calculation: the transformed truncation error is bounded by
  `N^(-epsilon/3)*|s|^theta*|zeta(s)/s|`, hence by a constant times
  `N^(-epsilon/3)*|t|^(-3/4+theta)`; its square is integrable for `theta<1/4`.
- external Lean result: no Balazard-Saias implementation was found. The audited Apache-2.0
  `PrimeNumberTheoremAnd/RiemannZetaConvexity.lean` compiles but proves only an exponent-one linear
  strip bound, which is insufficient. An unlicensed public exploration leaves the required
  weighted Phragmen-Lindelof interpolation as an explicit axiom; no code was reused.
- selected next theorem: an unconditional critical-line zeta bound with any exponent below `1/2`,
  for example `3/8`. It requires genuine polynomial-boundary Phragmen-Lindelof interpolation and
  sharp enough Gamma boundary control.
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `assumption_frontier_after`: RH-to-Lindelof is removed from the chosen published route. F1 now
  consists exactly of the unconditional zeta convexity bound plus Balazard-Saias.
- `hard_gap_after`: F1 remains open; F2/F3 stay closed; the reverse base criterion, G1, D, and RH
  remain open.
- model: Codex, GPT-5 family; exact backend identifier and reasoning effort are not exposed.
- budget: unbounded persistent-goal budget; no explicit per-round token budget.
- compaction state: compaction occurred after the source audit and initial documentation edits,
  before final verification. The continuation summary was checked against the worktree, fixed DAG,
  and preregistration before work resumed.
- verification: full `lake build` passes with 8586 jobs; incomplete-proof and explicit-declaration
  scans and `git diff --check` pass. No Lean source file changed in this audit.
- detailed record: `research/m1_f1_route_audit_20260711.md`.

## Batch 2026-07-11-M1-08: zeta convexity boundary closure

- `loop_id`: `BATCH-20260711-M1-08`
- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- preregistered target: an unconditional critical-line zeta bound with exponent `3/8`.
- compiled progress: entire pole removal; Abel `1/8` right-edge bound; exact Gamma reflection and
  cosine cancellation; zeta `5/8` left-edge bound; pole-removed boundary powers `9/8` and `13/8`.
- stopped dependency: the corrected Fiori midpoint quotient and its uniform interior growth
  witness for `PhragmenLindelof.vertical_strip` remain to be formalized.
- rejected shortcut: no invalid `re(s)`-dependent auxiliary function and no axiom for weighted
  interpolation or growth was introduced.
- `result_class`: `FORMALIZATION_ONLY`
- `hard_gap_before`: F1 contains zeta convexity plus Balazard-Saias.
- `hard_gap_after`: unchanged; the fixed `3/8` theorem is not compiled.
- `hard_gap_delta`: none.
- `assumption_frontier_after`: both polynomial edge estimates are compiled; midpoint interpolation
  and interior growth remain explicit open obligations.
- model: Codex, GPT-5 family; exact backend identifier and reasoning effort are not exposed.
- budget: unbounded persistent-goal budget; no explicit per-round token budget.
- compaction state: resumed from a generated context summary after preregistration and rechecked
  the fixed DAG, sources, and worktree before continuing.
- detailed record: `research/m1_zeta_convexity_boundary_20260711.md`.

## Batch 2026-07-11-M1-09: corrected zeta convexity midpoint

- `loop_id`: `BATCH-20260711-M1-09`
- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- fixed target: unconditional critical-line zeta exponent `3/8`.
- compiled result: `exists_norm_riemannZeta_criticalLine_le_rpow` proves the exact target.
- route: extend the `13/8` and `9/8` edge bounds over compact segments; formalize Fiori's
  holomorphic reflection and `(13,9)` quotient; prove both edge bounds; use the audited global
  finite-order theorem to discharge `PhragmenLindelof.vertical_strip`; take a sixteenth root and
  divide by the pole-removal factor.
- upstream reuse: 11 Apache-2.0 modules from `PrimeNumberTheoremAnd` commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393` were vendored unchanged. Exact hashes are in the
  detailed record.
- invalid route excluded: no `re(s)`-dependent auxiliary function and no growth/interpolation
  axiom.
- `result_class`: `HARD_GAP_REDUCED`
- `hard_gap_before`: zeta convexity and Balazard-Saias both remain inside F1.
- `hard_gap_after`: zeta convexity is closed; Balazard-Saias remains, so F1 itself stays open.
- `hard_gap_delta`: remove only `G2/F1/zeta-convexity`.
- `assumption_frontier_after`: unconditional `3/8` theorem compiled; Balazard-Saias is not assumed.
- trusted dependencies: representative upstream, growth, midpoint, and final theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- verification: full build passed with 8599 jobs; exact target witness, incomplete-proof scan,
  explicit-declaration scan, upstream hash identity, and `git diff --check` passed.
- model: Codex, GPT-5 family; exact backend identifier and reasoning effort are not exposed.
- budget: unbounded persistent-goal budget; no explicit per-round token budget.
- compaction state: none during this batch.
- detailed record: `research/m1_zeta_convexity_midpoint_20260711.md`.
