# H9 Riesz Mellin Boundary Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-RIESZ-MELLIN-BOUNDARY-01`

Selected node: `H9-RIESZ-EXPONENTIAL-MELLIN-BOUNDARY-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Selection rationale

The Redheffer characteristic-polynomial endpoint is publicly closed. Fresh selection compares
its open non-unit-root estimates with H1's arbitrary-length moment, H2's actual-zeta bow
exclusion, H7's ground-state limit, H8's all-index hyperbolicity, H10's geometric or
regularized-trace transfer, H11's sparse-exception amplifier, and H12's global count contour.
None of those comparisons supplied a new source-backed premise.

The classical Riesz exponential-smoothing criterion is absent from the repository even though
the project already has the Mobius L-series, reciprocal zeta, Gamma integrals, and a general
sum-to-Mellin theorem. More importantly, a modern peer-reviewed source states the ordinary
Mellin integral on a region wider than its zero-end convergence domain. This campaign therefore
tests a concrete possible human omission: distinguish the literal integral from its analytic
continuation and expose the exact strip on which the RH argument may safely begin.

This is not numerical optimization and does not assume the RH-equivalent Riesz decay. It is a
source reconstruction with a falsifiable domain claim.

## Primary-source anchors

Marcel Riesz, *Sur l'hypothese de Riemann*, Acta Mathematica 40 (1916), 185--190, introduced the
entire Riesz function. In modern normalization,

```text
P_2(x) = sum_{n>=1} mu(n) / n^2 * exp(-x/n^2)
R(x) = x * P_2(x),
```

and RH is equivalent to

```text
P_2(x) = O_epsilon(x^(-3/4+epsilon)).
```

Archit Agarwal, Meghali Garg, and Bibekananda Maji,
*Riesz-type criteria for the Riemann hypothesis*, Proc. Amer. Math. Soc. 150 (2022),
5151--5163, DOI `10.1090/proc/16064`, arXiv `2202.00637`, records:

- equations `(1.5)` and `(1.8)`: the Riesz decay and its general `P_k` form;
- Lemma 2.4: the displayed Mellin identity
  `integral x^(-s-1) P_k(x) dx = Gamma(-s)/zeta(2s+k)`;
- equation `(3.31)`: the product form used in the reverse implication.

For `k=2`, the source states Lemma 2.4 on `-1/2<Re(s)<1`, excluding `s=0`. Its proof first
obtains the literal integral identity for `Re(s)<0` and then invokes analytic continuation.
Because `P_2(0)=1/zeta(2) != 0`, the ordinary integral cannot converge at the zero endpoint when
`Re(s)>=0`. The campaign must distinguish these two meanings.

Sources:

- `https://archive.ymsc.tsinghua.edu.cn/pacm_paperurl/20170108203031601228270`;
- `https://arxiv.org/abs/2202.00637`;
- `https://doi.org/10.1090/proc/16064`.

## Exact fixed endpoint

Use the actual arithmetic Mobius function and real exponential, with a complex-valued kernel.
The implementation must prove all of the following.

1. Define the `n`th `k=2` Riesz term and
   `rieszTwoKernel x = sum' n, mu(n)/n^2 * exp(-x/n^2)`, with the `n=0` term exactly zero.
2. Prove absolute summability for every nonnegative `x`, and enough local uniform convergence to
   obtain continuity on a neighborhood of zero and local integrability on `(0,infinity)`.
3. Prove the exact zero value
   `rieszTwoKernel 0 = (riemannZeta 2)^-1` and its nonvanishing.
4. For source parameter `s` with `-1/2<Re(s)<0`, prove convergence of the ordinary Mellin
   integral and the exact product identity

   ```text
   riemannZeta (2*s+2) * mellin rieszTwoKernel (-s) = Gamma (-s).
   ```

   The proof must use justified absolute sum-integral interchange and may not divide by zeta
   outside its proved nonvanishing half-plane.
5. Prove a literal-domain falsification witness:

   ```text
   ¬ MellinConvergent rieszTwoKernel (-1/2).
   ```

   This is the source parameter `s=1/2`, which lies in the wider displayed region of Lemma 2.4
   but whose zero-end integrand has norm comparable to `x^(-3/2)`.
6. Define an explicit conditional decay interface
   `rieszTwoKernel =O[atTop] (fun x => x^(-a))`. From it, prove Mellin convergence and
   differentiability for every source parameter satisfying `-a<Re(s)<0`.
7. Compile exact checks for the zero value, both Mellin-strip inequalities, the divergence
   witness parameter, and the mapping `q=2*s+2` from the base strip to `Re(q)>1`.

The primary Target must aggregate the exact base-strip identity, the zero-end divergence
witness, and the conditional holomorphic-extension interface. A definition-only result,
finite approximation, or identity assumed as a hypothesis does not satisfy the endpoint.

## Proposed Lean surface

Names may change only to match project style; their mathematical content may not weaken.

```lean
def rieszTwoSeriesTerm (x : ℝ) (n : ℕ) : ℂ := ...

def rieszTwoKernel (x : ℝ) : ℂ :=
  ∑' n, rieszTwoSeriesTerm x n

theorem rieszTwoKernel_zero :
    rieszTwoKernel 0 = (riemannZeta 2)⁻¹ := ...

theorem rieszTwoKernel_zero_ne_zero :
    rieszTwoKernel 0 ≠ 0 := ...

theorem rieszTwo_mellin_identity
    {s : ℂ} (hleft : -(1 / 2 : ℝ) < s.re) (hright : s.re < 0) :
    riemannZeta (2 * s + 2) * mellin rieszTwoKernel (-s) =
      Complex.Gamma (-s) := ...

theorem not_mellinConvergent_rieszTwo_neg_half :
    ¬ MellinConvergent rieszTwoKernel (-(1 / 2 : ℂ)) := ...

theorem rieszTwo_mellin_differentiableAt_of_decay
    {a : ℝ}
    (hdecay : rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a)))
    {s : ℂ} (hleft : -a < s.re) (hright : s.re < 0) :
    DifferentiableAt ℂ (mellin rieszTwoKernel) (-s) := ...
```

The final syntax must use Lean's actual `Prop`, asymptotic, coercion, and Mellin APIs.

## Intended proof route

1. Reuse `ArithmeticFunction.LSeriesSummable_moebius_iff` at exponent two for the kernel
   majorant.
2. Reuse Mathlib's `hasSum_mellin` with coefficient `mu(n)/n^2`, frequency `1/n^2`, and Mellin
   variable `-s`.
3. Normalize its output to the Mobius L-series at `2*s+2`, then use the already compiled
   `LSeries_moebius_eq_reciprocal_riemannZeta` only where `1<Re(2*s+2)`.
4. Obtain the zero value from the same absolutely convergent Mobius L-series and prove local
   nonvanishing by continuity.
5. Refute convergence at Mellin parameter `-1/2` by lower-bounding the integrand norm near zero
   with a positive constant times `x^(-3/2)` and applying the exact rpow integrability
   criterion.
6. Use `mellinConvergent_of_isBigO_rpow` and
   `mellin_differentiableAt_of_isBigO_rpow` for the conditional enlarged strip. The near-zero
   input must be proved from continuity; it may not be postulated.

## Falsification tests

- `LITERAL_VERSUS_CONTINUATION`: never rewrite an analytically continued value as the ordinary
  integral where `MellinConvergent` fails.
- `ZERO_ENDPOINT`: `P_2(0)=1/zeta(2)` is nonzero; any claimed zero-end cancellation is false.
- `STRIP_SIGNS`: source parameter `s` corresponds to Mathlib Mellin parameter `-s`.
- `DIRICHLET_EXPONENT`: the Mobius L-series exponent is exactly `2*s+2`.
- `NAT_ZERO`: the source starts at `n=1`; the Lean `n=0` term must be definitionally or
  provably zero before division or positivity arguments.
- `K_TWO_ONLY`: do not import the `k=1` Hardy--Littlewood kernel, whose defining series has a
  different conditional-convergence/PNT boundary.
- `DECAY_NOT_PROVED`: `O(x^(-3/4+epsilon))` remains an explicit hypothesis in this campaign.
- `NO_ZERO_FREE_SMUGGLING`: no zeta nonvanishing theorem may be used below `Re=1`.
- `CRITERION_SURVIVES_AUDIT`: the literal-domain correction alone does not refute the Riesz RH
  equivalence; the reverse proof can start from the corrected base strip and continue left.

## Success and classification

Success requires every fixed endpoint, one proven aggregate Target, exact TargetChecks, selected
transitive axiom prints with standard axioms only, empty forbidden scans, warning-as-error
compilation, full build, and all public CI gates.

Expected classification:

- `result=RIESZ_TWO_MELLIN_LITERAL_STRIP_CORRECTED`;
- `historical_route_coverage_delta=1`;
- `source_domain_correction_delta=1`;
- `mobius_exponential_interface_delta=1`;
- `conditional_mellin_extension_delta=1`;
- `riesz_decay_delta=0`;
- `zero_free_identity_continuation_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

If the exact base-strip identity or the divergence witness cannot be compiled, record the
strongest theorem and exact obstruction as `PARTIAL / BLOCKER_EXPOSED`; do not relabel an
assumed identity or a finite approximation as success.

## Production and stopping gates

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI.

The local campaign stops when the fixed endpoint is proved, falsified, or reduced to a precise
Mathlib or mathematical obstruction. A successful endpoint returns to fresh route selection
before deciding whether to attack the conditional identity continuation and zero-free consumer.
Local STOP does not close the Riesz route, H9, or the active RH Goal.

## Local implementation result

The docs-only preregistration commit
`2a0f1dbbb894f107b5a4c4c8a5e9f1f5837a9811` passed public Lean Action run
`30210947076`, build job `89816945706`, in `1m37s`, opening the production gate.

The 490-line module `LeanLab/Riemann/RieszMellinBoundary.lean` now proves every fixed endpoint:

- absolute convergence and continuity of the actual `k=2` Mobius-exponential kernel;
- `rieszTwoKernel 0 = (riemannZeta 2)⁻¹` and nonvanishing;
- the unconditional bound `P_2(x)=O(x^-a)` for every `0<=a<1/2`;
- ordinary Mellin convergence and
  `zeta(2*s+2) * mellin P_2(-s) = Gamma(-s)` on `-1/2<Re(s)<0`;
- `¬ MellinConvergent P_2 (-1/2)`;
- convergence and differentiability on `-a<Re(s)<0` from an explicit `O(x^-a)` hypothesis.

One proven aggregate Target, four exact TargetChecks, and eight selected axiom prints compile.
Every selected axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`; the
new module's forbidden scan is empty, `git diff --check` passes, and the full build passes
`8773/8773`.

Classification is
`result=RIESZ_TWO_MELLIN_LITERAL_STRIP_CORRECTED`,
`historical_route_coverage_delta=1`, `source_domain_correction_delta=1`,
`mobius_exponential_interface_delta=1`, `conditional_mellin_extension_delta=1`,
`riesz_decay_delta=0`, `zero_free_identity_continuation_delta=0`, `hard_gap_delta=0`,
and `rh_frontier_delta=0`.

The next gate is a frozen implementation commit and public CI. After immutable evidence and a
final ledger, local STOP returns to fresh route selection; the Riesz decay criterion and
zero-free continuation remain open.

## Frozen implementation

Implementation commit `096aea939d27fb6828b702296c156bbef4ba1559` passed public Lean Action
run `30212146718`, build job `89820083261`, in `2m25s`. The 490-line production module, proven
Target, four exact TargetChecks, and eight selected standard-only axiom prints are frozen at
that hash.

The next gate is a docs-only immutable-evidence commit and public CI. No `LeanLab/` file may
change between the frozen implementation and immutable evidence. The Riesz decay, identity
continuation, zero exclusion, H9, and RH remain open.

Docs-only immutable-evidence commit `5448bd74cdf55a8ead8847f6c7cd50e21e8711e7` passed public
Lean Action run `30212403937`, build job `89820745802`, in `1m39s`. There is no `LeanLab/`
difference between the frozen implementation and evidence commits.

The next gate is one docs-only final ledger and its public CI. It closes only the literal Mellin
boundary endpoint; the Riesz decay, analytic continuation consumer, zeta zero exclusion, H9,
and RH remain open.
