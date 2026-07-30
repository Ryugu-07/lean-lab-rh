# Route Selection after H12 Jensen Top Zero Count

Date: 2026-07-30

Status: `H12_TOP_ARGUMENT_VARIATION_SELECTED`

## Governing selection rule

Historical coverage is omission search, not checklist completion. The selected node should
reconstruct a proof chain close enough to a claimed theorem that an omitted premise, an
unnecessarily strong hypothesis, a discarded branch, or a reusable cross-route lemma can be
identified. Original conjectures, falsification, and direct RH attacks remain open at every
selection.

Adjacency is not a reason to continue a route. Reentry is allowed only when the preceding
campaign materially changed the first live edge.

## Closed parent

Campaign
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`
is publicly closed at closure-ledger commit
`eab0fafd0e21101a759e9ccb20c1ba3b2ea4494a`, Lean Action run `30531096109`,
build job `90833363620`, in `2m3s`.

It proves multiplicity-bearing `O(log(t+2))` Jensen divisor counts for the actual zeta and
phase-normalized actual zeta derivative symmetrizations, together with inclusion of every
source real-part crossing on `[0,1]`. It does not convert those crossings into a continuous
change of argument.

## Cross-family comparison

| family | first live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood / Selberg / Levinson--Conrey | Prove the uniform eta remainder without an extra `abs(s)` loss, Selberg global moments, or an arbitrary-length mollified moment. | Central historical producers, but the present boundaries require deep global estimates rather than an unexpanded local inference. | Retain open. |
| H2 density / Maynard--Pratt | Prove the literal short-Mobius twisted fourth moment at length `T^(1/100)`. | The exact producer is isolated, and three plausible short proofs have already retained a positive power loss. | Park until a coefficient-`L2` or shifted-convolution input appears. |
| H7 spectral / Connes | Prove the actual prolate Rayleigh-excess-to-ground-gap rate, or bypass the tiny cluster by a separated commuting label. | A genuine possible repair exists, but neither the needed source rate nor a concrete joint-spectral theorem is currently available. | Retain open. |
| H8 entire-function / RKHS | Construct the concrete Conrey--Li half-strip Hardy space and actual-xi multiplier. | The abstract consumer compiles; the missing concrete object is broad and presently absent. | Retain open. |
| H10 function fields | Lift the rational polar realization to a general curve using one-point pole filtrations and Riemann--Roch. | Historically successful mathematics, but the required algebraic-geometric producer is much larger than the current local bridge. | Retain open. |
| H11 zero statistics | Instantiate the fixed-compact PCC remainder and carry the slow window through Fejer/Fujii, then amplify sparse exceptions. | The quantifier bridge compiles; the actual analytic asymptotics and sparse-exception mechanism remain open. | Retain open. |
| H12 Levinson--Montgomery | Convert the newly compiled actual crossing support and divisor sums into continuous top-side argument variation. | Page 52 calls this a standard consequence of Jensen without recording the branch, partition, endpoint, or multiplicity-to-cardinality steps. The preceding campaign has newly supplied the exact actual producer needed here. | **Select.** |

## Primary-source hinge

Levinson--Montgomery 1974, page 52, states that, by a standard use of Jensen's theorem, the
changes in argument of `zeta(sigma+i*t)` and `zeta'(sigma+i*t)` from `sigma=1` to
`sigma=0` are `O(log t)`.

Primary source:

`https://doi.org/10.1007/BF02392141`

The paper suppresses the passage from zeros of a real-part symmetrization to a single-valued
continuous argument change. That passage is the selected omission-sensitive hinge.

## Why the boundary changed

Before the parent campaign, an argument-variation proof would have ended at an assumed
crossing count. The project now has, for the actual functions:

1. finite multiplicity-bearing divisor support on a fixed Jensen ball;
2. `O(log(t+2))` divisor sums;
3. pointwise inclusion of every real crossing on `[0,1]`;
4. the necessary derivative phase normalization.

The remaining theorem is therefore a bounded topological/analytic conversion with an actual
source instantiation, not another estimate of the same constants.

## Fixed next campaign

- `campaign`:
  `LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-TOP-ARGUMENT-VARIATION-01`.
- `node`: `H12-LM-JENSEN-TOP-VARIATION-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `endpoint`: for cofinally many common zero-free actual top heights, prove that the
  imaginary parts of the horizontal integrals of `zeta'/zeta` and `zeta''/zeta'` on
  `[0,1]` are each `O(log(t+2))`.
- `core_bridge`: a nonvanishing differentiable complex path whose real-part zeros are
  contained in a finite set has continuous argument variation at most
  `pi * (card crossings + 1)`.
- `actual_charge`: map every crossing into the real projection of the corresponding Jensen
  divisor support, then bound support cardinality by the nonnegative multiplicity sum.
- `negative_controls`: no global use of principal `Complex.arg`; no omission of top-height
  nonvanishing; no count of support points as multiplicity; no phase omission for `zeta'`;
  no abstract crossing theorem presented as the actual source endpoint.
- `strict_boundary`: the global indented argument principle, bottom orientation for the exact
  branch, both Levinson--Montgomery count identities, Speiser, H12, and RH remain separate.
- `production_gate`: no `LeanLab/` or registration edit before docs-only preregistration
  passes public Lean Action CI.

The persistent RH Goal remains active.
