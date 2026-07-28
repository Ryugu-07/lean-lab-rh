# Route Selection after H11 Triangular Pair Mass

Date: 2026-07-28

Status: `RERANK_COMPLETE / H1_HARDY_ABEL_MOMENT_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H11-TRIANGULAR-PAIR-MASS-01` is publicly closed at
final-ledger commit `650bd2656b71c4a25a830d77ef49971eb8af1fc4`, Lean Action run
`30333486822`, build job `90193405245`, in `2m0s`.

Its frozen Lean source proves the exact finite triangular pair-mass decomposition and exposes
horizontal analytic multiplicity without normalization loss. It does not prove Fujii's second
moment, PCC, an absolute sparse-exception estimate, direct zero exclusion, or RH.

## Fresh cross-family comparison

This rerank applies the user's omission-search priority: reconstruct historical arguments far
enough to detect discarded local or absolute information. Ease of producing another lemma and
optimization of an already sufficient numerical constant are not ranking criteria.

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy 1914 | Reconstruct equations (1)--(6): the theta/Mellin transform, Abel boundary moments, and high-moment sign contradiction. | The project has the real xi sign consumer but not Hardy's actual proof mechanism. Existing de Bruijn-Newman infrastructure already contains the same xi/theta normalization. | **Select.** |
| H1 mollifier | Prove Farmer's arbitrary-length mollified moment estimate. | The complete Bettin--Gonek conditional implication to RH is compiled. No new source input for the open estimate appeared. | Retain open. |
| H2 density/moments | Localize and exclude one actual off-line bow or sparse orbit. | Direct RH value, but the audited mean-value inputs still lose the required local information. | Retain open. |
| H7 spectral | Identify finite ground states with a true xi limiting object. | Finite matrix and Rayleigh-gap consumers are deep; the actual source data/convergence layer is still absent. | Retain open. |
| H9 Franel | Formalize ordered Farey discrepancy and its RH-equivalent estimate. | Historically important and still queued, but the immediately preceding H9 campaign already closed the exact Mobius transform. | Rotate away. |
| H10 function field | Transfer the finite Frobenius mechanism through actual curve/cohomology data. | High analogy value; the missing geometric layer remains broad. | Retain open. |
| H12 Speiser | Complete the global Levinson--Montgomery count. | Source-exact but already heavily reconstructed; no new global contour premise appeared. | Retain open. |

## Source finding that fixes the node

Hardy's 1914 note does not use the later textbook proof based on upper and lower integrals of
Hardy's `Z(t)`. It starts from Cahen's Mellin formula, shifts to the xi critical line, and derives
an exponential-weight transform for `Xi(2t)`. After `2p` differentiations and an Abel limit
`alpha -> pi/2` from below, the source obtains alternating even moments

```text
integral_0^infinity
  ((exp(pi*t/2) + exp(-pi*t/2)) * t^(2*p) * Xi(2*t))
    / (1/4 + 4*t^2) dt
  = (-1)^p * pi * cos(pi/8) / 4^(2*p).
```

The displayed boundary integral occurs only after an Abel-limit step under an eventual-sign
hypothesis. Treating it as an unconditional Lebesgue integral would erase the main convergence
issue. The selected Lean endpoint therefore keeps the interior family `|alpha| < pi/2` and its
one-sided limit explicit.

There is also an exact cross-route normalization already available:

```text
hardyXi(2*t) = 8 * deBruijnNewmanH 0 (4*t).
```

This follows from `deBruijnNewmanH_zero_eq_riemannXi` and identifies Hardy's `Xi(2t)` with the
existing H6 Fourier/theta object, rather than introducing a second xi convention.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01`.
- `node`: `H1-HARDY-ABEL-MOMENT-AMPLIFICATION-01`.
- `mode`: `LITERATURE`.
- `positive_endpoint`: exact H1/H6 normalization, source interior moment and Abel-law
  definitions, both eventual-sign contradictions, a zero above every height, and an infinite
  set of actual project `IsNontrivialZero` witnesses on the critical line, all conditional only
  on the source Abel moment law.
- `open_analytic_edge`: prove the Abel moment law itself from Hardy's Cahen-Mellin/theta formula
  and the project kernel. It may not be assumed as an unconditional theorem.
- `negative_controls`: no unconditional boundary integral, no abstract function detached from
  `riemannXi`, no single-parity argument, no missing factor from `Xi(2t)`, and no claim that
  Hardy's theorem or RH is unconditional.
- `strict_boundary`: the source Abel moment law, Hardy--Littlewood's quantitative count,
  positive critical-zero proportions, H1, and RH remain open.
- `production_gate`: no `LeanLab/` edit before this docs-only preregistration passes public
  Lean Action CI.
