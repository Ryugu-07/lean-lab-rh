# H12 Speiser Admissible-Contour Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Node: `H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `MEANINGFUL_PARTIAL / SOURCE_DEPENDENCY_SPLIT /
IMPLEMENTATION_AND_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_PENDING`

## Fixed target

Replace Levinson--Montgomery's low-zero-table bottom sign with a fixed common zero-free
horizontal segment, construct cofinal admissible top segments, and attempt the actual indented
argument-principle proof of their Theorem 1 for the project's multiplicity-bearing counts.

Full and meaningful-partial criteria are fixed in
`research/h12_speiser_admissible_contour_prereg_20260728.md`.

## Attempt log

| phase | action | compiled result | decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H1 mollifiers, H2 density, H7 spectral, H10 function fields, H11 statistics, H12 Speiser, and H13 transfer after the H1 Hardy closure. | H12 has a source-exact global count theorem, four compiled local inputs, and an untested weakening of the source's numerical bottom premise. | Select H12. |
| `SOURCE_ALIGNMENT` | Rechecked Levinson--Montgomery 1974 Theorem 1 and section 2 against the project count predicates. | The source uses `t=10` plus low-zero information to obtain a signed lower boundary; the asymptotic contour comparison can instead test a fixed common zero-free bottom contribution. | Preregister the replacement; no production edit before public CI. |
| `PREREGISTRATION_PUBLIC_CI` | Published docs-only preregistration `519dde1d49919491fa2d10dfa4e80ee30df7f10a`. | Run `30381170428`, job `90349104858`, passed in `1m31s`. | Open production editing for the fixed target. |
| `COMMON_SLICES` | Projected the actual compact zeta and derivative zero sets to their finite sets of bad imaginary parts. | `exists_speiserCommonZeroFreeHorizontal_between` gives a common closed zero-free segment in every positive-height interval; `exists_speiserCommonZeroFreeHorizontal_above` gives cofinal segments. | Enter the fixed-bottom integral. |
| `FIXED_BOTTOM` | Used actual analyticity and nonvanishing to prove continuity of both composed logarithmic derivatives. | Both interval-integrability theorems and `exists_speiserFixedBottomLogDerivBound` compile. The selected bottom contributes one fixed nonnegative constant. | Recheck exactly where the source uses bottom sign. |
| `SOURCE_DEPENDENCY_RECHECK` | Re-read section 2, especially the proof of equations `(1.1)` and `(1.2)`. | A fixed bounded bottom suffices for the `O(log T)` count comparison. The exact-count branch instead uses strict left-half-plane containment of `zeta'/zeta` on the whole closed indented contour to force zero change of argument. | Split the preregistered mechanism. |
| `WINDING_FALSIFICATION` | Tested whether nonvanishing and matching endpoints force zero logarithmic winding. | `speiserNonzeroWindingModel` is everywhere nonzero, agrees at `0` and `1`, and `integral_logDeriv_speiserNonzeroWindingModel` is exactly `2*pi*I`. | Reject common nonvanishing as a replacement for the exact-count base orientation. |
| `REGISTRATION` | Added an aggregate Target, exact statement checks, and eight selected axiom prints. | Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. | Run the local mechanical gates. |
| `LOCAL_AUDIT` | Ran warning-as-error standalone compilation, three forbidden scans, `git diff --check`, and the full build. | Scans are empty; patch check passes; full build passes `8782/8782`. | Freeze and publish the meaningful partial. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed implementation `fbdb2462141e20b169d25eae58ed3c9ef67eb92b`. | Run `30382486593`, job `90353492533`, passed in `2m7s`. | Keep proof sources frozen and publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC_CI` | Published docs-only evidence `70b437177d7e990319e973bffc36053b413450c0` after verifying an empty `LeanLab/` diff from the frozen implementation. | Run `30382794033`, job `90354522762`, passed in `1m41s`. | Publish one docs-only final ledger; proof sources remain frozen. |

## Strongest compiled facts

- `finite_speiserCommonBadHeightSet`
- `exists_speiserCommonZeroFreeHorizontal_between`
- `exists_speiserCommonZeroFreeHorizontal_above`
- `intervalIntegrable_speiserZetaLogDeriv_horizontal`
- `intervalIntegrable_speiserZetaDerivLogDeriv_horizontal`
- `exists_speiserFixedBottomLogDerivBound`
- `integral_logDeriv_speiserNonzeroWindingModel`
- `speiserAdmissibleHorizontal_endpoint`

## Source-dependency correction

The preregistration proposed one weakening for both parts of Levinson--Montgomery Theorem 1.
The source recheck and compiled negative control show that this was too broad.

For equation `(1.1)`, replacing the signed `t=10` bottom by any fixed common zero-free bottom is
valid at the dependency level: its two logarithmic-derivative integrals are fixed constants and
can be absorbed into `O(log T)`.

For equation `(1.2)`, common nonvanishing is insufficient. The source uses
`Re(zeta'/zeta)<0` on every boundary piece so the ratio's image lies in the left half-plane and
has zero winding. A nonvanishing closed path can have nonzero winding, as the compiled
exponential model proves.

## First open global statements

The exact existing asymptotic target remains:

```lean
theorem levinsonMontgomeryLogCountBound_actual :
    LevinsonMontgomeryLogCountBound
```

Its first missing mechanism is the multiplicity-bearing indented argument principle together
with the Jensen `O(log T)` top-edge argument variation.

The exact additional base-orientation target for the source dichotomy can be stated as:

```lean
def LevinsonMontgomeryNegativeBottom : Prop :=
  ∃ b : Real, 0 < b ∧
    ∀ sigma : Real, sigma ∈ Set.Icc (0 : Real) (1 / 2) →
      (logDeriv riemannZeta (sigma + b * Complex.I)).re < 0
```

The source proves this at `b=10` using low-zero verification. A proof without an unformalized zero
table, or a different theorem forcing the same zero-winding base orientation, remains open.

## Result boundary

- `result_class`: `MEANINGFUL_PARTIAL / SOURCE_DEPENDENCY_SPLIT`
- `historical_route_coverage_delta`: `1`
- `common_admissible_horizontal_delta`: `1`
- `fixed_bottom_asymptotic_dependency_delta`: `1`
- `zero_winding_obstruction_delta`: `1`
- `levinson_montgomery_log_count_delta`: `0`
- `levinson_montgomery_dichotomy_delta`: `0`
- `hard_gap_delta`: `0`
- `rh_frontier_delta`: `0`

No global argument-principle count, Jensen top bound, negative bottom, count dichotomy, completed
Speiser equivalence, derivative-zero exclusion, or RH result is proved.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary during the parent H1 campaign; governing
  files and actual source/count definitions were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
- `production_module`: `LeanLab/Riemann/SpeiserAdmissibleContour.lean`, 270 lines.
- `local_build`: `8782/8782`.
- `frozen_implementation`: `fbdb2462141e20b169d25eae58ed3c9ef67eb92b`, public-green on
  run `30382486593`, job `90353492533`, in `2m7s`.
- `immutable_evidence`: `70b437177d7e990319e973bffc36053b413450c0`, public-green on run
  `30382794033`, job `90354522762`, in `1m41s`.
- `proof_freeze`: `git diff --exit-code fbdb2462141e20b169d25eae58ed3c9ef67eb92b --
  LeanLab` is empty before the immutable-evidence commit.
