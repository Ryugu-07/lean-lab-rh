# H12 Levinson--Montgomery Global Count Re-entry

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Status: `STEPS_1_7_COMPILED / PUBLIC_IMPLEMENTATION_GREEN /
IMMUTABLE_EVIDENCE_CI_REQUIRED / CAMPAIGN_ACTIVE`

## Attempt log

| step | mode | result | next action |
| --- | --- | --- | --- |
| 1 | `PARENT_CLOSURE` | Actual top-side argument variations for `zeta` and `zeta'` are publicly closed at commit `08ab39cf512b7820a7c78f5fd87425486566e633`. The global indented count remains open. | Rerank across historical families without adjacency preference. |
| 2 | `CROSS_FAMILY_SELECTION` | H1/H2 require deep moments or density estimates; H7/H8 lack actual spectral producers; H10 lacks source-ready general-curve Riemann--Roch infrastructure; H11 lacks actual PCC/Fujii error or sparse amplification; H14 lacks certified global root-count input. H12 now has actual inputs surrounding one precise source-logic gap. | Select `H12-LM-GLOBAL-INDENTED-COUNT-01`. |
| 3 | `OMISSION_AUDIT` | The negative integer-height predicate is conditional only at nonzero points. An interior zero should be impossible because its positive real principal part immediately to the right contradicts strict negativity. This implication is not yet formalized. | Freeze punctured positive-right control and actual zero exclusion. |
| 4 | `MATERIAL_REENTRY` | The prior common-bottom attack failed because nonvanishing does not imply zero winding. The new attack instead uses the source-generated strict-negative branch, the compiled principal-log winding theorem, and the newly compiled actual top `O(log(t+2))` bounds. | Retain the complete count theorem as endpoint. |
| 5 | `PREREGISTRATION` | Full success is `levinsonMontgomeryTheoremOne_actual`; the negative-height geometry is only the first fixed segment. Meaningful partial requires three materially different attacks on the first global theorem that remains unavailable after the geometry compiles. | Publish docs-only preregistration and await public CI. |
| 6 | `PUNCTURED_ZERO_FACTOR` | General actual-zeta factorization with positive analytic multiplicity compiles. The residual logarithmic derivative is bounded near the zero, while the principal term is strictly positive immediately to the right. | Apply it only at punctured nonzero points. |
| 7 | `NEGATIVE_HEIGHT_GEOMETRY` | Strict negativity on every nonzero point excludes every interior zeta zero, then excludes derivative zeros and produces actual negative top geometry. The source integer-height alternative now compiles to negative geometry or the existing dense branch. | Enter the finite argument principle. |
| 8 | `FINITE_FACTORIZATION_ATTACK_1` | A first compact-divisor factorization failed because Mathlib's zero extraction gives an equality on a connected open neighborhood, not automatically on the whole compact rectangle. Treating the compact and open domains as identical would be invalid. | Prove a two-domain extraction theorem. |
| 9 | `FINITE_FACTORIZATION_ATTACK_2` | `AnalyticOnNhd.extract_zeros_eqOn_openSubset` compiles: divisor support is finite on a larger compact `K`, while the exact factorization is used only on a connected open `V` with the contour in `V` and `V subset K`. | Divide the finite zero polynomial and integrate the residual. |
| 10 | `FINITE_ARGUMENT_PRINCIPLE` | A multiplicity-aware finite rectangle argument principle compiles generically and for actual `zeta` and `zeta'`. Divisor values are identified with the project's existing multiplicities, not just support cardinalities. | Align the open-left count convention. |
| 11 | `ADAPTIVE_CUTOFF_ATTACK` | Direct critical-line indentation bookkeeping is unnecessary for this finite count identity. Local finiteness selects a common `r<1/2` to the right of every divisor support point whose real part is strictly below `1/2`; this preserves all open-left zeros and excludes critical-line zeros by a proved filter stabilization. | Split compact counts at the lower height. |
| 12 | `GLOBAL_COUNT_IDENTITY` | `levinsonMontgomery_globalCountDifference_actual` compiles. It expresses the difference of actual zeta-derivative and zeta rectangle integrals as the change in the multiplicity-bearing global Speiser count difference between `b` and `n`. | Attack `LevinsonMontgomeryLogCountBound`. |
| 13 | `LOG_COUNT_ATTACK_1` | Expanding the rectangle identity and taking imaginary parts uses the compiled `O(log(t+2))` top integrals and fixed-bottom terms, but leaves the real parts of both logarithmic-derivative integrals on both vertical sides. No repository theorem presently bounds or cancels these terms. | Isolate the vertical obstruction in theorem-shaped form and test a logarithmic-modulus endpoint formula. |
| 14 | `PUBLIC_IMPLEMENTATION` | Frozen implementation `87b06e0c258b5fbc8f141a7242ce0ac8ae9ac4dc` passed Lean Action run `30645129522`, build job `91204516436`, in `2m43s`. | Publish docs-only immutable evidence; keep the campaign active at step 8. |

## Current obstruction map

1. `CLOSED`: general zeta zero factorization and positive-right logarithmic-derivative control.
2. `CLOSED`: actual negative-height zero/derivative exclusion and geometry-or-dense dichotomy.
3. `CLOSED`: finite multiplicity-aware rectangle argument principle for actual `zeta` and
   `zeta'`.
4. `CLOSED`: adaptive common cutoff, open-left filter stabilization, and exact global count
   difference at negative integer heights.
5. `OPEN`: express and control the real parts of the left/right vertical logarithmic-derivative
   integrals. The natural candidate is a zero-free logarithmic-modulus endpoint identity, with
   explicit treatment of the adaptive side and the line `Re(s)=0`.
6. `OPEN`: transfer the resulting logarithmic count estimate from admissible integer heights to
   every sufficiently large real cutoff without assuming a new zero-density theorem.
7. `OPEN`: derive the exact-count sequence in the negative branch and combine it with the compiled
   dense branch.

## Assumption frontier

Open and forbidden as premises: `LevinsonMontgomeryLogCountBound`,
`LevinsonMontgomeryCountDichotomy`, `SpeiserDerivativeZeroFree`, RH, and any equivalent
zero-free or count theorem.

The project may prove any of them directly. Every intermediate result must compile without
`sorry`, pass the selected axiom audit, and retain actual multiplicities.

## Omission-sensitive finding

The source presentation emphasizes indentations around critical-line zeros. For the finite
open-left count identity, a different exact mechanism is available: compact divisor support is
finite, so one can choose a vertical side `r<1/2` beyond every support point that is genuinely
left of the critical line. Lean then proves that filtering the compact divisor by `Re(s)<r`
equals filtering it by `Re(s)<1/2`. This is not a claim that indentation is globally redundant;
it is a compiled replacement for this particular count-bookkeeping step.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary; governance, current Targets, preceding
  attempts, hard-gap DAG, public Git state, actual theorem signatures, and the 1974 source hinge
  were rechecked before selection.
- `global_goal`: active.
- `protected_files`: inherited protected files remain untouched and unstaged.
