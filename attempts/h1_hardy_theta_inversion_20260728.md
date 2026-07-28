# H1 Hardy Theta-Inversion Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H1-HARDY-THETA-INVERSION-01`

Node: `H1-HARDY-THETA-INVERSION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `MEANINGFUL_MELLIN_INVERSION_PARTIAL /
IMPLEMENTATION_AND_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_PENDING`

## Fixed target

Reconstruct Hardy's 1914 positive-real Cahen--Mellin equation (1) from the project's actual
Riemann xi normalization and Mathlib's actual theta functional-equation pair. Full success also
requires analytic continuation to the complex alpha strip and Hardy's equation (2).

## Attempt log

| phase | action | compiled result | decision |
| --- | --- | --- | --- |
| `SOURCE_ALIGNMENT` | Locked Hardy 1914 pages 1012--1014 and the exact `Xi(2t)/(1/4+4t^2)` normalization. | The source theta is Mathlib `evenKernel 0 x`; project `hardyXi` is the source `Xi`. | Preserve every scalar and scale. |
| `VERTICAL_INTEGRABILITY` | Used the compiled de Bruijn--Newman Fourier representation to bound `hardyXi(2t)` by the `L1` mass of `Phi`. Solved the project xi definition for the completed Mellin transform. | `verticalIntegrable_hardyCompletedMellin` compiles with an integrable rational majorant. | Enter positive-real Mellin inversion. |
| `FMODIF_AUDIT` | Tested continuity of Mathlib `WeakFEPair.f_modif` at `x=1`. | It is piecewise: `theta-1` above one, `theta-x^(-1/2)` below one, and zero at one. The preregistered claim that both pole terms are simultaneously present was false. | Exclude `x=1` for raw `f_modif` inversion and reconstruct the elementary pole kernel separately. |
| `POSITIVE_REAL_INVERSION` | Applied Mathlib's Mellin inversion theorem using the exact strong functional-equation pair. | `hardyMellinInv_eq_f_modif` compiles for `x>0`, `x!=1`. | Isolate the rational correction. |
| `POLE_KERNEL` | Defined the lower cutoff plus its reciprocal `x^(-1/2)` branch, proved its Mellin transform is `1/s+1/(1/2-s)`, and inverted it independently. | On `Re(s)=1/4`, the transform is exactly `2/(1/4+4t^2)`; `hardyPoleMellinInv_eq_kernel` compiles. | Subtract the two inverse transforms. |
| `CAHEN_EQUATION` | Proved phase-weighted integrability, split the inverse integrals, and restored both source pole terms. | `hardyCahenMellinInversion` proves equation (1) for every positive real `x`, including `x=1` by dominated continuity. | Attack A and Attack B are complete. |
| `ATTACK_C_FIRST_EDGE` | Tried to promote the real identity to `x=exp(i*alpha)` by strip analyticity. | The exact first missing theorem is the compact-substrip exponential integrability statement below. The current uniform xi bound only gives rational decay and cannot dominate `exp(a*|t|)`. | Stop at the preregistered meaningful-partial boundary; re-entry must prove actual xi exponential decay in this normalization. |
| `REGISTRATION` | Added one aggregate certificate and Target, exact checks, and selected transitive axiom prints. | Selected theorems use only `propext`, `Classical.choice`, and `Quot.sound`. | Run the remaining mechanical and public gates. |
| `LOCAL_AUDIT` | Ran warning-as-error compilation, three forbidden scans, patch check, and the full build. | Scans are empty; `git diff --check` passes; full build passes `8781/8781`. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed implementation `8b687aa46d67a049680a7cf964ce8e982f325afa`. | Run `30378958429`, job `90341715211`, passed in `2m29s`. | Keep all proof sources frozen and publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC_CI` | Published docs-only evidence at `189ac653a5e3b04bc49f639d80d9e8dd0614f515`. | Run `30379288299`, job `90342851859`, passed in `1m48s`; its `LeanLab/` diff from the frozen implementation is empty. | Publish one docs-only final ledger, then return to cross-family route selection. |

## Strongest compiled facts

- `norm_hardyXi_two_mul_le_phiMass`
- `verticalIntegrable_hardyCompletedMellin`
- `hardyMellinInv_eq_f_modif`
- `hardyPoleMellinInv_eq_kernel`
- `hardyXiPositiveRealIntegral_eq_pole_sub_f_modif`
- `hardyCahenMellinInversion`
- `hardyThetaInversion_endpoint`

The source-readable endpoint is:

```text
for x>0,
  1 + x^(-1/2)
    - (1/(2*pi)) * integral_R
        x^(-(1/4+i*t)) * 4*Xi(2*t)/(1/4+4*t^2) dt
  = Theta(pi*x).
```

This is exactly Hardy equation (1), since the displayed integral coefficient is
`(2/pi)` times the full-line integral with numerator `Xi(2t)`.

## Source-normalization correction

The preregistration's M0 item 5 said Mathlib `f_modif` equals
`Theta(pi*x)-1-x^(-1/2)` pointwise. It does not. The library chooses one subtraction on each
side of one so that the Mellin transform is entire:

```text
x>1:  f_modif(x) = Theta(pi*x)-1
0<x<1: f_modif(x) = Theta(pi*x)-x^(-1/2)
x=1:  f_modif(1) = 0.
```

The source formula is nevertheless unchanged. The independently compiled pole kernel contributes
the missing branch, and the two auxiliary discontinuities cancel in the final equation.

## First open Attack C theorem

The next theorem is recorded in theorem-shaped form but is not declared as a Lean theorem:

```lean
theorem integrable_hardyXiInterior_compactSubstrip
    {a : Real} (ha : 0 <= a) (haStrip : a < Real.pi / 2) :
    Integrable
      (fun t : Real =>
        Real.exp (a * |t|) *
          norm (hardyXi (2 * t) : Complex) /
            (1 / 4 + 4 * t ^ 2))
```

This is the first reusable domination statement needed for
`analyticOnNhd_hardyXiInteriorIntegral`. The current compiled uniform bound for xi proves only
`C/(1+t^2)` integrability. It does not prove the exponential margin. Re-entry should derive the
source-normalized Gamma decay, likely by combining the existing critical-line zeta growth bound
with a two-sided exact Gamma bound, before attempting termwise complex differentiation.

## Result boundary

- `result_class`: `MEANINGFUL_MELLIN_INVERSION_PARTIAL /
  SOURCE_NORMALIZATION_CORRECTION`
- `historical_route_coverage_delta`: `1`
- `hardy_equation_one_delta`: `1`
- `library_semantics_correction_delta`: `1`
- `strip_analyticity_delta`: `0`
- `hardy_equation_two_delta`: `0`
- `hard_gap_delta`: `0`
- `rh_frontier_delta`: `0`

No complex-strip equation (2), tangential Abel limit, all-order moment law, unconditional
critical-line infinitude theorem, positive-proportion theorem, H1, or RH is proved.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary after preregistration public CI; current
  governance, worktree protections, primary-source normalization, Mellin APIs, and the existing
  Hardy consumer were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
- `frozen_implementation`: `8b687aa46d67a049680a7cf964ce8e982f325afa`, public-green on
  run `30378958429`, job `90341715211`, in `2m29s`.
- `immutable_evidence`: `189ac653a5e3b04bc49f639d80d9e8dd0614f515`, public-green on
  run `30379288299`, job `90342851859`, in `1m48s`; its `LeanLab/` diff from the frozen
  implementation is empty.
