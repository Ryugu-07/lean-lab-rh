# H1 Bettin--Gonek Inverse Mellin Convolution Campaign

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-BETTIN-GONEK-INVERSE-MELLIN-CONVOLUTION-01`

Selected node: `H1-BETTIN-GONEK-INVERSE-MELLIN-CONVOLUTION-01`

Status: `PUBLIC_IMPLEMENTATION_GREEN / EVIDENCE_CI_PENDING`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H1 inverse Mellin/convolution, H12 Levinson--Montgomery analytic counts, H2 actual-zeta bow exclusion, and H7 weak-regularity explicit-formula transport under the omission-seeking historical policy. | H1 has a fixed source paragraph whose two ends are already actual compiled objects. H7 is the strongest reserve, H12 remains broad, and H2 lacks an identified arithmetic amplifier. | Select the H1 equations `(2.2)`--`(2.4)` bridge. |
| `SOURCE_RECONSTRUCTION` | Read the primary TeX for arXiv:1604.02740 and isolated the standalone `G_t` decay, inverse Mellin support/bound, convolution identity, and truncated integral estimate. | The paper compresses three analytically nontrivial operations into one paragraph: line movement to zero and infinity, support recovery, and Mellin-product convolution. | Require all three operations and the resulting bound in one campaign. |
| `PRIOR_ATTEMPT_AUDIT` | Compared the fixed endpoint with the compiled H1 Mellin and J-contour campaigns. | The prior contour estimate controls `G_t H_t` only after exact zeta cancellation. It does not imply any standalone `G_t` decay, inverse Mellin support, or Fubini identity. | Record the substantive re-entry difference and prohibit rational-kernel substitution. |
| `API_AUDIT` | Inspected the actual auxiliary, mollifier Mellin, J-line, zeta-growth, rectangle-contour, improper-integral, and Fubini interfaces. | The project has the endpoint objects and finite-rectangle machinery, but no identified generic inverse-Mellin convolution theorem. The difficult source line is `Re(w)=0`, where the zeta argument has real part `-1/2`. | Fix a source-specific direct proof and an explicit analytic-interface failure outcome. |
| `PREREGISTRATION` | Fixed standalone `G_t` decay/integrability, support and boundedness of the literal inverse Mellin kernel, the actual convolution identity, and the interval upper bound. | Production Lean editing remains closed until this docs-only preregistration passes public CI. | Commit only the preregistration ledger, push, and require public Lean Action CI. |
| `PRODUCTION_GATE` | Published preregistration commit `3acbaa32aa7cdcf9303adb38976d213e5057967f`. | Public Lean Action run `30181383630`, build job `89738396880`, passed in `1m35s`. | Open production editing and attack standalone `G_t` decay first. |
| `LEFT_BOUNDARY_DECAY` | Expanded the literal `G_t` on `Re(w)=0`, used the zeta functional equation and the compiled Gamma/cosine estimates, and derived an explicit inverse-cube majorant in `1+|Im(w)+t|`. | The actual auxiliary factor is absolutely integrable on the zero line without cancelling against `H_t`; no source mismatch occurred. | Prove the real-part-three boundary and propagate the estimate across the fixed strip. |
| `FIXED_STRIP` | Multiplied by `(w+it+1)^3`, verified the Phragmen--Lindelof boundary and growth premises, and divided the lift back on `0<=Re(w)<=3`. | Lean proves uniform `O(|Im(w)+t|^-3)` decay, stronger than the source's required exponent `5/2`, and absolute integrability on both source lines. | Shift the inverse-Mellin line from three to zero. |
| `LEFT_LINE_SHIFT` | Built finite rectangles, proved both horizontal integrals vanish from the fixed-strip majorant, and identified the line-three and line-zero inverse-Mellin integrals for `0<u<=1`. | The literal kernel has an explicit nonnegative finite bound independent of `u` on `0<u<=1`. | Establish arbitrary-right estimates for support. |
| `RIGHT_LINE_SHIFT` | Proved one majorant uniform over every `Re(w)=R>=3`, integrability on each right line, finite shifts from three to `R`, and decay of the normalized line integral as `R->+infinity` when `u>1`. | Lean proves `bettinGonekInverseMellinKernel rho t u=0` for every `u>1`; a fixed finite rectangle was not used as a substitute for the limit. | Attack the actual convolution by product-space Fubini. |
| `DIRECT_FUBINI` | Defined the source double integrand, proved exact norm factorization into the weighted mollifier and `G_t`, established product measurability and integrability, swapped the Bochner integrals, and used the positive-real complex-power quotient identity. | Lean identifies the inner mollifier integral with the compiled `H_t`, cancels through the existing exact `G_t H_t=JKernel` theorem, and proves equation `(2.4)` with the correct `1/(2*pi)` normalization. | Use support and boundedness to derive the source upper estimate. |
| `SUPPORT_CUTOFF_AND_BOUND` | Split `Ioi 1` as `Ioc 1 x` union `Ioi x`, killed the tail with the compiled support theorem, proved local integrability of the actual log mollifier norm, and applied the kernel bound pointwise. | The exact preregistered `Icc 1 x` upper bound for `2<=x` compiles. Endpoint conventions are justified by the zero measure of the singleton. | Package the fixed endpoint and run output gates. |
| `CERTIFICATE_AND_REGISTRATION` | Packaged decay, all right-line integrability, product Fubini, support, boundedness, convolution, and the final estimate in `bettinGonekInverseMellinConvolution_endpoint`; added one proven Target, an exact TargetCheck, and selected axiom prints. | The production module, Targets, exact TargetChecks, and AxiomsAudit compile. Selected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. | Run forbidden scans, patch check, and the full build before freezing implementation. |
| `LOCAL_MECHANICAL_GATES` | Ran direct warning-as-error compilation, the three forbidden scans, `git diff --check`, and the complete project build. | The production source is diagnostic-free; all forbidden scans and the patch check are empty; `lake build` passes `8760/8760`. | Freeze the implementation commit, push, and require independent public Lean Action CI. |

## Local result

- `decision`: `FULL_INVERSE_MELLIN_SUCCESS` locally, with all mechanical gates green.
- `source_file`: `LeanLab/Riemann/BettinGonekInverseMellinConvolution.lean`.
- `aggregate`: `bettinGonekInverseMellinConvolution_endpoint`.
- `source_alignment`: no support-direction, branch, convolution-orientation, or `2*pi`
  normalization mismatch was found.
- `hard_gap_before`: standalone `G_t` inversion, support/boundedness of `g_t`, and actual
  convolution `(2.4)` were absent from the formal H1 chain.
- `hard_gap_after`: the next uncompiled H1 source edge is Cauchy--Schwarz plus the critical-line
  zeta second-moment transfer, integration in `t`, and uniform asymptotic bookkeeping.
- `hard_gap_delta`: `0` for RH; `source_analytic_bridge_delta=1`.
- `assumption_frontier_before`: no inverse-Mellin support, boundedness, or convolution theorem
  was available as an unconditional premise.
- `assumption_frontier_after`: those source statements are compiled unconditionally for every
  actual nontrivial zero; no moment estimate, Farmer conjecture, H1, or RH premise was added.
- `public_implementation`: frozen commit `b99a10f3b0543587c1aacdd992e88b28ea9f35e5`
  passed Lean Action run `30183853748`, build job `89744990702`, in `2m24s`.

## Claim boundary

No Cauchy--Schwarz moment transfer, zeta second-moment lower bound, uniform integration in `t`,
Farmer arbitrary-length moment conjecture, H1, or RH is assumed or proved.

Closing or obstructing this fixed endpoint will not exhaust Bettin--Gonek, the mollifier family,
or H1. H7 weak-regularity transport, H12 analytic counts, H2 arithmetic localization, original
conjectures, falsification, and direct RH attacks remain eligible in later route selection.
