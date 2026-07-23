# H1 Bettin--Gonek Mellin Identity Campaign

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`

Selected node: `H1-BETTIN-GONEK-H-MELLIN-IDENTITY-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `SOURCE_AUDIT` | Re-read Bettin--Gonek equations `(2.1)`--`(2.5)` and compared their real-cutoff mollifier with `farmerMollifier`. | The cutoff, taper, Mobius coefficient, and critical-line argument align. Mathlib Mellin parameter is `1-w`. | Test the exact kernel and reciprocal-zeta dependencies. |
| `INFRASTRUCTURE_AUDIT` | Searched project and pinned Mathlib for logarithmic improper integrals, Mellin transforms, and the Mobius L-series. | `integral_Ioi_log_pow_mul_cpow_neg_sub_one` supplies the kernel at unit scale; `LSeries_moebius_eq_reciprocal_riemannZeta` supplies the final Dirichlet series. | Select the sum-integral interchange as the real proof edge. |
| `ADVERSARIAL_TEST` | Checked the source exponent after scaling one term. | The term is `mu(n) n^(1-w-s)/(w-1)^2`; summability requires `Re(w+s-1)>1`, exactly `Re(w)>3/2` on the critical line. No extra `x<=1` term is allowed because the mollifier is zero there. | Preregister the complete source identity, not a kernel-only theorem. |
| `PREREGISTRATION` | Fixed the actual pointwise cutoff identity, scaled kernel, absolute interchange, reciprocal-zeta identification, and `HasMellin` endpoint. | Production Lean remains gated on public preregistration CI. | Commit, push, and require public CI before proof-source editing. |

## Open obstacles

- Prove the floor-cutoff finite sum equals the source-supported infinite sum pointwise.
- Produce a summable norm majorant strong enough for Bochner sum-integral exchange.
- Control complex-power scaling without changing the source exponent or branch convention.
- Keep the Mellin parameter `1-w` and the source zeta argument `w-1/2+it` definitionally aligned.

## Claim boundary

No Mellin identity is yet registered as proven. Inverse Mellin support, auxiliary decay, contour
shift, selected-residue extraction, moment-to-power transfer, Farmer's conjecture, and RH remain
open.
