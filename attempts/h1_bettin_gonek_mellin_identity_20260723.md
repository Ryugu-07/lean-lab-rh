# H1 Bettin--Gonek Mellin Identity Campaign

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-MELLIN-IDENTITY-01`

Selected node: `H1-BETTIN-GONEK-H-MELLIN-IDENTITY-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `SOURCE_AUDIT` | Re-read Bettin--Gonek equations `(2.1)`--`(2.5)` and compared their real-cutoff mollifier with `farmerMollifier`. | The cutoff, taper, Mobius coefficient, and critical-line argument align. Mathlib Mellin parameter is `1-w`. | Test the exact kernel and reciprocal-zeta dependencies. |
| `INFRASTRUCTURE_AUDIT` | Searched project and pinned Mathlib for logarithmic improper integrals, Mellin transforms, and the Mobius L-series. | `integral_Ioi_log_pow_mul_cpow_neg_sub_one` supplies the kernel at unit scale; `LSeries_moebius_eq_reciprocal_riemannZeta` supplies the final Dirichlet series. | Select the sum-integral interchange as the real proof edge. |
| `ADVERSARIAL_TEST` | Checked the source exponent after scaling one term. | The term is `mu(n) n^(1-w-s)/(w-1)^2`; summability requires `Re(w+s-1)>1`, exactly `Re(w)>3/2` on the critical line. No extra `x<=1` term is allowed because the mollifier is zero there. | Preregister the complete source identity, not a kernel-only theorem. |
| `PREREGISTRATION` | Fixed the actual pointwise cutoff identity, scaled kernel, absolute interchange, reciprocal-zeta identification, and `HasMellin` endpoint. | Production Lean remains gated on public preregistration CI. | Commit, push, and require public CI before proof-source editing. |
| `PREREGISTRATION_CI` | Published the fixed endpoint before creating production proof source. | Commit `3dfe6e96bbbb57474aa241630a3624c4ed290b3d` passed run `29974255134`, job `89102575415`, in `1m49s`. | Open the production gate. |
| `REAL_CUTOFF` | Expanded the existing `farmerMollifier` after multiplying by `log x`, then compared the floor sum with supported terms over all naturals. | The finite and pointwise `tsum` source formulas compile. The `n=0`, `x<1`, and `x=1` cases contribute zero exactly. | Prove the one-term improper integral. |
| `SCALED_KERNEL` | Applied the positive-real substitution `x=n*u` to the logarithmic kernel and tracked principal complex powers. | Integrability and `n^(1-w)/(w-1)^2` compile for `Re(w)>1`. | Establish an absolute integrated-norm majorant. |
| `ABSOLUTE_FUBINI` | Computed the exact kernel norm integral and bounded the critical-line Mobius coefficient by `n^(-1/2)`. | The majorant is `n^(1/2-Re(w))/(Re(w)-1)^2`, summable for exactly `Re(w)>3/2`. A Tonelli argument proves integrability of the pointwise `tsum`; the Bochner sum-integral exchange compiles. | Identify the resulting L-series. |
| `RECIPROCAL_ZETA` | Rewrote each integrated source term at exponent `w+s-1` and invoked the compiled Mobius L-series theorem. | The integral equals `zeta(w-1/2+i*t)^(-1)/(w-1)^2`; the source denominator normalization is algebraically identical because zeta is nonzero in this half-plane. | Package Mellin convergence and source `H_t`. |
| `ENDPOINT` | Proved `MellinConvergent`, `HasMellin`, `bettinGonekH_eq`, and the aggregate endpoint. | `FULL_SUCCESS_AT_MELLIN_ENDPOINT` holds locally. Twelve exact TargetChecks and nine selected standard-only axiom prints pass. | Complete scans, full build, and public implementation/evidence/ledger gates. |
| `LOCAL_GATES` | Recompiled production and registries, scanned forbidden tokens, checked the diff, audited selected axioms, and built the complete project. | The production scan is empty, `git diff --check` passes, and the 8,755-job full build succeeds with inherited replay warnings only. | Freeze and publish the implementation commit. |
| `IMPLEMENTATION_CI` | Published the frozen implementation and required a clean public rebuild. | Commit `1ca590891a51da76712e8a2dd177287de56d0b43` passed run `29976558428`, job `89109449098`, in `2m6s`. Proof source is frozen. | Publish immutable evidence without changing Lean source. |

## Resolved local obstacles

- The floor-cutoff finite sum equals the source-supported infinite sum pointwise, including the
  integer boundary.
- The exact integrated-norm majorant is summable and supports Bochner sum-integral exchange.
- Positive-real complex-power scaling preserves the source exponent and branch convention.
- The Mellin parameter `1-w` and zeta argument `w-1/2+it` are algebraically aligned in Lean.

## Remaining route obstacles

- Construct the inverse Mellin object `g_t` and prove the source support and boundedness claims.
- Prove sufficient vertical decay for the regularized auxiliary `G_t`.
- Justify the contour shift and selected-residue lower bound with uniform constants.
- Complete the moment-to-power transfer and prove, rather than assume, Farmer's arbitrary-length
  mollified moment conjecture.

## Claim boundary

The Mellin identity is compiled, registered as a proven Target, and public-green at the frozen
implementation commit. Immutable evidence and final-ledger CI remain for campaign closure.
Inverse Mellin support, auxiliary decay, contour shift, selected-residue extraction,
moment-to-power transfer, Farmer's conjecture, and RH remain open.
