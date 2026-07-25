# H7 Weil Finite Dictionary Admissibility Campaign

Date: 2026-07-24

Campaign: `LITERATURE-20260724-H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01`

Selected node: `H7-WEIL-FINITE-DICTIONARY-ADMISSIBILITY-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H7 finite-test admissibility, H1 inverse Mellin/convolution, H12 Speiser counting, H2 bow localization, H10 function-field transfer, and H11 sparse-exception amplification. | H7 has a newly compiled literal finite Fourier weight and a published exact zero-side consumer whose sole immediate missing hypothesis is source admissibility. This is a sharper omission test than another generic function-field polynomial lemma and has no numerical-optimization endpoint. | Select the source admissibility edge, with mandatory cross-route reranking after closure. |
| `SOURCE_RECONSTRUCTION` | Read arXiv:2607.02828, Lemma 2.2 and its proof in the original TeX. | Every finite even-sector vector is claimed admissible. Moment constraints are not required. The proof uses endpoint vanishing, continuity, piecewise smoothness, bounded variation of the zero-extended derivative, two integrations by parts, and a local zero count. | Correct the route map and freeze the literal assumptions. |
| `PROJECT_API_AUDIT` | Inspected the compact Laplace transform, `C^2` xi-divisor summability theorem, compact `C^6` arithmetic explicit formula, and the existing Volterra/Fourier source objects. | The project can already express the source-to-Laplace affine coordinate and has a reciprocal-square divisor majorant, but the existing summability theorem assumes global `C^2`, which the source weight need not satisfy. | Prove piecewise decay directly; do not reuse the `C^2` theorem by false type alignment. |
| `PREREGISTRATION` | Fixed continuity/support, literal entire test, exact Laplace/xi coordinate transport, strip inverse-square decay, and actual multiplicity-bearing zero summability. | Production Lean remains gated on public preregistration CI. | Commit, push, and require public CI. |
| `PRODUCTION_GATE` | Published preregistration commit `aeadffd932c087a9d14b3c5c1828b4eb2faef3ce`. | Public Lean Action run `30073965695`, build job `89420586899`, passed in `2m3s`. | Open production proof-source editing. |
| `BOUNDARY_REGULARITY` | Rewrote the literal piecewise Fourier weight as a continuous clamped chord of the Volterra kernel. | Lean proves `K_u(0)=0`, continuity through the origin and both endpoints, compact support, and integrability; the physical density is also continuous, compactly supported, and integrable. | Construct the literal test and audit all source coordinates. |
| `ENTIRE_AND_COORDINATES` | Differentiated the compact Fourier integral and changed variables to the project logarithmic density. | Lean proves the test is entire and even, has exponential type at most `log(C)`, and satisfies the exact `(s-1/2)/i` Laplace and xi-divisor identities. No sign, `2*pi`, or half-shift mismatch appeared. | Attack source-strength horizontal-strip decay. |
| `DECAY_ATTEMPT` | Split the Fourier band into smooth left and right halves and integrated by parts twice on each half, retaining endpoint and origin derivative terms. | Lean proves the fixed-strip bound `norm(g_u(z)) <= M*(1+|Re(z)|)^-2`. The anticipated global BV/Stieltjes API was not needed; the derivative jumps survive explicitly in the decay numerator. | Connect the bound to the actual multiplicity-bearing divisor. |
| `ZERO_SUM` | Computed the rotated zero coordinate and compared `(1+|Im(rho)|)^-2` with `norm(rho)^-2`. | Existing certified Hadamard reciprocal-square summability yields summability of both norms and values over `RiemannXiDivisorZeroIndex`, and of the exact project symmetrized Laplace weights. No RH, simplicity, ordering, or zero-count asymptotic is used. | Package and register the fixed endpoint. |
| `REGISTRATION` | Added `WeilFiniteDictionaryAdmissibilityCertificate`, one proven Target, exact aggregate/decay/summability checks, and selected axiom prints. | Direct warning-as-error compilation passes. Selected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden scan and `git diff --check` are empty, and the full `8759/8759` build passes. | Freeze the implementation, then run immutable-evidence and final-ledger public CI. |
| `IMPLEMENTATION_CI` | Published frozen implementation commit `257b80dcda7d4a68a9c6a4b9860b1a97fa42c0ca`. | Public Lean Action run `30140659408`, build job `89633127915`, passed in `2m37s`. | Keep proof and governance source frozen; publish docs-only immutable evidence. |

## Claim boundary

The campaign proves the source admissibility lemma and actual zero-series well-definedness. It
does not assume or prove the weaker-class arithmetic explicit formula, the total finite
matrix-to-zero identity, pole or archimedean transports, cutoff limits, H7, or RH.
