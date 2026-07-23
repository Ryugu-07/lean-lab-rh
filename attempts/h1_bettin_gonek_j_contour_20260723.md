# H1 Bettin--Gonek J-Contour Campaign

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-J-CONTOUR-01`

Selected node: `H1-BETTIN-GONEK-J-CONTOUR-01`

Status: `IMPLEMENTED_LOCAL / FROZEN_IMPLEMENTATION_PENDING`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H1 `J_t` contour movement, H7 three-block assembly, H12 analytic Speiser counts, H2 bow exclusion, and H11 sparse-exception amplification. | H1 has compiled objects immediately on both sides of a source-stated contour edge; the alternatives currently need either definition-only assembly or an unidentified arithmetic mechanism. | Select the source-exact H1 contour endpoint. |
| `SOURCE_RECONSTRUCTION` | Read the original TeX for arXiv:1604.02740 equations `(2.3)`--`(2.5)`. | `G_tH_t` cancels to a rational one-pole kernel. The line-zero `O(1)` bound and selected-residue power are part of the same mechanism. | Require all three statements in one fixed endpoint. |
| `API_AUDIT` | Inspected the compiled Mellin identity, auxiliary regularization, rectangle Cauchy, improper integral, and power-norm APIs. | Existing infrastructure supports finite rectangles and vertical integrals; no source-specific contour theorem currently exists. | Publish preregistration before proof-source editing. |
| `PREREGISTRATION` | Fixed the actual-product identity, two vertical integrals, finite and infinite contour shifts, uniform boundary bound, exact residue norm, and lower inequality. | Production Lean remains gated on public preregistration CI. | Commit, push, and require public CI. |
| `PRODUCTION_GATE` | Published preregistration commit `6eb8686e145fe0661172cde6fed5d43ae3a7b33b`. | Public Lean Action run `29980444843`, build job `89120915406`, passed in `1m53s`. | Open production editing. |
| `SOURCE_CANCELLATION` | Expanded the compiled regularized `G_t`, actual `H_t`, shifted argument, and selected pole. | The zeta factor and `(w-1)^2` cancel exactly to the source `J_t` rational kernel on `Re(w)>3/2`; no source mismatch. | Continue to actual vertical integrals. |
| `VERTICAL_LINES` | Derived pointwise Cauchy majorants on `Re(w)=0` and `Re(w)=3`. | Both lines are absolutely integrable. The zero-line kernel is bounded by `4/(1+(y+t)^2)`, giving `norm(JLine(0))<=2` uniformly in `x`. | Build the finite rectangle. |
| `FINITE_RECTANGLE` | Proved holomorphy of the pole-removed actual kernel on `Re(w)>-1` and applied the local weighted Cauchy rectangle theorem. | A rectangle from real part zero to three crosses exactly `rho+1/2-it` when its height exceeds the pole ordinate; the exact residue coefficient and orientation agree with equation `(2.5)`. | Prove horizontal decay without an assumed premise. |
| `HORIZONTAL_DECAY` | Bounded the actual kernel uniformly for real part in `[0,3]` by `5*max(1,x^3)/|u|^4` once the height clears explicit source thresholds. | Both horizontal interval integrals tend to zero at infinite height. No abstract decay proposition or resource-limit relaxation is used. | Pass the finite identity to full vertical integrals. |
| `INFINITE_CONTOUR` | Combined symmetric interval convergence with both horizontal limits. | `JLine(3)=JLine(0)+residue` compiles exactly with the `1/(2*pi)` normalization. | Recover the selected-zero power. |
| `RESIDUE_POWER` | Computed the complex-power norm at the selected pole and proved the denominator scale positive. | `norm(residue)=residueScale*x^(Re(rho)+1/2)` and `residueScale*x^(Re(rho)+1/2)<=norm(JLine(3))+2`. | Register and audit the aggregate endpoint. |
| `LOCAL_GATES` | Added one proven Target, an exact aggregate TargetCheck, selected transitive axiom prints, and definition alignment; then ran the forbidden scan, patch check, and full build. | The 947-line module and all exact entry points pass with warnings as errors; selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden scan is empty, `git diff --check` passes, and the full 8,757-job build succeeds. | Freeze the implementation and require public Lean Action CI. |

## Claim boundary

The campaign does not assume or prove the inverse Mellin support theorem, `G_t` decay by itself,
convolution equation `(2.4)`, the complete moment-to-power bridge, Farmer's conjecture, H1, or RH.

Closing this fixed endpoint does not exhaust Bettin--Gonek, mollifiers, or H1. Historical-route
campaigns are omission-seeking mechanism tests: each closes only its preregistered edge, while
other source edges and the always-open original-conjecture track remain eligible for later loops.
