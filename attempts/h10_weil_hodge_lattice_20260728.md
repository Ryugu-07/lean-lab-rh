# H10 Weil Surface Hodge-Lattice Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01`

Node: `H10-WEIL-SURFACE-HODGE-LATTICE-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FULL_SOURCE_NUMERICAL_HINGE_SUCCESS / LOCAL_AUDIT_GREEN /
IMPLEMENTATION_PUBLIC_CI_REQUIRED`

## Fixed target

Kernel-check the integer-lattice-to-real semipositivity step in Weil's surface/Hodge proof,
derive the exact Hasse--Weil point-count bound, and compose the extension-wise result with the
existing finite spectral-rigidity theorem.

The complete criteria and claim boundary are fixed in
`research/h10_weil_hodge_lattice_prereg_20260728.md`.

## Attempt log

| phase | action | result | decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed H12 Speiser admissible contour at its registered meaningful partial. | Final ledger `9d86466f36f872005ec270309ce09d47168d4018` passed run `30383048725`, job `90355386390`, in `1m47s`. | Return to cross-family selection. |
| `CROSS_FAMILY_AUDIT` | Compared H1 mollifiers, H2 density, H7 spectral, H10 function fields, H11 statistics, and H13 transfer. | The repository has no campaign for Weil's surface/Hodge proof, while its Bombieri--Stepanov route is already represented. | Select the distinct H10 surface route. |
| `SOURCE_ALIGNMENT` | Reconstructed Kedlaya Section 5.2 from the Hodge-index inequality through the diagonal/Frobenius quadratic form. | Geometry yields integer divisor tests; the numerical conclusion uses real semipositivity and then the Hasse--Weil discriminant bound. | Audit the integer-to-real bridge exactly. |
| `API_SURVEY` | Checked rational numerator/denominator APIs, rational density in the reals, closed predicates, square-root identities, and the existing finite power-sum rigidity theorem. | The numerical hinge has a direct no-sorry Lean surface; actual curve intersection theory remains unavailable. | Publish docs-only preregistration before proof editing. |
| `NEGATIVE_CONTROL_DESIGN` | Chose `(b-2*a)^2-a^2/2`. | It is nonnegative on `{-1,0,1}^2` but negative at `(1,2)`. | Require it to block finite-box promotion. |
| `PREREGISTRATION_PUBLIC_CI` | Published docs-only preregistration `3c8742a23b6b955fa4ea976fd860593d6e052c27`. | Run `30383689739`, job `90357535402`, passed in `2m32s`. | Open production editing for the fixed endpoint. |
| `INTEGER_LATTICE_BRIDGE` | Scaled rational pairs to one common integer denominator, then used rational density and closedness. | `weilHodgeForm_nonneg_real_of_int` proves that integer-divisor positivity already gives real semipositivity. | Enter the source discriminant bound. |
| `POINT_COUNT_BOUND` | Evaluated the form at `(2*g,N-(q+1))`, with genus zero handled separately. | `abs_pointCount_sub_le_of_weilHodgeForm_nonneg_int` gives the exact `2*g*sqrt(q)` bound. | Compose extension-wise bounds with finite spectral rigidity. |
| `SPECTRAL_COMPOSITION` | Converted real extension power sums to norm bounds and handled the zeroth power sum by the spectrum cardinality. | `norm_eq_sqrt_of_weilHodge_lattice_extensions` forces every reciprocal spectral norm to equal `sqrt(q)`. | Run the finite-box falsification. |
| `FINITE_BOX_FALSIFICATION` | Checked the explicit homogeneous model on every integer pair with absolute coordinates at most one. | The complete finite box is nonnegative, but `(1,2)` has value `-1/2`. | Reject finite coefficient testing as a Hodge certificate. |
| `REGISTRATION` | Added one Target, seven exact TargetChecks, and seven selected axiom prints. | Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. | Run local mechanical gates. |
| `LOCAL_AUDIT` | Ran warning-as-error production and registry compiles, three forbidden scans, `git diff --check`, and the full build. | Scans are empty; patch check passes; full build passes `8783/8783`. | Freeze and publish the implementation. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary during H12 closure; governing files,
  route records, source statements, and current repository state were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
- `preregistration`: `3c8742a23b6b955fa4ea976fd860593d6e052c27`, public-green on run
  `30383689739`, job `90357535402`, in `2m32s`.
- `production_module`: `LeanLab/Riemann/WeilHodgeLattice.lean`, 243 lines.
- `local_build`: `8783/8783`.

## Current boundary

Local result: `FULL_SOURCE_NUMERICAL_HINGE_SUCCESS`.

The source's integral-divisor inequality needs no extra real-coefficient premise. It supplies
the exact Hasse--Weil point-count bound, and its extension-wise spectral specialization reaches
the existing finite reciprocal critical-circle theorem. This closes the numerical consumer in
Weil's surface proof, not its geometric producer.

Actual curve intersection numbers, the Hodge index theorem on `X x X`, the identification of
the diagonal/Frobenius intersection with point counts, extension point-count identities,
number-field transfer, H10, and RH remain open.

Result accounting:

- `historical_route_coverage_delta=1`;
- `integer_lattice_bridge_delta=1`;
- `source_numerical_hinge_delta=1`;
- `finite_spectral_composition_delta=1`;
- `actual_curve_geometry_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

Frozen implementation and public CI are the next gate.
