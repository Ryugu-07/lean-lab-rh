# H10 Weil Surface Hodge-Lattice Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01`

Node: `H10-WEIL-SURFACE-HODGE-LATTICE-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

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

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary during H12 closure; governing files,
  route records, source statements, and current repository state were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.

## Current boundary

No production theorem has been added. Actual Hodge index, curve intersections, extension point
counts, number-field transfer, H10, and RH remain open. Public preregistration CI is the next
gate.
