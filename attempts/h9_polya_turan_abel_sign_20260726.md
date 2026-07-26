# H9 Pólya--Turán Abel Sign Audit

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01`

Selected node: `H9-POLYA-TURAN-ABEL-SIGN-AUDIT-01`

Status: `LOCAL_FULL_ABEL_AUDIT_SUCCESS / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H7 weak-regularity transport, H12 analytic Speiser counts, H2 bow localization, H10 function-field transfer, the next H1 moment step, and the unformalized Pólya--Turán historical route. | H7 remains the strongest compiled-chain reserve, but Pólya--Turán is a genuine census hole: it is named only as a failed mechanism and has neither a source card nor a Lean theorem. | Select a bounded source/logic audit before returning to the ranked theorem bridges. |
| `SOURCE_RECONSTRUCTION` | Separated Pólya's unweighted Liouville sum, Turán's harmonic-weighted sum, Turán's finite zeta sections, the Haselgrove disproof, the 2008 exact computation, and Alkan's modern repaired equivalences. | The route is not one conjecture.  The first two sums are linked by finite Abel summation, while the finite zeta-section route has a separate failure mechanism. | Fix only the exact Abel/sign edge; do not conflate the three claims. |
| `API_AUDIT` | Located Mathlib's exact integer-valued `ArithmeticFunction.liouville` and finite rational-sum APIs. | The endpoint can use exact `Rat` arithmetic with no numerical oracle. | Preregister a general Abel identity, Liouville specialization, sign consequence, and generic witness. |
| `PREREGISTRATION` | Fixed the theorem statements, source boundary, success/falsification conditions, and mechanical gates. | Production Lean editing remains closed until this docs-only state passes public CI. | Commit the preregistration state, push, and require public Lean Action CI. |
| `PUBLIC_GATE` | Published preregistration commit `f6f1329558bca0aa233bbaa472604c2bacbd6fa4`. | Lean Action run `30184412364`, build job `89746411347`, passed in `2m2s`. | Open only the fixed production endpoint. |
| `GENERIC_ABEL` | Defined one-indexed rational prefix and harmonic sums and proved the exact finite Abel identity. | `finiteHarmonicWeightedSum_eq_abel` compiles for every rational sequence and every positive endpoint. | Specialize to the source Liouville sequence. |
| `LIOUVILLE_ALIGNMENT` | Cast Mathlib's integer-valued Liouville function to `Rat`, checked values at one and two, and specialized Abel summation. | `turanLiouvilleSum_eq_abel` compiles with exact source indexing and no floating point. | Determine the strongest consequence of the historical prefix-sign premise. |
| `SIGN_CONSEQUENCE` | Isolated the positive first prefix and proved the remaining Abel coefficients nonnegative. | Prefix nonpositivity from index two yields only `turanLiouvilleSum (N+2) <= 1/2`; it does not yield weighted positivity. | Test whether the missing sign follows from prefix logic alone. |
| `FALSIFICATION_WITNESS` | Tested the sequence `a(1)=1`, `a(2)=-3`, and `a(n)=0` afterward. | Lean proves every prefix from index two equals `-2`, while the second harmonic-weighted sum equals `-1/2`. The generic sign-only shortcut is false. | Record this as a logic obstruction, not a Liouville counterexample. |
| `REGISTRATION` | Added the aggregate certificate, proven Target, exact TargetChecks, and six selected axiom prints. | All interfaces compile; the selected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. | Run the full mechanical gate. |
| `MECHANICAL_AUDIT` | Compiled the 244-line module directly and through Lake; scanned forbidden tokens and declarations; ran `git diff --check` and the full build. | New source is warning-free, scans are empty, patch check passes, and `lake build` passes `8761/8761`. | Freeze the implementation and require public CI. |

## Current boundary

No historical false sign conjecture is assumed.  No published large-index counterexample, finite
zeta-section zero, eventual-sign-to-RH implication, Alkan equivalence, or RH theorem is claimed.
The generic witness is not the Liouville sequence.  The persistent RH Goal remains active.
