# Attempt Log: H2 Classical Zero-Detector Mellin Route

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`

Status: `MEANINGFUL_MELLIN_PARTIAL / PUBLICLY_CLOSED`

## Attempt ledger

| step | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_CLOSURE` | Completed the H1 Selberg local sign-change public evidence chain. | Final ledger `2be8491d89ba02acc01cb133f596bd46580303be`, run `30391193466`, job `90382907452`, passed in `1m43s`. | Return to full-atlas selection. |
| `COVERAGE_AUDIT` | Compared H2 prose, production modules, Targets, and attempts. | The half-isolated finite geometry and bow countermodel compile, but no module reconstructs the classical analytic zero detector used before density estimates. | Consider an H2 mechanism-level re-entry. |
| `SOURCE_AUDIT` | Read Maynard--Pratt Appendix C and Guth--Maynard Section 13.1 against Ingham--Huxley history. | Both current proofs expose the same truncated-Mobius, Gamma--Mellin, dyadic Type-I/Type-II entry point. | Select the common detector rather than an exponent optimization. |
| `ARITHMETIC_AUDIT` | Checked project and Mathlib support for Mobius arithmetic functions, Dirichlet convolution, L-series multiplication, actual zeta, and finite mollifiers. | The coefficient gap and right-half-plane product identity have direct library support. | Freeze them as the first mandatory clauses. |
| `ANALYTIC_AUDIT` | Compared the source contour with existing Gamma, zeta-convexity, inverse-Mellin, and contour modules. | Original-line inversion and a narrow shift crossing `w=0` and `w=1-rho` are plausible but not already compiled as this detector. Horizontal-edge decay is the likely first hard point. | Attempt the full actual shift; accept only an exact theorem-level partial. |
| `LOGIC_AUDIT` | Separated zero detection from later large-value counting. | The detector only produces a large block or line remainder. Mean values and large-value estimates are distinct later inputs, and density still cannot exclude a sparse orbit. | Keep zero count, exponents, and RH outside the endpoint. |
| `NEGATIVE_CONTROL_DESIGN` | Tested promotion from fixed total mass to one uniformly large block. | Without a cardinality bound, mass can be spread over arbitrarily many blocks. | Require a compiled cardinality-dependent threshold and countermodel. |
| `PREREG_PUBLIC_GATE` | Published the docs-only preregistration before production edits. | Commit `fc6e3c1ac5a8effc4db842716078229c869f6f56` passed public run `30391792808`, job `90384919913`, in `2m0s`. | Open the frozen production endpoint. |
| `COEFFICIENT_IMPLEMENTATION` | Defined the cutoff Mobius arithmetic function, its convolution with arithmetic zeta, and the actual finite Mobius Dirichlet polynomial. | Lean proves the divisor-sum formula, `a_M(1)=1` for `1<=M`, the exact gap for `2<=n<=M`, and the actual product `L(a_M,s)=M_M(s)*zeta(s)` for `1<Re(s)`. | Proceed to the smoothed analytic layer. |
| `FORWARD_MELLIN_IMPLEMENTATION` | Defined the exponentially smoothed series and applied Mathlib's Mellin theorem with explicit absolute summability. | Lean proves the head-tail coefficient-gap split and the full forward transform `mellin(I_z)(w)=Gamma(w)*M_M(z+w)*zeta(z+w)` for `1<Re(z)` and `0<Re(w)`. | Test the local singularities needed by the shift. |
| `LOCAL_SINGULARITY_IMPLEMENTATION` | Replaced `Gamma(w)*zeta(rho+w)` at `w=0` by a `dslope` expression and translated the zeta residue at `w=1-rho`. | For an actual `IsNontrivialZero rho`, Lean proves removable Gamma-pole cancellation on the relevant punctured domain and the exact retained residue `Y^(1-rho)*Gamma(1-rho)*M_M(1)`. No simple-zero hypothesis is used. | Attempt the global line theorem without assuming it. |
| `INVERSE_MELLIN_AUDIT` | Compared the compiled forward transform with the source's vertical inversion and infinite rectangle shift. | The first unavailable theorem is the vertical inverse identity `ClassicalDetectorInverseMellinLine`. The local residue facts do not by themselves justify inversion, horizontal-edge decay, or a contour shift. | Register one exact open successor and stop this breadth-first campaign. |
| `FINITE_DETECTOR_IMPLEMENTATION` | Formalized the source-independent mass inequality and cardinality-sensitive detector. | Lean proves a large remainder or block at threshold `1/(3*(card+1))`; uniform blocks compile as the negative control against a cardinality-free threshold. | Keep later Type-I/Type-II counting separate. |
| `LOCAL_CLASSIFICATION` | Packaged only the compiled layers in `ClassicalDetectorMellinPartialCertificate`. | Clauses 1--5, the abstract part of clause 8, clause 10, the full forward Mellin identity, and both local singularity calculations compile. The aggregate intentionally has no inverse-Mellin or global contour-shift field. | Classify `MEANINGFUL_MELLIN_PARTIAL`; run the full local and public evidence chain. |
| `LOCAL_AUDIT` | Ran warning-as-error checks, selected axiom prints, forbidden scans, diff checks, and the complete repository build. | The new module, Targets, and TargetChecks pass warning-as-error; seven selected declarations use only standard axioms; scans and `git diff --check` are empty; full build passes `8786/8786`. | Freeze the implementation and require public CI. |
| `IMPLEMENTATION_PUBLIC_GATE` | Published the frozen implementation and waited for the complete remote Lean Action. | Commit `b050e9d027ca0fa27619803df1e764b1a65f887c` passed run `30394320528`, job `90393394704`, in `2m37s`. The subsequent `LeanLab/` diff is empty. | Publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC_GATE` | Published the docs-only evidence with proof sources frozen. | Commit `ee2e2adbadad66ed8927b3aae62bd7c49f1f9baa` passed run `30394609125`, job `90394329560`, in `1m41s`; the `LeanLab/` diff from the frozen implementation is empty. | Publish one docs-only final ledger, then return to historical route selection. |

## Frozen boundary

This campaign attempts the actual classical zero-detector Mellin mechanism through the shifted
identity and finite detector dichotomy. It does not prove a Type-I/Type-II count, a fourth
moment, a large-values theorem, any zero-density exponent, actual-zeta bow exclusion, H2, or RH.

Failure after the public gate must identify the first unavailable theorem or false implication
and update the obstacle map. No unproved statement may become a premise.

## Current classification

- `result`: `MEANINGFUL_MELLIN_PARTIAL`.
- `historical_subroute_coverage_delta=1`.
- `mobius_coefficient_gap_delta=1`.
- `classical_zero_detector_delta=0`: the inverse Mellin line and global shift remain open.
- `mellin_shift_delta=0`.
- `zero_density_delta=0`.
- `hard_gap_delta=0`.
- `rh_frontier_delta=0`.

The first exact successor is `ClassicalDetectorInverseMellinLine`, followed by an infinite
rectangle contour shift whose horizontal edges require explicit Gamma decay and zeta growth
control. This campaign does not assume either statement.

Local stop is `MEANINGFUL_MELLIN_PARTIAL`. After the final-ledger public gate, return to a fresh
cross-family historical selection; do not continue H2 or optimize a density exponent by inertia.

Final ledger `b51748405512f194080f8370e5956763a9269b71` passed public Lean Action run
`30394847509`, job `90395094917`, in `1m36s`. This campaign is publicly closed.
