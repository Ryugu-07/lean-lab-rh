# R5 Gaussian-Weil Quadratic Positivity Campaign

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-QUADRATIC-POSITIVITY-01`

Date: 2026-07-16

Status: `IMPLEMENTATION_PUBLICLY_VERIFIED`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; continued from the preserved task summary,
  repository state, and external-memory checkpoints

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | Redrew G6/G7 after public closure of the finite Gaussian test core. Generic Schwartz density, continuity, separated tempered extension, regularization, W2 positivity, and RH remain open. | Audit whether density or a narrower W2 consequence can be made honest with current interfaces. |
| 2 | `LITERATURE` | Arias de Reyna extends a finite Hermite core by tempered-distribution continuity, but the relevant separated quasicrystal temperedness is RH-equivalent. Lagarias records Weil positivity as an RH criterion. | Do not smuggle temperedness into a density argument; isolate a direction that may explicitly assume RH. |
| 3 | `FALSIFICATION` | Mathlib has Schwartz seminorms, Fourier automorphisms, translation, locally convex separation, and tempered-distribution multiplication, but no packaged Gaussian/Hermite Schwartz density or Wiener theorem. L2 density is insufficient. A direct RH-forward pair-packet calculation survives all algebraic, sign, and summability checks. | Select the finite real Gaussian-Weil quadratic endpoint and preregister it as conditional only. |
| 4 | `SCRATCH_ADMISSION` | Lean compiles the critical-line Gaussian evaluation, the finite cosine-difference Gram identity, packet-to-square pointwise equality, transport of summability to the real square family, exact zero `tsum` identity, direct packet arithmetic formula, and RH-forward real-part nonnegativity. | Admit the candidate and begin formal Proof Attempt A; helper-only closure is forbidden. |
| 5 | `PROOF_ATTEMPT_A_AND_INDEPENDENT_AUDIT` | `WeilGaussianQuadraticPositivity.lean` reaches the exact square `tsum`, direct arithmetic identity, and RH-forward arithmetic nonnegativity. Singleton and zero-coefficient boundaries compile. The warning-free standalone module, Targets, exact TargetChecks, seven standard-only axiom prints, empty forbidden scans, `git diff --check`, and the 8,673-job full build pass. | Close locally as `BRIDGE_REDUCED`; publish implementation and require public CI before later use. |
| 6 | `PUBLIC_IMPLEMENTATION_GATE` | Implementation commit `cf271684f786efcb2e83a57d76c51e215205d1d1` passed public Lean Action CI run `29447980403`, build job `87463120301`, in `1m49s`. | Backfill immutable evidence and require the evidence commit's own public CI. |

## Accounting At Selection

- `classification_if_complete`: `BRIDGE_REDUCED`
- `hard_gap_before`: no compiled sign theorem on the finite Gaussian packet core
- `hard_gap_after`: an exact RH-forward arithmetic positive quadratic kernel for every finite real
  packet of shifts
- `hard_gap_delta`: one conditional W2 kernel bridge; zero for unconditional positivity and RH
- `unconditional_RH_progress`: none
- `forbidden_success`: a finite cosine identity alone, a zero-side sign without the arithmetic
  formula, unconditional positivity, or a converse RH claim

## Scratch Evidence

- `scratch_symmetricGaussianWeight_on_criticalLine`: compiled
- `scratch_sum_mul_cos_sub_eq_sq_add_sq`: compiled
- `scratch_gaussianWeilPacket_on_criticalLine`: compiled
- `scratch_summable_gaussianXiZeroSquareTerm`: compiled
- `scratch_gaussianXiZeroQuadratic_eq_tsum_square`: compiled
- `scratch_gaussianXiZeroQuadratic_arithmetic_formula`: compiled
- `RiemannHypothesis.scratch_gaussianXiArithmeticQuadratic_re_nonneg`: compiled
- `next_gate`: completed by the formal module and independent local audit

## Local Result Before Publication

- `main_theorem`: `RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg`
- `zero_square_theorem`: `RiemannHypothesis.gaussianXiZeroQuadratic_eq_tsum_square`
- `summability`: `RiemannHypothesis.summable_gaussianXiZeroSquareTerm`
- `arithmetic_identity`: `gaussianXiZeroQuadratic_arithmetic_formula`
- `boundary_checks`: exact singleton square term and zero-coefficient arithmetic reduction
- `axiom_audit`: only `propext`, `Classical.choice`, and `Quot.sound`
- `full_build`: 8,673 jobs passed
- `classification`: `BRIDGE_REDUCED`
- `implementation_ci`: run `29447980403`, job `87463120301`, passed in `1m49s`
- `remaining_gate`: immutable evidence commit and public Lean Action CI
