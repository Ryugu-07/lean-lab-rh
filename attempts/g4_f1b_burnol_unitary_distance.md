# G4-F1b Burnol Unitary Distance Assembly

Date: 2026-07-13

- `batch_id`: `BATCH-20260713-G4-F1B`
- `node_id`: `B1`
- `gap_id`: `G4/F1b`
- `work_class`: `SOURCE_FORMALIZATION`
- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_before`: F1b selected; F2-F5 open; M2/G3 parked and unchanged.
- `hard_gap_after`: F1b complete; F2 selected; F3-F5 and M2/G3 unchanged.
- `hard_gap_delta`: closed the fixed unitary distance-model source edge only.

## Target

Formalize as one indivisible batch the critical-line phase

```text
s(xi) = 1/2 + (2*pi*xi) I,
m(xi) = (s(xi)-1)/s(xi),
```

the induced complex `L2` isometry `T`, its explicit actions

```text
T chi = chi1,
T (rho(theta/t)) = -A(t/theta),
```

the resulting span transport, and Burnol's exact distance identity.

## Successful Route

1. Prove directly that the critical-line denominator is nonzero and that `|m(xi)|=1`. Package
   multiplication by `m` and by its conjugate as inverse maps on frequency-side complex `L2`.
2. Conjugate the frequency multiplier by the compiled Fourier-Mellin isometry. This gives the
   positive-half-line complex linear isometric equivalence `burnolHardyInverseL2`.
3. Define `chi1(t)=(1+log t) chi_(0,1](t)` explicitly. Prove its `L2` membership and Mellin
   transform `(s-1)/s^2`; Fourier-Mellin injectivity then gives `T chi=chi1` as an equality of
   actual `L2` quotient elements.
4. Define every model generator explicitly as `A(t/theta)`. The scaled F1a Mellin formula and the
   fractional-part-kernel formula, with the project frequency normalization, prove
   `T rho(theta/t)=-A(t/theta)` for every admissible `theta`.
5. Map the original generator set through the isometry, absorb the required minus sign in the
   complex span, and prove exact submodule equality with the explicit model-kernel span.
6. Apply invariance of `Metric.infDist` under the isometry to obtain the exact source-facing
   equality `burnolDistance cutoff = burnolModelDistance cutoff`.

## Rejected Or Corrected Routes

- Defining `chi1` or the model span as an abstract image was rejected by the preregistered
  anti-tautology gate. Both theorem-facing objects have explicit representatives.
- A generic unit-modulus multiplier was treated only as infrastructure; the batch was not counted
  until target, every kernel, both spans, and the distance were transported together.
- The source sign was not discarded: the pointwise `L2` theorem retains
  `T rho(theta/t)=-A(t/theta)`. Only the subsequent complex-span proof absorbs the minus sign.
- The dilation scalar was handled through explicit scaled Mellin formulas rather than silently
  identifying normalized and unnormalized dilations.

## Lean Surface And Audit

- Module: `LeanLab/Riemann/BurnolHardy.lean`.
- Central names: `norm_burnolHardyInverseMultiplier`, `burnolFrequencyPhaseL2`,
  `burnolHardyInverseL2`, `hasMellin_burnolChiOne`, `burnolHardyInverseL2_target`,
  `burnolHardyInverseL2_kernel`, `burnolHardyInverseL2_map_kernelSpan`,
  `burnolDistance_eq_modelDistance`.
- Explicit representatives: `burnolChiOneL2_coeFn` and `burnolModelKernelL2_coeFn`.
- Exact witnesses compile in `TargetChecks.lean`.
- Trusted dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake build` passes with 8611 jobs; incomplete-proof and explicit-declaration scans and
  `git diff --check` pass.
- No `sorry`, `admit`, `sorryAx`, project `axiom`, or project `constant` is present.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed).
- `reasoning_effort`: not exposed.
- `budget`: unbounded persistent-goal budget.
- `compaction_state`: one automatic compaction occurred during implementation; work resumed from
  retained state and rechecked the fixed target before assembly.
- `commit_SHA`: `087f07a28c48794d9dbfec30309759a05b37db20`.
- `public_CI`: success, run `29231279145`, build job `86755849239`.
