# R5 Compact Weil Zero-Cutoff Preregistration

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

Mode: `LITERATURE -> PROOF_ATTEMPT_A`

## Fixed Proposition

For every smooth compactly supported complex-valued function on the additive logarithmic line,
symmetrize its bilateral Laplace transform under `s |-> 1-s`. Prove that this entire symmetric
weight passes the project's selected zero-free xi rectangles to infinite height and recovers the
complete multiplicity-bearing xi-zero sum.

The indivisible endpoint is equivalent to the following Lean statement:

```lean
def symmetrizedCompactLaplaceWeight (f : R -> C) (s : C) : C :=
  (compactLaplaceTransform f s + compactLaplaceTransform f (1 - s)) / 2

theorem tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral
    {f : R -> C} (hf : ContDiff R infinity f)
    (hfsupp : HasCompactSupport f) {c : R} (hc : 1 < c) :
    Tendsto
      (selectedXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      atTop
      (nhds (pi * sum' p,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p)))
```

The formal file may use Lean Unicode and the project's existing names for `pi`, `tsum`, filters,
and the xi divisor. The endpoint must quantify over every `ContDiff R infinity` compactly supported
`f`; a fixed bump or an extra assumed top-edge limit is not an equivalent endpoint.

## Fixed-Gap Entry

- `node_id`: W1
- `gap_id`: G6
- `work_class`: FORMALIZATION
- `hard_gap_before`: W1c1 is open for a source-faithful generic test class; only Gaussian probes
  and finite Gaussian packets have an infinite-height formula
- `hard_gap_after` on success: the compact-smooth symmetric class has a complete zero-side cutoff
  passage; its arithmetic prime, pole, and archimedean evaluation remains open
- `expected_hard_gap_delta`: 1 at the fixed W1c1 zero-side subedge; G6/W1 remains open
- `classification` on success: `BRIDGE_REDUCED`
- `assumption_frontier_before`: the generic selected-height theorem still requires differentiability,
  reflection symmetry, divisor summability, and top-edge decay as external premises
- `assumption_frontier_after` on success: those four premises are discharged from only smoothness
  and compact support after explicit reflection symmetrization

This is not a mechanical wrapper. The current compact transform module proves only twofold decay
on the critical strip. The selected xi top edge has a compiled coarse `O(R^4)` logarithmic-
derivative bound, so a new sixfold integration-by-parts estimate on the wider fixed rectangle strip
is required before the generic contour endpoint can apply.

## Five-Candidate Screen

1. **Prove the full compact-support arithmetic explicit formula immediately.** This is the closest
   final W1 endpoint, but it additionally requires a carefully normalized Fourier inversion of
   every von-Mangoldt term, finite physical prime support, and a generic GammaR line argument.
   It is deferred as the natural successor rather than hidden inside the zero-cutoff proof.
2. **Prove the complete zero-side cutoff passage for the symmetrized compact-smooth class.** This
   discharges the exact four hypotheses of the existing generic rectangle theorem. It is selected.
3. **Prove only the compact prime-line Fourier inversion.** This is meaningful but does not address
   the current contour cutoff obstruction and is deferred behind Candidate 2.
4. **Prove only pole or GammaR integrability for compact weights.** These are mechanical components
   and are rejected as standalone campaign endpoints.
5. **Turn the compact separator into another RH-equivalent positivity criterion.** This repeats the
   already compiled Gaussian reverse-separation route and has no new unconditional sign mechanism.
   It is rejected by the anti-cycling rule.

## Source And Novelty Boundary

- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, Appendix B records
  the explicit formula for smooth compactly supported multiplicative test functions, while
  Appendix C states the compact-support positivity criterion:
  https://arxiv.org/abs/2006.13771
- The same paper emphasizes that compact support makes the finite-place side involve only finitely
  many primes. That arithmetic evaluation is not claimed in the present endpoint.
- The existing project theorem `tendsto_selectedXiRightVerticalIntegralFor` is the formal contour
  skeleton. The new work is to prove that the source-aligned compact class satisfies its analytic
  hypotheses.

This campaign formalizes a classical mechanism. No mathematical or formalization novelty claim is
allowed without a separate audit against mathlib, Isabelle AFP, external Lean repositories, and
the literature.

## Fixed Proof DAG

1. Prove that the bilateral Laplace transform of a continuous compactly supported function is
   complex differentiable everywhere by a dominated derivative-under-integral argument.
2. Define the reflection symmetrization and prove exact `F(1-s)=F(s)`.
3. Transport the existing reciprocal-square xi-divisor summability through the divisor reflection
   permutation and prove absolute summability of the symmetrized weight.
4. Prove an iterated integration-by-parts identity for compactly supported smooth functions and
   specialize it to six derivatives.
5. Bound the sixth-derivative transform uniformly whenever `abs (re s) <= c`, obtaining
   `norm (L f s) <= M * norm(s)^(-6)` for `s != 0`.
6. On the selected top edge, apply the bound to both `s` and `1-s`. Since both imaginary parts
   have magnitude above the height scale `R`, obtain `O(R^(-6))` for the symmetric weight.
7. Combine this with the compiled `O(R^4)` xi logarithmic-derivative estimate and the fixed edge
   length to prove the top integral is `O(R^(-2))` and tends to zero.
8. Apply `tendsto_selectedXiRightVerticalIntegralFor` to reach the exact endpoint.

## Adversarial And Boundary Tests

- `f=0` must reduce to the zero limit without a nonzero-mass premise.
- No evenness premise is allowed; reflection symmetry must come from the explicit two-term
  symmetrization.
- The real parts on the top rectangle range over `[1-c,c]`, not merely `[0,1]`; reusing the current
  strip bound without widening it is invalid.
- Two integrations by parts are insufficient against the compiled fourth-power top-edge bound.
- Both `s` and `1-s` must be proved nonzero on the positive selected top edge before division by
  their sixth powers.
- Divisor summability must retain analytic multiplicity and must not replace the divisor with an
  unordered set of distinct zero values.

## Rejection Conditions

- Reject a proof that assumes the top-edge limit, transform differentiability, or divisor
  summability instead of deriving it from `hf` and `hfsupp`.
- Reject a fixed bump, Gaussian, finite Gaussian packet, Schwartz-density assertion, or tempered-
  distribution extension as a substitute for the quantified compact-smooth endpoint.
- Reject a proof that silently uses the `[0,1]` strip estimate on the wider rectangle.
- Reject `sorry`, `admit`, `native_decide`, project axioms, unsafe declarations, numerical
  evaluators, or resource-limit relaxations.
- If sixfold decay or transform differentiability fails under two independent Lean approaches,
  close as `NO_PROGRESS`; do not weaken the endpoint to another helper theorem.

## Local Result

The exact preregistered theorem compiles in
`LeanLab/Riemann/WeilCompactLaplaceZeroCutoff.lean`. Lean proves whole-plane transform
differentiability, exact two-term reflection symmetry, complete multiplicity-bearing divisor
summability, arbitrary iterated compact-support integration by parts, inverse-sixth-power decay on
the full fixed rectangle strip, the resulting `O(R^(-2))` top-edge estimate, and the final
selected-height xi right-line limit.

All adversarial boundaries are retained: no evenness premise is added, the wider real strip is
used, both reflected top-edge arguments are shown nonzero, and analytic divisor multiplicity is
preserved. The 373-line module is diagnostic-free; exact Targets and TargetChecks, five
standard-only axiom prints, empty forbidden scans, `git diff --check`, and the full 8,680-job build
pass locally.

Classification is `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the fixed W1c1 compact
zero-side subedge. The compact arithmetic prime, pole, and archimedean evaluation, W2/G7, and RH
remain open. Preregistration commit `e70201cb71b0909ae3f7b798336931e0bd9f32ee` passed public Lean
Action CI run `29463597042`, build job `87511970349`.

Implementation commit `0e6451944ee1edb2d76d67f4fe097de2aa19ad17` passed public Lean Action CI
run `29464308480`, build job `87514106839`, in `2m10s`. Immutable evidence backfill and its own
public CI remain before campaign closure.
