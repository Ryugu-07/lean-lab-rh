# R5 Compact Weil Criterion Preregistration

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-CRITERION-01`

Date: 2026-07-16

Status: `PREREGISTERED`

Mode: `LITERATURE`

## Source Endpoint

Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, Appendix C,
Proposition C.1, states that for every finite set `F` disjoint from the nontrivial zeta zeros and
containing `0` and `1`, RH is equivalent to the Weil inequality on every smooth compactly
supported convolution square whose Mellin transform vanishes on `F`:

https://arxiv.org/pdf/2006.13771

The source follows Yoshida's compact-support criterion. Its converse uses a compactly supported
Mellin interpolant normalized at one selected zero, vanishing on `F`, and quadratically small at
the other zeros. The project already has a stronger complete-divisor `ell^1` separator and now has
the full compact `C^6` arithmetic explicit formula. Those two new public prerequisites are the
specific evidence allowing this previously deferred assembly to be reopened.

## Fixed Additive-Log Definitions

For a compactly supported smooth function `g : R -> C`, define the additive-log form of the source
involution and convolution square by

```text
compactLaplaceConjInvolution g x = exp(-x) * conj(g(-x))
compactLaplaceAutocorrelation g = g * compactLaplaceConjInvolution g
```

where `*` is additive convolution. If `G(s)` is the bilateral Laplace transform of `g`, then the
transform of the autocorrelation must be proved to be

```text
G(s) * conj(G(1 - conj(s))).
```

At an RH zero this is `normSq(G(s))`. The arithmetic quadratic is fixed at the already supported
right line `c=2`:

```text
compactWeilArithmeticQuadratic g =
  compactSymmetrizedXiArchimedeanIntegral
    (compactLaplaceAutocorrelation g) 2
  - tsum (compactSymmetrizedVonMangoldtWeight
      (compactLaplaceAutocorrelation g))
```

The elementary pole term is absent only after proving from `0,1 in F` that the autocorrelation
transform vanishes at `0` and `1`.

## Fixed Lean Endpoint

Names of internal definitions may change to fit the existing namespace, but the final theorem may
not be weakened:

```lean
theorem riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg
    (F : Finset C)
    (hFzero : forall z in F, not (IsNontrivialZero z))
    (hzero : 0 in F) (hone : 1 in F) :
    Mathlib.RiemannHypothesis iff
      forall g : R -> C,
        ContDiff R infinity g ->
        HasCompactSupport g ->
        (forall z in F, compactLaplaceTransform g z = 0) ->
        0 <= (compactWeilArithmeticQuadratic g).re
```

The final theorem must quantify over every finite source-admissible `F`, not only `{0,1}`, and over
all smooth compactly supported complex functions satisfying the exact vanishing conditions.

## Five-Candidate Screen

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: Connes--Consani/Yoshida compact Weil criterion for arbitrary finite `F` | The complete compact arithmetic formula and complete-divisor separator are now public. The remaining work is the genuine source assembly: constrained interpolation, conjugate involution, convolution square, sign, and reverse off-line witness. | Select. |
| C2: Delsarte formula for every entire weight with rapid strip decay | The prime side is no longer finite and requires a new infinite Fourier/prime interchange plus a topology controlling every vertical seminorm. This is the later W1c2 extension, not an adjacent endpoint. | Defer. |
| C3: complete raw `IsWeilStripAdmissible` in transform supremum | The raw carrier includes the nonpositive half-line ignored by Mellin integration and is nonseparated. Bounded strip transforms also have no vertical decay. Completion would lose a proved physical representative. | Reject. |
| C4: Arias de Reyna tempered prime measure criterion | Temperedness of the arithmetic measure is itself RH-equivalent. Its RH-forward proof needs a strong prime-counting error and its reverse is not a prerequisite for C1. | Defer; never assume temperedness. |
| C5: Connes--Consani semi-local operator positivity | The source's quantitative support result requires prolate spectral data and computer-assisted inequalities. It is a distinct operator campaign and supplies no immediate full-prime sign. | Defer. |

## Adversarial Tests

1. The source sign is `sum_v W_v <= 0`; under the project's normalization this must become
   nonnegativity of `compactWeilArithmeticQuadratic`, because the explicit formula identifies the
   latter with `pi` times the zero quadratic.
2. `F` must be disjoint from the complete nontrivial-zero set and contain both `0` and `1`.
   Omitting either endpoint changes the pole term and is a rejection.
3. For an off-line zero `rho`, the conjugate-reflection partner `1-conj(rho)` is a distinct
   nontrivial zero. The reverse witness must assign transform values `1` and `-1` at this pair and
   vanish exactly on `F`.
4. Equal-value multiplicity copies cannot be separated. They must all contribute the same negative
   target value and strengthen, rather than invalidate, the contradiction.
5. No multiplicity-preserving conjugation permutation may be silently assumed. The proof may use
   uniform strip bounds for the partner factor and only the existing reflection permutation where
   it is actually available.
6. The two target values and every low zero used in the finite split must be killed or protected
   before the convolution-power tail limit. Choosing the finite set after estimating the
   polynomial tail is forbidden circularity.
7. The endpoint is an RH equivalence, not an unconditional positivity proof. It must not be
   reported as closing W2/G7 or proving RH.

## Fixed Proof DAG

1. Prove `riemannXi(conj(s)) = conj(riemannXi(s))` and that nontrivial zeros are closed under
   conjugation and conjugate reflection.
2. Define the additive-log conjugate involution. Prove smooth compact-support preservation and its
   exact Laplace covariance `G(s) -> conj(G(1-conj(s)))`.
3. Define compact autocorrelation, prove smooth compact support, and prove the exact transform
   product.
4. Strengthen the existing compact separator to vanish on an arbitrary finite set disjoint from
   its protected target, while retaining exact normalization and the complete strict `ell^1` tail.
5. Under RH, prove the zero quadratic is a summable `normSq` family and has nonnegative real part.
6. If RH fails, choose an off-line divisor index and its conjugate-reflection partner. Construct two
   finite-constrained separators, subtract them, split off a finite low-zero set, and prove the
   complete zero quadratic has strictly negative real part.
7. Apply the public compact `C^6` arithmetic formula to the autocorrelation. Use the `F` endpoint
   conditions to remove the pole term and prove the exact arithmetic/zero quadratic identity.
8. Assemble both implications of the fixed endpoint, exact TargetChecks, selected axiom prints,
   forbidden scans, full local build, and independent public CI.

## Rejection Conditions

- Reject any assumption of RH in the reverse direction, simple zeros, a zero enumeration,
  Riemann--von Mangoldt asymptotics, temperedness, Schwartz density, or an unproved conjugation
  multiplicity theorem.
- Reject replacing arbitrary finite `F` by `{0,1}` or dropping exact vanishing.
- Reject a theorem only about the zero side without the compiled arithmetic functional.
- Reject a theorem only about the arithmetic identity without the RH equivalence.
- Reject a raw or finite zero set in place of the complete multiplicity-bearing divisor `tsum`.
- Reject any `sorry`, `admit`, `native_decide`, project axiom, unsafe/opaque declaration, or
  resource-limit relaxation.
- If the constrained separator or off-line negative quadratic cannot be closed after two genuinely
  different proof mechanisms, close the campaign as `NO_PROGRESS` and return to route selection.

## Accounting

- `hard_gap_before`: the compact C6 explicit formula and unconstrained compact separator are public,
  but the source compact-support positivity criterion is not assembled
- `hard_gap_after_if_complete`: Connes--Consani Appendix C Proposition C.1 is compiled on the
  equivalent additive-log compact class with the exact arithmetic side
- `hard_gap_delta`: one source-level W1/G6 compact-criterion edge if the full endpoint compiles;
  zero for W2/G7 and RH
- `assumption_frontier_before`: constrained compact interpolation, conjugate autocorrelation, and
  the reverse off-line quadratic are unproved
- `assumption_frontier_after_if_complete`: unconditional positivity W2/G7 and RH remain; the
  Delsarte/Schwartz distributional extension remains optional rather than a premise of the compact
  criterion
- `expected_classification`: `KNOWN_THEOREM_FORMALIZED` or `BRIDGE_REDUCED`
- `normalized_tuple`: `(arbitrary finite F containing 0 and 1 and disjoint from xi zeros, smooth
  compact additive-log g with G|F=0, conjugate-reflection convolution square, exact compact
  arithmetic Weil quadratic nonnegative for all g iff Mathlib.RiemannHypothesis)`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_campaign`: no

