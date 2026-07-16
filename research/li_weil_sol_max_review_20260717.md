# Clean-Context Sol 5.6 Max Review: Li and Weil Spine

Date: 2026-07-17

Agent: `019f6a5f-5647-70c1-b89c-14e0088bb73a`

Scope: read-only theorem and trust audit of `LiReverseCriterion.lean`, `LiWeilGram.lean`,
`WeilTestAlgebra.lean`, `WeilCompactPositivityCriterion.lean`, and the actual convolution
companion `WeilConvolution.lean`. The agent did not use README, HANDOFF, memory, or prior-agent
claims as evidence.

## Findings

- P0: none.
- P1: none.
- P2: none.
- P3: `WeilTestAlgebra.lean` contains involution/star covariance but no convolution declaration;
  `weilConvolution` is in `WeilConvolution.lean`. Summaries must attribute those layers separately.
- P3: the compact positivity theorem name is broad, but its exact statement is constrained by a
  finite `F`, endpoint membership, exclusion of nontrivial zeros, and transform vanishing on `F`.
  Any summary that omits these hypotheses overstates the theorem.

## Exact reviewed endpoints

```lean
riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg :
  RiemannHypothesis ↔
    ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re

exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half
    (p₀ : RiemannXiDivisorZeroIndex)
    (hp₀ : (riemannXiDivisorZeroValue p₀).re ≠ 1 / 2) :
  ∃ n : ℕ, (liCoefficientCandidate n).re < 0

riemannHypothesis_iff_forall_liWeilQuadratic_nonneg :
  RiemannHypothesis ↔
    ∀ c : ℕ →₀ ℝ, 0 ≤ liWeilQuadratic c

RiemannHypothesis.liWeilQuadratic_eq_tsum_normSq
    (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) :
  liWeilQuadratic c =
    ∑' p, Complex.normSq (liWeilCombination c p)

mellinConvergent_weilInvolution_iff (f : ℝ → ℂ) (s : ℂ) :
  MellinConvergent (weilInvolution f) s ↔
    MellinConvergent f (1 - s)

mellin_weilInvolution (f : ℝ → ℂ) (s : ℂ) :
  mellin (weilInvolution f) s = mellin f (1 - s)

mellinConvergent_weilStar_iff (f : ℝ → ℂ) (s : ℂ) :
  MellinConvergent (weilStar f) s ↔
    MellinConvergent f (1 - conj s)

mellin_weilStar (f : ℝ → ℂ) (s : ℂ) :
  mellin (weilStar f) s = conj (mellin f (1 - conj s))

riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg
    (F : Finset ℂ)
    (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (hzero : 0 ∈ F) (hone : 1 ∈ F) :
  RiemannHypothesis ↔
    ∀ g : ℝ → ℂ,
      ContDiff ℝ ∞ g →
      HasCompactSupport g →
      (∀ z ∈ F, compactLaplaceTransform g z = 0) →
      0 ≤ (compactWeilArithmeticQuadratic g).re
```

## Mathematical audit

- `n : ℕ` denotes the successor-indexed coefficient `lambda_(n+1)`; the
  `Nat.dist n m - 1` term is used only under `n ≠ m`.
- The off-line Li chain, simultaneous phase choice, `3/16` main/tail margin, finite superlevel
  set, and multiplicity bookkeeping are coherent.
- Gram summability reduces to absolutely summable reflection-paired Li terms. Single-coordinate
  tests recover `2 * Re lambda_(n+1)`.
- The zero-point failure of `weilInvolution` is explicitly represented; Mellin integration uses
  `Ioi 0`, so this introduces no mismatch.
- The compact convention is `arithmetic = archimedean - prime`; after endpoint cancellation it
  equals `pi * zeroQuadratic`. Autocorrelation transforms as
  `G(s) * conj(G(1-conj(s)))`.
- The constrained separator and negative witness account for repeated divisor indices and both
  conjugate-reflection target values.

## Trust audit

Selected `#print axioms` output contained only `propext`, `Classical.choice`, and `Quot.sound`.
The relevant source contains no custom axioms, `sorry`, `admit`, `native_decide`, `unsafe`, or
`opaque` declarations. All requested files and `WeilConvolution.lean` elaborated successfully.

## Decision

`CONTINUE`. P1b is complete with the two P3 wording corrections above. The reviewed criteria are
equivalences; they do not establish their positivity premises unconditionally.

Limitation: the review inspected relevant imported definitions, separator, zero formula, and
explicit-formula normalization, but did not independently rederive every contour/Fourier decay
estimate or perform a writing clean rebuild.
