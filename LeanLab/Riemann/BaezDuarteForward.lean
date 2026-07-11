import LeanLab.Riemann.BaezDuarteReverse
import LeanLab.Riemann.BalazardSaiasContour
import LeanLab.Riemann.FourierL2Compat

set_option linter.style.header false

/-!
# Forward fixed-epsilon convergence in the strong Baez-Duarte criterion
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform ArithmeticFunction.Moebius

namespace LeanLab.Riemann

/-- The positive-natural kernel, extended by zero at the unused natural index zero. -/
def baezDuarteKernelL2Nat (a : ℕ) : positiveHalfLineL2 :=
  if ha : 0 < a then baezDuarteKernelL2 ⟨a, ha⟩ else 0

theorem baezDuarteKernelL2Nat_coeFn {a : ℕ} (ha : 0 < a) :
    baezDuarteKernelL2Nat a
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fractionalPartKernel ((a : ℝ)⁻¹) := by
  rw [baezDuarteKernelL2Nat, dif_pos ha]
  exact baezDuarteKernelL2_coeFn ⟨a, ha⟩

/-- The exact source finite Mobius approximation as an element of real `L²(0,infinity)`. -/
def baezDuarteMobiusApproxL2 (δ : ℝ) (N : ℕ) : positiveHalfLineL2 :=
  ∑ a ∈ Finset.Icc 1 N,
    (((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ)) •
      baezDuarteKernelL2Nat a

theorem baezDuarteMobiusApproxL2_coeFn (δ : ℝ) (N : ℕ) :
    baezDuarteMobiusApproxL2 δ N
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        baezDuarteMobiusApprox δ N := by
  classical
  simp only [baezDuarteMobiusApproxL2]
  refine (Lp.coeFn_fun_finsetSum (Finset.Icc 1 N) fun a =>
    ((((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ)) •
      baezDuarteKernelL2Nat a)).trans ?_
  have hsum := eventuallyEq_sum
    (s := Finset.Icc 1 N) (l := ae (volume.restrict (Ioi (0 : ℝ))))
    (fun a ha => by
      have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
      refine (Lp.coeFn_smul
        (((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ))
        (baezDuarteKernelL2Nat a)).trans ?_
      exact (baezDuarteKernelL2Nat_coeFn ha_pos).const_smul
        (((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ)))
  filter_upwards [hsum] with x hx
  simpa [baezDuarteMobiusApprox, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hx

theorem baezDuarteMobiusApproxL2_mem_span (δ : ℝ) (N : ℕ) :
    baezDuarteMobiusApproxL2 δ N ∈ baezDuarteKernelSpan := by
  classical
  rw [baezDuarteMobiusApproxL2]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.smul_mem
  have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
  rw [baezDuarteKernelL2Nat, dif_pos ha_pos]
  exact Submodule.subset_span ⟨⟨a, ha_pos⟩, rfl⟩

/-- The classical Mellin formula (2.7) for a finite source Mobius approximation. -/
theorem hasMellin_baezDuarteMobiusApprox
    (δ : ℝ) (N : ℕ) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun x : ℝ => (baezDuarteMobiusApprox δ N x : ℂ)) s
      ((-riemannZeta s / s) * mobiusDirichletPartialSum N (s + δ)) := by
  classical
  have hterm : ∀ a ∈ Finset.Icc 1 N,
      HasMellin
        (fun x : ℝ =>
          ((((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) *
            fractionalPartKernel ((a : ℝ)⁻¹) x : ℝ) : ℂ)) s
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
          (a : ℂ) ^ (-(s + δ)) * (-riemannZeta s / s)) := by
    intro a ha
    have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
    have hk := hasMellin_baezDuarteKernel ⟨a, ha_pos⟩ s hs0 hs1
    have hsmul := hasMellin_const_smul hk.1
      (((((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) : ℝ) : ℂ))
    rw [hk.2] at hsmul
    have ha_ne : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
    have hpow :
        ((((a : ℝ) ^ (-δ) : ℝ) : ℂ) * (a : ℂ) ^ (-s)) =
          (a : ℂ) ^ (-(s + δ)) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg a)]
      simp only [Complex.ofReal_natCast, Complex.ofReal_neg]
      rw [← Complex.cpow_add _ _ ha_ne]
      congr 1
      ring
    convert hsmul using 1
    · funext x
      simp [smul_eq_mul]
    · simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
      rw [← hpow]
      ring
  have hfinite : ∀ u : Finset ℕ, u ⊆ Finset.Icc 1 N →
      HasMellin
        (fun x : ℝ => ∑ a ∈ u,
          ((((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) *
            fractionalPartKernel ((a : ℝ)⁻¹) x : ℝ) : ℂ)) s
        (∑ a ∈ u,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            (a : ℂ) ^ (-(s + δ)) * (-riemannZeta s / s)) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro _hu
        simp [HasMellin, MellinConvergent, mellin]
    | @insert a u ha ih =>
        intro hu
        have haI : a ∈ Finset.Icc 1 N := hu (by simp)
        have huI : u ⊆ Finset.Icc 1 N := fun b hb => hu (by simp [hb])
        have haM := hterm a haI
        have ihM := ih huI
        have hadd := hasMellin_add haM.1 ihM.1
        rw [haM.2, ihM.2] at hadd
        simpa [ha] using hadd
  have hsum := hfinite (Finset.Icc 1 N) (fun _ ha => ha)
  convert hsum using 1
  · funext x
    simp [baezDuarteMobiusApprox]
  · rw [mobiusDirichletPartialSum]
    rw [← Finset.sum_mul]
    ring

/-- The source finite approximation in complex `L²(0,infinity)`. -/
def baezDuarteMobiusApproxComplexL2 (δ : ℝ) (N : ℕ) : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp (baezDuarteMobiusApproxL2 δ N)

theorem baezDuarteMobiusApproxComplexL2_coeFn (δ : ℝ) (N : ℕ) :
    baezDuarteMobiusApproxComplexL2 δ N
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ => (baezDuarteMobiusApprox δ N x : ℂ) := by
  filter_upwards [baezDuarteOfRealLp_coeFn (baezDuarteMobiusApproxL2 δ N),
    baezDuarteMobiusApproxL2_coeFn δ N] with x hcomplex hreal
  rw [baezDuarteMobiusApproxComplexL2, hcomplex, hreal]

/-- The weighted-log representative of the source finite approximation. -/
def baezDuarteMobiusWeightedLog (δ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    baezDuarteMobiusApprox δ N (Real.exp (-u))

theorem baezDuarteMobiusWeightedLog_ae_weightedLogForwardFun (δ : ℝ) (N : ℕ) :
    baezDuarteMobiusWeightedLog δ N =ᵐ[volume]
      weightedLogForwardFun (baezDuarteMobiusApproxComplexL2 δ N) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (baezDuarteMobiusApproxComplexL2_coeFn δ N)
  filter_upwards [hsource] with u hu
  change baezDuarteMobiusApproxComplexL2 δ N (Real.exp (-u)) =
    (baezDuarteMobiusApprox δ N (Real.exp (-u)) : ℂ) at hu
  simp only [baezDuarteMobiusWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteMobiusWeightedLog_memLp (δ : ℝ) (N : ℕ) :
    MemLp (baezDuarteMobiusWeightedLog δ N) (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp (baezDuarteMobiusApproxComplexL2 δ N)).ae_eq
    (baezDuarteMobiusWeightedLog_ae_weightedLogForwardFun δ N).symm

theorem baezDuarteMobiusWeightedLog_toLp (δ : ℝ) (N : ℕ) :
    (baezDuarteMobiusWeightedLog_memLp δ N).toLp
        (baezDuarteMobiusWeightedLog δ N) =
      weightedLogPullback (baezDuarteMobiusApproxComplexL2 δ N) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (baezDuarteMobiusWeightedLog_memLp δ N)
    (weightedLogForwardFun_memLp (baezDuarteMobiusApproxComplexL2 δ N))
    (baezDuarteMobiusWeightedLog_ae_weightedLogForwardFun δ N)

theorem baezDuarteMobiusWeightedLog_integrable (δ : ℝ) (N : ℕ) :
    Integrable (baezDuarteMobiusWeightedLog δ N) := by
  have hM := hasMellin_baezDuarteMobiusApprox δ N (1 / 2 : ℂ) (by norm_num) (by norm_num)
  exact integrable_weightedLog_of_mellinConvergent hM.1

theorem fourier_baezDuarteMobiusWeightedLog (δ : ℝ) (N : ℕ) (ξ : ℝ) :
    𝓕 (baezDuarteMobiusWeightedLog δ N) ξ =
      let s : ℂ := (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I
      (-riemannZeta s / s) * mobiusDirichletPartialSum N (s + δ) := by
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    baezDuarteMobiusApprox δ N (Real.exp (-u))) ξ = _
  let τ : ℝ := 2 * Real.pi * ξ
  let s : ℂ := (1 / 2 : ℂ) + τ * Complex.I
  have hs0 : 0 < s.re := by dsimp only [s]; norm_num
  have hs1 : s.re < 1 := by dsimp only [s]; norm_num
  have hM := hasMellin_baezDuarteMobiusApprox δ N s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (fun x : ℝ => (baezDuarteMobiusApprox δ N x : ℂ)) τ
  rw [hM.2] at hFourier
  have hτ : τ / (2 * Real.pi) = ξ := by
    dsimp only [τ]
    field_simp [Real.pi_ne_zero]
  rw [hτ] at hFourier
  simpa only [τ, s] using hFourier.symm

theorem fourier_baezDuarteMobiusWeightedLog_sub (δ : ℝ) (N M : ℕ) (ξ : ℝ) :
    𝓕 (fun u => baezDuarteMobiusWeightedLog δ N u -
        baezDuarteMobiusWeightedLog δ M u) ξ =
      -(burnolMobiusTransformedError δ N (2 * Real.pi * ξ) -
        burnolMobiusTransformedError δ M (2 * Real.pi * ξ)) := by
  rw [Real.fourier_eq]
  simp_rw [smul_sub]
  rw [integral_sub
    ((Real.fourierIntegral_convergent_iff ξ).2
      (baezDuarteMobiusWeightedLog_integrable δ N))
    ((Real.fourierIntegral_convergent_iff ξ).2
      (baezDuarteMobiusWeightedLog_integrable δ M))]
  change 𝓕 (baezDuarteMobiusWeightedLog δ N) ξ -
      𝓕 (baezDuarteMobiusWeightedLog δ M) ξ = _
  rw [fourier_baezDuarteMobiusWeightedLog, fourier_baezDuarteMobiusWeightedLog]
  simp only [burnolMobiusTransformedError]
  ring

/-- Burnol's vertical `L²` majorant in Mathlib's Fourier-frequency normalization. -/
def baezDuarteScaledMajorant (η : ℝ) (ξ : ℝ) : ℂ :=
  baezDuarteVerticalMajorant (3 / 8 + η) (2 * Real.pi * ξ)

theorem baezDuarteScaledMajorant_memLp {η : ℝ} (hη : η < 1 / 8) :
    MemLp (baezDuarteScaledMajorant η) (2 : ℝ≥0∞) volume := by
  apply MemLp.comp_mul_left_volume (burnolMobiusMajorant_memLp hη)
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

theorem baezDuarteMobiusWeightedLog_sub_integrable (δ : ℝ) (N M : ℕ) :
    Integrable (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u) :=
  (baezDuarteMobiusWeightedLog_integrable δ N).sub
    (baezDuarteMobiusWeightedLog_integrable δ M)

theorem baezDuarteMobiusWeightedLog_sub_memLp (δ : ℝ) (N M : ℕ) :
    MemLp (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u) (2 : ℝ≥0∞) volume :=
  (baezDuarteMobiusWeightedLog_memLp δ N).sub
    (baezDuarteMobiusWeightedLog_memLp δ M)

theorem continuous_fourier_baezDuarteMobiusWeightedLog_sub (δ : ℝ) (N M : ℕ) :
    Continuous (𝓕 (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u)) := by
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (baezDuarteMobiusWeightedLog_sub_integrable δ N M)

theorem norm_fourier_baezDuarteMobiusWeightedLog_sub_le
    {δ η K : ℝ} {N M : ℕ}
    (hbound : ∀ (n : ℕ) (t : ℝ), 2 ≤ n →
      ‖burnolMobiusTransformedError δ n t‖ ≤
        K * (n : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖)
    (hN : 2 ≤ N) (hM : 2 ≤ M) (ξ : ℝ) :
    ‖𝓕 (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u) ξ‖ ≤
      (K * (N : ℝ) ^ (-δ / 3) + K * (M : ℝ) ^ (-δ / 3)) *
        ‖baezDuarteScaledMajorant η ξ‖ := by
  rw [fourier_baezDuarteMobiusWeightedLog_sub, norm_neg]
  calc
    ‖burnolMobiusTransformedError δ N (2 * Real.pi * ξ) -
        burnolMobiusTransformedError δ M (2 * Real.pi * ξ)‖
        ≤ ‖burnolMobiusTransformedError δ N (2 * Real.pi * ξ)‖ +
          ‖burnolMobiusTransformedError δ M (2 * Real.pi * ξ)‖ := norm_sub_le _ _
    _ ≤ K * (N : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) (2 * Real.pi * ξ)‖ +
        K * (M : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) (2 * Real.pi * ξ)‖ :=
      add_le_add (hbound N _ hN) (hbound M _ hM)
    _ = _ := by simp only [baezDuarteScaledMajorant]; ring

theorem fourier_baezDuarteMobiusWeightedLog_sub_memLp
    {δ η K : ℝ} {N M : ℕ} (hK : 0 < K) (hη : η < 1 / 8)
    (hbound : ∀ (n : ℕ) (t : ℝ), 2 ≤ n →
      ‖burnolMobiusTransformedError δ n t‖ ≤
        K * (n : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖)
    (hN : 2 ≤ N) (hM : 2 ≤ M) :
    MemLp (𝓕 (fun u => baezDuarteMobiusWeightedLog δ N u -
      baezDuarteMobiusWeightedLog δ M u)) (2 : ℝ≥0∞) volume := by
  let C : ℝ := K * (N : ℝ) ^ (-δ / 3) + K * (M : ℝ) ^ (-δ / 3)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajor := (baezDuarteScaledMajorant_memLp hη).const_smul (C : ℂ)
  refine hmajor.of_le
    (continuous_fourier_baezDuarteMobiusWeightedLog_sub δ N M).aestronglyMeasurable
    (ae_of_all volume fun ξ => ?_)
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  exact norm_fourier_baezDuarteMobiusWeightedLog_sub_le hbound hN hM ξ

theorem baezDuarteMobiusWeightedLog_sub_toLp (δ : ℝ) (N M : ℕ) :
    (baezDuarteMobiusWeightedLog_sub_memLp δ N M).toLp
        (fun u => baezDuarteMobiusWeightedLog δ N u -
          baezDuarteMobiusWeightedLog δ M u) =
      weightedLogPullback
        (baezDuarteMobiusApproxComplexL2 δ N -
          baezDuarteMobiusApproxComplexL2 δ M) := by
  calc
    _ = (baezDuarteMobiusWeightedLog_memLp δ N).toLp
          (baezDuarteMobiusWeightedLog δ N) -
        (baezDuarteMobiusWeightedLog_memLp δ M).toLp
          (baezDuarteMobiusWeightedLog δ M) := by
      convert MemLp.toLp_sub (baezDuarteMobiusWeightedLog_memLp δ N)
        (baezDuarteMobiusWeightedLog_memLp δ M)
      simp only [Pi.sub_apply]
    _ = _ := by
      rw [baezDuarteMobiusWeightedLog_toLp,
        baezDuarteMobiusWeightedLog_toLp, map_sub]

theorem norm_baezDuarteMobiusApproxComplexL2_sub_le
    {δ η K : ℝ} {N M : ℕ} (hK : 0 < K) (hη : η < 1 / 8)
    (hbound : ∀ (n : ℕ) (t : ℝ), 2 ≤ n →
      ‖burnolMobiusTransformedError δ n t‖ ≤
        K * (n : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖)
    (hN : 2 ≤ N) (hM : 2 ≤ M) :
    ‖baezDuarteMobiusApproxComplexL2 δ N -
        baezDuarteMobiusApproxComplexL2 δ M‖ ≤
      (K * (N : ℝ) ^ (-δ / 3) + K * (M : ℝ) ^ (-δ / 3)) *
        ‖(baezDuarteScaledMajorant_memLp hη).toLp
          (baezDuarteScaledMajorant η)‖ := by
  let f : ℝ → ℂ := fun u => baezDuarteMobiusWeightedLog δ N u -
    baezDuarteMobiusWeightedLog δ M u
  have hf1 : Integrable f := baezDuarteMobiusWeightedLog_sub_integrable δ N M
  have hf2 : MemLp f (2 : ℝ≥0∞) volume :=
    baezDuarteMobiusWeightedLog_sub_memLp δ N M
  have hF2 : MemLp (𝓕 f) (2 : ℝ≥0∞) volume :=
    fourier_baezDuarteMobiusWeightedLog_sub_memLp hK hη hbound hN hM
  have hcompat := fourier_toLp_eq_toLp_fourier hf1 hf2 hF2
  have hnorm :
      ‖hF2.toLp (𝓕 f)‖ ≤
        (K * (N : ℝ) ^ (-δ / 3) + K * (M : ℝ) ^ (-δ / 3)) *
          ‖(baezDuarteScaledMajorant_memLp hη).toLp
            (baezDuarteScaledMajorant η)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hF2.coeFn_toLp,
      (baezDuarteScaledMajorant_memLp hη).coeFn_toLp] with ξ hFourier hmajor
    rw [hFourier, hmajor]
    exact norm_fourier_baezDuarteMobiusWeightedLog_sub_le hbound hN hM ξ
  calc
    ‖baezDuarteMobiusApproxComplexL2 δ N -
        baezDuarteMobiusApproxComplexL2 δ M‖ =
        ‖weightedLogPullback
          (baezDuarteMobiusApproxComplexL2 δ N -
            baezDuarteMobiusApproxComplexL2 δ M)‖ :=
      (weightedLogPullback.norm_map _).symm
    _ = ‖hf2.toLp f‖ := by
      rw [baezDuarteMobiusWeightedLog_sub_toLp]
    _ = ‖𝓕 (hf2.toLp f)‖ := (MeasureTheory.Lp.norm_fourier_eq _).symm
    _ = ‖hF2.toLp (𝓕 f)‖ := by rw [hcompat]
    _ ≤ _ := hnorm

theorem RiemannHypothesis.cauchySeq_baezDuarteMobiusApproxComplexL2
    (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) :
    CauchySeq (baezDuarteMobiusApproxComplexL2 δ) := by
  let η : ℝ := 1 / 16
  have hη : 0 < η := by norm_num [η]
  have hη_top : η < 1 / 8 := by norm_num [η]
  obtain ⟨K, hK, hbound⟩ :=
    RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le_compiled
      hRH hδ hδ_top hη
  let B : ℝ := ‖(baezDuarteScaledMajorant_memLp hη_top).toLp
    (baezDuarteScaledMajorant η)‖
  have hsmall : Tendsto
      (fun n : ℕ => K * (n : ℝ) ^ (-δ / 3) * B) atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_natCast_rpow_neg_delta_div_three hδ).const_mul K).mul_const B
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      K * (n : ℝ) ^ (-δ / 3) * B < ε / 2 :=
    hsmall.eventually (Iio_mem_nhds (half_pos hε))
  have htwo : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  rcases (eventually_atTop.1 (hevent.and htwo)) with ⟨n₀, hn₀⟩
  refine ⟨n₀, fun m hm n hn => ?_⟩
  have hm' := hn₀ m hm
  have hn' := hn₀ n hn
  rw [dist_eq_norm]
  calc
    ‖baezDuarteMobiusApproxComplexL2 δ m -
        baezDuarteMobiusApproxComplexL2 δ n‖ ≤
        (K * (m : ℝ) ^ (-δ / 3) + K * (n : ℝ) ^ (-δ / 3)) * B := by
      exact norm_baezDuarteMobiusApproxComplexL2_sub_le hK hη_top hbound hm'.2 hn'.2
    _ = K * (m : ℝ) ^ (-δ / 3) * B +
        K * (n : ℝ) ^ (-δ / 3) * B := by ring
    _ < ε / 2 + ε / 2 := add_lt_add hm'.1 hn'.1
    _ = ε := by ring

/-- Under RH, every fixed source-admissible positive weight gives a norm-convergent sequence of
natural-index Mobius approximations, and its limit remains in the natural-kernel closure. -/
theorem RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2
    (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) :
    ∃ f : positiveHalfLineL2,
      Tendsto (baezDuarteMobiusApproxL2 δ) atTop (nhds f) ∧
        f ∈ baezDuarteKernelClosure := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (RiemannHypothesis.cauchySeq_baezDuarteMobiusApproxComplexL2
      hRH hδ hδ_top)
  let f : positiveHalfLineL2 := baezDuarteRealPartLp g
  have hreal : Tendsto (baezDuarteMobiusApproxL2 δ) atTop (nhds f) := by
    have hmap := (baezDuarteRealPartLp.continuous.tendsto g).comp hg
    simpa [Function.comp_def, baezDuarteMobiusApproxComplexL2,
      baezDuarteRealPartLp_ofReal, f] using hmap
  refine ⟨f, hreal, ?_⟩
  have hclosed : IsClosed (baezDuarteKernelClosure : Set positiveHalfLineL2) := by
    rw [baezDuarteKernelClosure]
    exact Submodule.isClosed_topologicalClosure baezDuarteKernelSpan
  apply hclosed.mem_of_tendsto hreal
  exact Eventually.of_forall fun N =>
    Submodule.le_topologicalClosure baezDuarteKernelSpan
      (baezDuarteMobiusApproxL2_mem_span δ N)

end LeanLab.Riemann
