import LeanLab.Riemann.BaezDuarteTailTransfer
import LeanLab.Riemann.LiScaffold
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.ODE.Gronwall
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

set_option linter.style.header false

/-!
# The Baez-Duarte zeta-ratio estimate

This file derives the Gamma-ratio input to Baez-Duarte Lemma 2.2 from logarithmic growth of the
digamma function on vertical strips.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace LeanLab.Riemann

/-- Logarithmic digamma growth and Gronwall give a polynomial Gamma-ratio bound on every fixed
positive vertical strip. -/
theorem exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
    (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℂ) (δ : ℝ), a ≤ z.re → (z + δ).re ≤ b → 0 ≤ δ →
        ‖Complex.Gamma (z + δ) / Complex.Gamma z‖ ≤
          (|z.im| + 2) ^ (C * δ) := by
  obtain ⟨C, hC, hdigamma⟩ :=
    Complex.exists_norm_digamma_le_log (a := a) (b := b) ha
  refine ⟨C, hC, ?_⟩
  intro z δ hz_re hzδ_re hδ
  let F : ℝ → ℂ := fun u => Complex.Gamma (z + u) / Complex.Gamma z
  let F' : ℝ → ℂ := fun u => Complex.digamma (z + u) * F u
  let K : ℝ := C * Real.log (|z.im| + 2)
  have hz_pos : 0 < z.re := lt_of_lt_of_le ha hz_re
  have hz_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hz_pos
  have hpath (u : ℝ) :
      HasDerivAt (fun y : ℝ => z + (y : ℂ)) 1 u := by
    simpa using (hasDerivAt_id u).ofReal_comp.const_add z
  have hF_deriv (u : ℝ) (hu : u ∈ Set.Icc 0 δ) :
      HasDerivAt F (F' u) u := by
    have hzu_re : 0 < (z + (u : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hu.1]
    have hzu_ne : Complex.Gamma (z + (u : ℂ)) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos hzu_re
    have hGdiff : DifferentiableAt ℂ Complex.Gamma (z + (u : ℂ)) :=
      Complex.differentiableAt_Gamma _ (fun n hzero => by
        have hre := congrArg Complex.re hzero
        simp at hre
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        change 0 < z.re + u at hzu_re
        linarith)
    have hGcomp :
        HasDerivAt (fun y : ℝ => Complex.Gamma (z + (y : ℂ)))
          (deriv Complex.Gamma (z + (u : ℂ))) u := by
      change HasDerivAt
        (Complex.Gamma ∘ fun y : ℝ => z + (y : ℂ))
          (deriv Complex.Gamma (z + (u : ℂ))) u
      simpa only [one_smul] using hGdiff.hasDerivAt.scomp u (hpath u)
    have hlogDeriv :
        Complex.digamma (z + (u : ℂ)) =
          deriv Complex.Gamma (z + (u : ℂ)) /
            Complex.Gamma (z + (u : ℂ)) := by
      rw [Complex.digamma_def, logDeriv_apply]
    have hderivGamma :
        deriv Complex.Gamma (z + (u : ℂ)) =
          Complex.digamma (z + (u : ℂ)) *
            Complex.Gamma (z + (u : ℂ)) := by
      rw [hlogDeriv]
      exact (div_mul_cancel₀ _ hzu_ne).symm
    have hderiv_value :
        deriv Complex.Gamma (z + (u : ℂ)) / Complex.Gamma z =
          Complex.digamma (z + (u : ℂ)) *
            (Complex.Gamma (z + (u : ℂ)) / Complex.Gamma z) := by
      rw [hderivGamma]
      ring_nf
    simpa only [F, F', hderiv_value] using hGcomp.div_const (Complex.Gamma z)
  have hF_cont : ContinuousOn F (Set.Icc 0 δ) := by
    intro u hu
    exact (hF_deriv u hu).continuousAt.continuousWithinAt
  have hF_right (u : ℝ) (hu : u ∈ Set.Ico 0 δ) :
      HasDerivWithinAt F (F' u) (Set.Ici u) u :=
    (hF_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt
  have hK_nonneg : 0 ≤ K := by
    exact mul_nonneg hC.le (Real.log_nonneg (by linarith [abs_nonneg z.im]))
  have hbound (u : ℝ) (hu : u ∈ Set.Ico 0 δ) :
      ‖F' u‖ ≤ K * ‖F u‖ + 0 := by
    have hzu_lo : a ≤ (z + (u : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [hu.1]
    have hzu_hi : (z + (u : ℂ)).re ≤ b := by
      have hu_le : u ≤ δ := hu.2.le
      simp only [Complex.add_re, Complex.ofReal_re] at hzδ_re ⊢
      linarith
    have hpsi := hdigamma (z + (u : ℂ)) hzu_lo hzu_hi
    have hpsi' : ‖Complex.digamma (z + (u : ℂ))‖ ≤ K := by
      simpa [K] using hpsi
    change ‖Complex.digamma (z + (u : ℂ)) * F u‖ ≤ K * ‖F u‖ + 0
    rw [norm_mul, add_zero]
    exact mul_le_mul_of_nonneg_right hpsi' (norm_nonneg (F u))
  have hF_zero : ‖F 0‖ ≤ 1 := by
    simp [F, hz_ne]
  have hgronwall :=
    norm_le_gronwallBound_of_norm_deriv_right_le
      (f := F) (f' := F') (a := 0) (b := δ)
      (K := K) (δ := 1) (ε := 0)
      hF_cont hF_right hF_zero hbound δ ⟨hδ, le_rfl⟩
  have hbase_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg z.im]
  rw [sub_zero, gronwallBound_ε0, one_mul] at hgronwall
  simp only [K] at hgronwall
  change ‖Complex.Gamma (z + δ) / Complex.Gamma z‖ ≤ _
  rw [Real.rpow_def_of_pos hbase_pos]
  convert hgronwall using 1
  ring_nf

theorem Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  have hpi : (starRingEnd ℂ) (Real.pi : ℂ) = (Real.pi : ℂ) := by simp
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [starRingEnd_apply, star_ofNat]
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) harg
  have hgamma := Complex.Gamma_conj (s / 2)
  have hpow' :
      (Real.pi : ℂ) ^ (-(starRingEnd ℂ) s / 2) =
        (starRingEnd ℂ) ((Real.pi : ℂ) ^ (-s / 2)) := by
    simpa [map_neg, map_div₀, htwo] using hpow
  have hgamma' :
      Complex.Gamma ((starRingEnd ℂ) s / 2) =
        (starRingEnd ℂ) (Complex.Gamma (s / 2)) := by
    simpa [map_div₀, htwo] using hgamma
  rw [hpow', hgamma']

theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq,
    completedRiemannZeta₀_conj]
  simp only [map_sub, map_one, map_div₀]

theorem riemannZeta_conj (s : ℂ) :
    riemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (riemannZeta s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · calc
      riemannZeta ((starRingEnd ℂ) 0) = riemannZeta 0 := by rw [map_zero]
      _ = (-1 / 2 : ℂ) := riemannZeta_zero
      _ = (starRingEnd ℂ) (riemannZeta 0) := by
        rw [riemannZeta_zero]
        norm_num [starRingEnd_apply]
  · have hconj : (starRingEnd ℂ) s ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hs
    rw [riemannZeta_def_of_ne_zero hconj, riemannZeta_def_of_ne_zero hs,
      completedRiemannZeta_conj, Gammaℝ_conj, map_div₀]

/-- Away from a zero of `ζ`, the completed zeta functional equation expresses the quotient at
`1 - s` and `s` as a quotient of archimedean Gamma factors. -/
theorem riemannZeta_one_sub_div (s : ℂ)
    (hs_re : 0 < s.re) (h1s_re : 0 < (1 - s).re)
    (hzeta : riemannZeta s ≠ 0) :
    riemannZeta (1 - s) / riemannZeta s =
      Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) := by
  have hs_ne : s ≠ 0 := by
    intro hs
    simp [hs] at hs_re
  have h1s_ne : 1 - s ≠ 0 := by
    intro hs
    simp [hs] at h1s_re
  have hGamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs_re
  have hGamma_one_sub : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos h1s_re
  have hcompleted : completedRiemannZeta s ≠ 0 := by
    intro hzero
    apply hzeta
    rw [riemannZeta_def_of_ne_zero hs_ne, hzero, zero_div]
  rw [riemannZeta_def_of_ne_zero h1s_ne,
    riemannZeta_def_of_ne_zero hs_ne, completedRiemannZeta_one_sub]
  field_simp

/-- The Baez-Duarte zeta quotient is bounded by the corresponding quotient of completed Gamma
factors. The inequality also covers zeros of the denominator, where Lean's division is zero. -/
theorem norm_baezDuarteZetaRatio_le_norm_Gammaℝ_div
    (ε τ : ℝ) (hε : 0 ≤ ε) (hε_half : ε < 1 / 2) :
    ‖baezDuarteZetaRatio ε τ‖ ≤
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ε + τ * Complex.I) /
        Complex.Gammaℝ (1 - ((1 / 2 : ℂ) + ε + τ * Complex.I))‖ := by
  let s : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  have hs_re : 0 < s.re := by
    norm_num [s, Complex.div_re, Complex.normSq]
    linarith
  have h1s_re : 0 < (1 - s).re := by
    norm_num [s, Complex.div_re, Complex.normSq]
    linarith
  by_cases hzeta : riemannZeta s = 0
  · have hden :
        riemannZeta ((1 / 2 : ℂ) + ε + τ * Complex.I) = 0 := by
      simpa only [s] using hzeta
    rw [baezDuarteZetaRatio, norm_div, hden, norm_zero, div_zero]
    exact norm_nonneg _
  · have harg :
        (1 / 2 : ℂ) - ε + τ * Complex.I =
          (starRingEnd ℂ) (1 - s) := by
      apply Complex.ext <;> simp [s]
      ring
    have hnum :
        ‖riemannZeta ((1 / 2 : ℂ) - ε + τ * Complex.I)‖ =
          ‖riemannZeta (1 - s)‖ := by
      rw [harg, riemannZeta_conj]
      simpa only [starRingEnd_apply] using Complex.norm_conj (riemannZeta (1 - s))
    have hratio := riemannZeta_one_sub_div s hs_re h1s_re hzeta
    rw [baezDuarteZetaRatio, show (1 / 2 : ℂ) + ε + τ * Complex.I = s by rfl,
      norm_div, hnum, ← norm_div, hratio]

/-- On the symmetric points used by Baez-Duarte, the completed Gamma quotient splits into the
ordinary Gamma quotient and the decaying real factor `π ^ (-ε)`. -/
theorem norm_Gammaℝ_div_symmetric_eq (ε τ : ℝ) :
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ε + τ * Complex.I) /
        Complex.Gammaℝ (1 - ((1 / 2 : ℂ) + ε + τ * Complex.I))‖ =
      Real.pi ^ (-ε) *
        ‖Complex.Gamma ((1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I + ε) /
          Complex.Gamma ((1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I)‖ := by
  let s : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  let z : ℂ := (1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I
  have hs_half : s / 2 = z + ε := by
    apply Complex.ext <;> simp [s, z]
    ring
  have h1s_half : (1 - s) / 2 = (starRingEnd ℂ) z := by
    rw [starRingEnd_apply]
    apply Complex.ext <;>
      norm_num [s, z, Complex.div_re, Complex.normSq] <;> ring
  have hpower :
      ‖(Real.pi : ℂ) ^ (-s / 2)‖ /
          ‖(Real.pi : ℂ) ^ (-(1 - s) / 2)‖ =
        Real.pi ^ (-ε) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_sub Real.pi_pos]
    congr 1
    norm_num [s, Complex.div_re, Complex.normSq]
    ring
  have hgamma :
      ‖Complex.Gamma (s / 2)‖ / ‖Complex.Gamma ((1 - s) / 2)‖ =
        ‖Complex.Gamma (z + ε) / Complex.Gamma z‖ := by
    rw [hs_half, h1s_half, Complex.Gamma_conj, norm_div]
    rw [Complex.norm_conj]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_div, norm_mul, norm_mul,
    mul_div_mul_comm, hpower, hgamma]

/-- Uniformly for `0 ≤ ε ≤ 1/4`, the completed Gamma quotient has polynomial growth with an
exponent linear in `ε`. -/
theorem exists_norm_Gammaℝ_div_symmetric_le_rpow :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ 1 / 4 →
        ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ε + τ * Complex.I) /
            Complex.Gammaℝ (1 - ((1 / 2 : ℂ) + ε + τ * Complex.I))‖ ≤
          (|τ| / 2 + 2) ^ (C * ε) := by
  obtain ⟨C, hC, hGamma⟩ :=
    exists_norm_Gamma_div_le_rpow_of_re_mem_Icc (1 / 8) (3 / 8) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro ε τ hε hε_quarter
  let z : ℂ := (1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I
  have hz_lo : (1 / 8 : ℝ) ≤ z.re := by
    norm_num [z, Complex.div_re, Complex.normSq]
    linarith
  have hz_hi : (z + ε).re ≤ (3 / 8 : ℝ) := by
    norm_num [z, Complex.div_re, Complex.normSq]
    linarith
  have hGamma_bound := hGamma z ε hz_lo hz_hi hε
  have hpi : Real.pi ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      (neg_nonpos.mpr hε)
  have him : |z.im| = |τ| / 2 := by
    norm_num [z, Complex.div_im, Complex.normSq, abs_div]
  rw [norm_Gammaℝ_div_symmetric_eq]
  calc
    Real.pi ^ (-ε) *
          ‖Complex.Gamma ((1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I + ε) /
            Complex.Gamma ((1 / 4 : ℂ) - ε / 2 + (τ / 2) * Complex.I)‖
        ≤ Real.pi ^ (-ε) * ((|z.im| + 2) ^ (C * ε)) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [z] using hGamma_bound
          · exact Real.rpow_nonneg Real.pi_pos.le _
    _ ≤ 1 * ((|z.im| + 2) ^ (C * ε)) := by
      exact mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg (by positivity) _)
    _ = (|τ| / 2 + 2) ^ (C * ε) := by
      simp only [one_mul]
      rw [him]

/-- Baez-Duarte Lemma 2.2 in the form needed for dominated convergence: the zeta quotient grows
like a fixed polynomial raised to an exponent linear in `ε`. -/
theorem exists_norm_baezDuarteZetaRatio_le_rpow :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ 1 / 4 →
        ‖baezDuarteZetaRatio ε τ‖ ≤ (|τ| / 2 + 2) ^ (C * ε) := by
  obtain ⟨C, hC, hGamma⟩ := exists_norm_Gammaℝ_div_symmetric_le_rpow
  refine ⟨C, hC, ?_⟩
  intro ε τ hε hε_quarter
  exact (norm_baezDuarteZetaRatio_le_norm_Gammaℝ_div ε τ hε
    (by linarith)).trans (hGamma ε τ hε hε_quarter)

/-- A fixed small interval of `ε` admits a normalized uniform zeta-ratio bound with exponent
strictly below the `L²` threshold. -/
theorem exists_baezDuarteZetaRatio_bound :
    ∃ C ε₀ K : ℝ,
      0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ C * ε₀ < 1 / 2 ∧ 0 < K ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ ε₀ →
        ‖baezDuarteZetaRatio ε τ‖ ≤
          K * (1 + |τ|) ^ (C * ε) := by
  obtain ⟨C, hC, hratio⟩ := exists_norm_baezDuarteZetaRatio_le_rpow
  let ε₀ : ℝ := 1 / (8 * (C + 1))
  let K : ℝ := 2 ^ (C * ε₀)
  have hden : 0 < 8 * (C + 1) := by positivity
  have hε₀ : 0 < ε₀ := by
    simp only [ε₀, one_div]
    positivity
  have hε₀_quarter : ε₀ < 1 / 4 := by
    rw [show ε₀ = 1 / (8 * (C + 1)) by rfl, div_lt_iff₀ hden]
    nlinarith
  have hCε₀ : C * ε₀ < 1 / 2 := by
    rw [show ε₀ = 1 / (8 * (C + 1)) by rfl,
      show C * (1 / (8 * (C + 1))) = C / (8 * (C + 1)) by ring,
      div_lt_iff₀ hden]
    nlinarith
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C, ε₀, K, hC, hε₀, hε₀_quarter, hCε₀, hK, ?_⟩
  intro ε τ hε hε_le
  have hε_quarter : ε ≤ 1 / 4 := le_trans hε_le hε₀_quarter.le
  have hp : 0 ≤ C * ε := mul_nonneg hC.le hε
  have hp_le : C * ε ≤ C * ε₀ :=
    mul_le_mul_of_nonneg_left hε_le hC.le
  have hbase : |τ| / 2 + 2 ≤ 2 * (1 + |τ|) := by
    linarith [abs_nonneg τ]
  have hbase_nonneg : 0 ≤ |τ| / 2 + 2 := by positivity
  have hpower :
      (|τ| / 2 + 2) ^ (C * ε) ≤
        K * (1 + |τ|) ^ (C * ε) := by
    calc
      (|τ| / 2 + 2) ^ (C * ε)
          ≤ (2 * (1 + |τ|)) ^ (C * ε) :=
        Real.rpow_le_rpow hbase_nonneg hbase hp
      _ = 2 ^ (C * ε) * (1 + |τ|) ^ (C * ε) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ 2 ^ (C * ε₀) * (1 + |τ|) ^ (C * ε) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp_le)
          (Real.rpow_nonneg (by positivity) _)
      _ = K * (1 + |τ|) ^ (C * ε) := by rfl
  exact (hratio ε τ hε hε_quarter).trans hpower

/-- The transformed zeta quotient used in the unconditional convergence passage. -/
def baezDuarteZetaRatioIntegrand (ε τ : ℝ) : ℂ :=
  baezDuarteZetaRatio ε τ /
    ((1 / 2 : ℂ) - ε + τ * Complex.I)

theorem one_div_norm_baezDuarteDenominator_le
    (ε τ : ℝ) (hε_quarter : ε ≤ 1 / 4) :
    1 / ‖(1 / 2 : ℂ) - ε + τ * Complex.I‖ ≤
      5 / (1 + |τ|) := by
  let z : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
  have hz_re : (1 / 4 : ℝ) ≤ z.re := by
    norm_num [z, Complex.div_re, Complex.normSq]
    linarith
  have hz_norm : (1 / 4 : ℝ) ≤ ‖z‖ :=
    hz_re.trans (Complex.re_le_norm z)
  have him_norm : |τ| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    norm_num [z, Complex.div_im, Complex.normSq] at h
    simpa only using h
  have hz_norm_pos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz_norm
  have hbase_pos : 0 < 1 + |τ| := by positivity
  have hsum : 1 + |τ| ≤ 5 * ‖z‖ := by linarith
  change 1 / ‖z‖ ≤ 5 / (1 + |τ|)
  exact (div_le_div_iff₀ hz_norm_pos hbase_pos).2 (by simpa using hsum)

/-- A single `L²` function dominates the transformed zeta quotients for every sufficiently small
nonnegative `ε`. This is the domination consequence of Baez-Duarte Lemma 2.2. -/
theorem exists_baezDuarteZetaRatioIntegrand_majorant :
    ∃ C ε₀ K : ℝ,
      0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ C * ε₀ < 1 / 2 ∧ 0 < K ∧
      MemLp
        (fun τ : ℝ =>
          ((5 * K : ℝ) : ℂ) * baezDuarteVerticalMajorant (C * ε₀) τ)
        (2 : ℝ≥0∞) volume ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ ε₀ →
        ‖baezDuarteZetaRatioIntegrand ε τ‖ ≤
          ‖((5 * K : ℝ) : ℂ) * baezDuarteVerticalMajorant (C * ε₀) τ‖ := by
  obtain ⟨C, ε₀, K, hC, hε₀, hε₀_quarter, hCε₀, hK, hratio⟩ :=
    exists_baezDuarteZetaRatio_bound
  have hmajorant :
      MemLp
        (fun τ : ℝ =>
          ((5 * K : ℝ) : ℂ) * baezDuarteVerticalMajorant (C * ε₀) τ)
        (2 : ℝ≥0∞) volume :=
    (baezDuarteVerticalMajorant_memLp (C * ε₀) hCε₀).const_mul
      ((5 * K : ℝ) : ℂ)
  refine ⟨C, ε₀, K, hC, hε₀, hε₀_quarter, hCε₀, hK, hmajorant, ?_⟩
  intro ε τ hε hε_le
  let A : ℝ := 1 + |τ|
  let β : ℝ := C * ε₀
  have hA : 1 ≤ A := by
    simp only [A]
    linarith [abs_nonneg τ]
  have hp_le : C * ε ≤ β := by
    exact mul_le_mul_of_nonneg_left hε_le hC.le
  have hratio' :
      ‖baezDuarteZetaRatio ε τ‖ ≤ K * A ^ β := by
    calc
      ‖baezDuarteZetaRatio ε τ‖ ≤ K * A ^ (C * ε) := by
        simpa only [A] using hratio ε τ hε hε_le
      _ ≤ K * A ^ β := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hA hp_le) hK.le
  have hε_quarter : ε ≤ 1 / 4 := le_trans hε_le hε₀_quarter.le
  have hdenominator := one_div_norm_baezDuarteDenominator_le ε τ hε_quarter
  rw [baezDuarteZetaRatioIntegrand, norm_div]
  calc
    ‖baezDuarteZetaRatio ε τ‖ /
          ‖(1 / 2 : ℂ) - ε + τ * Complex.I‖ =
        ‖baezDuarteZetaRatio ε τ‖ *
          (1 / ‖(1 / 2 : ℂ) - ε + τ * Complex.I‖) := by ring
    _ ≤ (K * A ^ β) *
          (1 / ‖(1 / 2 : ℂ) - ε + τ * Complex.I‖) := by
      exact mul_le_mul_of_nonneg_right hratio' (by positivity)
    _ ≤ (K * A ^ β) * (5 / A) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [A] using hdenominator
      · exact mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)
    _ = 5 * K * A ^ (-1 + β) := by
      rw [show -1 + β = β - 1 by ring, Real.rpow_sub (by positivity),
        Real.rpow_one]
      ring
    _ = ‖((5 * K : ℝ) : ℂ) *
          baezDuarteVerticalMajorant (C * ε₀) τ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 5 * K),
        baezDuarteVerticalMajorant, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end LeanLab.Riemann
