import LeanLab.Riemann.HardyCriticalLineSign
import LeanLab.Riemann.DeBruijnNewman

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's Abel-moment amplification

This module formalizes the contradiction consumer in Hardy's 1914 proof. The source Abel
moment law remains an explicit hypothesis.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- Hardy's source integrand before taking the left Abel limit at `pi / 2`. -/
def hardyXiAbelMomentIntegrand (alpha : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  ((Real.exp (alpha * t) + Real.exp (-alpha * t)) *
      t ^ (2 * p) * hardyXi (2 * t)) /
    (1 / 4 + 4 * t ^ 2)

/-- Hardy's interior Abel moment over the positive half-line. -/
def hardyXiAbelMoment (alpha : ℝ) (p : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi 0, hardyXiAbelMomentIntegrand alpha p t

/-- The exact analytic input extracted from Hardy's equations (2)--(4).

The endpoint is a one-sided Abel limit. No boundary integrability is included. -/
structure HardyXiAbelMomentLaw : Prop where
  integrable :
    ∀ alpha p, |alpha| < Real.pi / 2 →
      IntegrableOn (hardyXiAbelMomentIntegrand alpha p) (Ioi 0)
  tendsto :
    ∀ p,
      Tendsto (fun alpha ↦ hardyXiAbelMoment alpha p)
        (𝓝[<] (Real.pi / 2))
        (𝓝 (((-1 : ℝ) ^ p) * Real.pi * Real.cos (Real.pi / 8) /
          4 ^ (2 * p)))

theorem hardyXi_two_mul_eq_deBruijnNewmanH_zero_four_mul (t : ℝ) :
    hardyXi (2 * t) =
      8 * (deBruijnNewmanH 0 (4 * t)).re := by
  have hpoint :
      ((1 + Complex.I * (4 * t : ℂ)) / 2) =
        hardyCriticalLinePoint (2 * t) := by
    apply Complex.ext
    · simp [hardyCriticalLinePoint]
    · simp [hardyCriticalLinePoint]
      ring
  rw [deBruijnNewmanH_zero_eq_riemannXi, hpoint]
  change (riemannXi (hardyCriticalLinePoint (2 * t))).re =
    8 * (((1 / 8 : ℂ) * riemannXi (hardyCriticalLinePoint (2 * t))).re)
  norm_num
  ring

theorem continuous_hardyXiAbelMomentIntegrand (alpha : ℝ) (p : ℕ) :
    Continuous (hardyXiAbelMomentIntegrand alpha p) := by
  unfold hardyXiAbelMomentIntegrand
  have hexp : Continuous (fun t : ℝ ↦ Real.exp (alpha * t)) := by fun_prop
  have hexpNeg : Continuous (fun t : ℝ ↦ Real.exp (-alpha * t)) := by fun_prop
  have hpow : Continuous (fun t : ℝ ↦ t ^ (2 * p)) := by fun_prop
  have hxi : Continuous (fun t : ℝ ↦ hardyXi (2 * t)) :=
    continuous_hardyXi.comp (by fun_prop)
  have hden : Continuous (fun t : ℝ ↦ 1 / 4 + 4 * t ^ 2) := by fun_prop
  exact (((hexp.add hexpNeg).mul hpow).mul hxi).div hden fun t ↦ by positivity

private theorem cos_pi_div_eight_pos :
    0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

private theorem hardyXiAbel_odd_limit_neg (n : ℕ) :
    ((-1 : ℝ) ^ (2 * n + 1)) * Real.pi * Real.cos (Real.pi / 8) /
        4 ^ (2 * (2 * n + 1)) < 0 := by
  have heven : (-1 : ℝ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  have hodd : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, heven]
    norm_num
  rw [hodd]
  have hpc : 0 < Real.pi * Real.cos (Real.pi / 8) :=
    mul_pos Real.pi_pos cos_pi_div_eight_pos
  have hnum : -1 * Real.pi * Real.cos (Real.pi / 8) < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hnum (by positivity)

private theorem hardyXiAbel_even_limit_pos (n : ℕ) :
    0 < ((-1 : ℝ) ^ (2 * n)) * Real.pi * Real.cos (Real.pi / 8) /
        4 ^ (2 * (2 * n)) := by
  have heven : (-1 : ℝ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven]
  have hpc : 0 < Real.pi * Real.cos (Real.pi / 8) :=
    mul_pos Real.pi_pos cos_pi_div_eight_pos
  have hnum : 0 < 1 * Real.pi * Real.cos (Real.pi / 8) := by
    simpa using hpc
  exact div_pos hnum (by positivity)

theorem exists_interior_hardyXiAbelMoment_odd_neg
    (hLaw : HardyXiAbelMomentLaw) (n : ℕ) :
    ∃ alpha : ℝ,
      0 < alpha ∧ alpha < Real.pi / 2 ∧
        hardyXiAbelMoment alpha (2 * n + 1) < 0 := by
  have hneg := hardyXiAbel_odd_limit_neg n
  have hevent :
      ∀ᶠ alpha in 𝓝[<] (Real.pi / 2),
        hardyXiAbelMoment alpha (2 * n + 1) < 0 :=
    (hLaw.tendsto (2 * n + 1)).eventually
      (eventually_lt_nhds hneg)
  have hpi : 0 < Real.pi / 2 := by positivity
  have hboth :
      ∀ᶠ alpha in 𝓝[<] (Real.pi / 2),
        hardyXiAbelMoment alpha (2 * n + 1) < 0 ∧
          alpha < Real.pi / 2 ∧ 0 < alpha := by
    filter_upwards [hevent, self_mem_nhdsWithin,
      (eventually_gt_nhds hpi).filter_mono nhdsWithin_le_nhds]
        with alpha hmoment halpha hpositive
    exact ⟨hmoment, halpha, hpositive⟩
  obtain ⟨alpha, hmoment, halpha, hpositive⟩ := hboth.exists
  exact ⟨alpha, hpositive, halpha, hmoment⟩

theorem exists_interior_hardyXiAbelMoment_even_pos
    (hLaw : HardyXiAbelMomentLaw) (n : ℕ) :
    ∃ alpha : ℝ,
      0 < alpha ∧ alpha < Real.pi / 2 ∧
        0 < hardyXiAbelMoment alpha (2 * n) := by
  have hpos := hardyXiAbel_even_limit_pos n
  have hevent :
      ∀ᶠ alpha in 𝓝[<] (Real.pi / 2),
        0 < hardyXiAbelMoment alpha (2 * n) :=
    (hLaw.tendsto (2 * n)).eventually
      (eventually_gt_nhds hpos)
  have hpi : 0 < Real.pi / 2 := by positivity
  have hboth :
      ∀ᶠ alpha in 𝓝[<] (Real.pi / 2),
        0 < hardyXiAbelMoment alpha (2 * n) ∧
          alpha < Real.pi / 2 ∧ 0 < alpha := by
    filter_upwards [hevent, self_mem_nhdsWithin,
      (eventually_gt_nhds hpi).filter_mono nhdsWithin_le_nhds]
        with alpha hmoment halpha hpositive
    exact ⟨hmoment, halpha, hpositive⟩
  obtain ⟨alpha, hmoment, halpha, hpositive⟩ := hboth.exists
  exact ⟨alpha, hpositive, halpha, hmoment⟩

private theorem hardyXiAbelMomentIntegrand_pos
    {alpha t : ℝ} {p : ℕ} (_halpha : 0 < alpha) (ht : 0 < t)
    (hxi : 0 < hardyXi (2 * t)) :
    0 < hardyXiAbelMomentIntegrand alpha p t := by
  unfold hardyXiAbelMomentIntegrand
  positivity

private theorem hardyXiAbelMomentIntegrand_neg
    {alpha t : ℝ} {p : ℕ} (_halpha : 0 < alpha) (ht : 0 < t)
    (hxi : hardyXi (2 * t) < 0) :
    hardyXiAbelMomentIntegrand alpha p t < 0 := by
  unfold hardyXiAbelMomentIntegrand
  have hweight :
      0 < (Real.exp (alpha * t) + Real.exp (-alpha * t)) * t ^ (2 * p) := by
    positivity
  have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hweight hxi) hden

private theorem exists_hardyXiAbelMoment_initial_bound
    {T : ℝ} (hT : 1 < T) :
    ∃ K : ℝ, 0 < K ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < Real.pi / 2 →
        ∀ p : ℕ,
          ‖∫ t : ℝ in Ioc 0 T, hardyXiAbelMomentIntegrand alpha p t‖ ≤
            K * T ^ (2 * p) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * T))).exists_bound_of_continuousOn
      continuous_hardyXi.continuousOn
  let M₁ : ℝ := max M 1
  let E : ℝ := Real.exp ((Real.pi / 2) * T) + 1
  let K : ℝ := 4 * E * M₁ * T
  have hM₁_pos : 0 < M₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hE_pos : 0 < E := by
    dsimp only [E]
    positivity
  have hK_pos : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK_pos, ?_⟩
  intro alpha halpha halphaPi p
  have hpoint :
      ∀ t ∈ Ioc (0 : ℝ) T,
        ‖hardyXiAbelMomentIntegrand alpha p t‖ ≤
          (4 * E * M₁) * T ^ (2 * p) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    have htwoT : 2 * t ∈ Icc (0 : ℝ) (2 * T) := by
      constructor <;> nlinarith
    have hxi : |hardyXi (2 * t)| ≤ M₁ := by
      have hbound := hM (2 * t) htwoT
      have hboundAbs : |hardyXi (2 * t)| ≤ M := by
        simpa [Real.norm_eq_abs] using hbound
      exact hboundAbs.trans (le_max_left _ _)
    have halphaMul :
        alpha * t ≤ (Real.pi / 2) * T :=
      mul_le_mul halphaPi.le htT ht0.le (by positivity)
    have hexpAlpha :
        Real.exp (alpha * t) ≤ Real.exp ((Real.pi / 2) * T) :=
      Real.exp_le_exp.mpr halphaMul
    have hexpNeg : Real.exp (-alpha * t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_pos halpha ht0])
    have hexp :
        Real.exp (alpha * t) + Real.exp (-alpha * t) ≤ E := by
      dsimp only [E]
      linarith
    have hpow : t ^ (2 * p) ≤ T ^ (2 * p) := by
      gcongr
    have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
    have hquarter : (1 / 4 : ℝ) ≤ 1 / 4 + 4 * t ^ 2 := by
      nlinarith [sq_nonneg t]
    rw [Real.norm_eq_abs, hardyXiAbelMomentIntegrand, abs_div, abs_mul, abs_mul,
      abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _)),
      abs_pow, abs_of_pos ht0, abs_of_pos hden]
    calc
      (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
            t ^ (2 * p) * |hardyXi (2 * t)| /
          (1 / 4 + 4 * t ^ 2) ≤
          E * T ^ (2 * p) * M₁ / (1 / 4) := by
        gcongr
      _ = (4 * E * M₁) * T ^ (2 * p) := by ring
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Ioc (0 : ℝ) T) measure_Ioc_lt_top hpoint
  calc
    ‖∫ t : ℝ in Ioc 0 T, hardyXiAbelMomentIntegrand alpha p t‖ ≤
        (4 * E * M₁) * T ^ (2 * p) * T := by
      simpa only [Measure.real, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal hT0.le] using hnorm
    _ = K * T ^ (2 * p) := by
      dsimp only [K]
      ring

private def hardyXiAbelPositiveBase (t : ℝ) : ℝ :=
  hardyXi (2 * t) / (1 / 4 + 4 * t ^ 2)

private theorem continuous_hardyXiAbelPositiveBase :
    Continuous hardyXiAbelPositiveBase := by
  unfold hardyXiAbelPositiveBase
  refine (continuous_hardyXi.comp (by fun_prop)).div (by fun_prop) ?_
  intro t
  positivity

private theorem exists_hardyXiAbelMoment_positive_tail_bound
    (hLaw : HardyXiAbelMomentLaw) {T : ℝ} (hT : 1 < T)
    (hxi : ∀ t, T < t → 0 < hardyXi (2 * t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < Real.pi / 2 →
        ∀ p : ℕ,
          C * (2 * T) ^ (2 * p) ≤
            ∫ t : ℝ in Ioi T, hardyXiAbelMomentIntegrand alpha p t := by
  let A : ℝ := 2 * T
  let B : ℝ := A + 1
  let C : ℝ := ∫ t : ℝ in A..B, hardyXiAbelPositiveBase t
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hTA : T < A := by
    dsimp only [A]
    linarith
  have hAB : A < B := by
    dsimp only [B]
    linarith
  have hbasePos :
      ∀ t ∈ Icc A B, 0 < hardyXiAbelPositiveBase t := by
    intro t ht
    unfold hardyXiAbelPositiveBase
    exact div_pos (hxi t (hTA.trans_le ht.1)) (by positivity)
  have hC_pos : 0 < C := by
    dsimp only [C]
    apply intervalIntegral.integral_pos hAB
      continuous_hardyXiAbelPositiveBase.continuousOn
    · intro t ht
      exact (hbasePos t ⟨ht.1.le, ht.2⟩).le
    · exact ⟨A, left_mem_Icc.mpr hAB.le, hbasePos A (left_mem_Icc.mpr hAB.le)⟩
  refine ⟨C, hC_pos, ?_⟩
  intro alpha halpha halphaPi p
  have habs : |alpha| < Real.pi / 2 := by
    rw [abs_of_pos halpha]
    exact halphaPi
  have hfull : IntegrableOn
      (hardyXiAbelMomentIntegrand alpha p) (Ioi 0) :=
    hLaw.integrable alpha p habs
  have htail : IntegrableOn
      (hardyXiAbelMomentIntegrand alpha p) (Ioi T) :=
    hfull.mono_set (Ioi_subset_Ioi hT0.le)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi T)]
        hardyXiAbelMomentIntegrand alpha p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hardyXiAbelMomentIntegrand_pos halpha (hT0.trans ht)
      (hxi t ht)).le
  have hsubset : Ioc A B ⊆ Ioi T := by
    intro t ht
    exact hTA.trans ht.1
  have hinterval_le_tail :
      (∫ t : ℝ in Ioc A B, hardyXiAbelMomentIntegrand alpha p t) ≤
        ∫ t : ℝ in Ioi T, hardyXiAbelMomentIntegrand alpha p t :=
    setIntegral_mono_set htail hnonneg (ae_of_all volume hsubset)
  have hbaseInt : IntegrableOn hardyXiAbelPositiveBase (Ioc A B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB.le).mp
      (continuous_hardyXiAbelPositiveBase.intervalIntegrable A B)
  have hscaledInt :
      IntegrableOn
        (fun t : ℝ ↦ hardyXiAbelPositiveBase t * A ^ (2 * p))
        (Ioc A B) :=
    hbaseInt.mul_const _
  have hintegrandInt :
      IntegrableOn (hardyXiAbelMomentIntegrand alpha p) (Ioc A B) :=
    htail.mono_set hsubset
  have hscaled_le :
      (∫ t : ℝ in Ioc A B,
          hardyXiAbelPositiveBase t * A ^ (2 * p)) ≤
        ∫ t : ℝ in Ioc A B,
          hardyXiAbelMomentIntegrand alpha p t := by
    apply setIntegral_mono_on hscaledInt hintegrandInt measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := hT0.trans (hsubset ht)
    have hAt : A ≤ t := ht.1.le
    have hbase : 0 < hardyXiAbelPositiveBase t :=
      hbasePos t ⟨hAt, ht.2⟩
    have hpow : A ^ (2 * p) ≤ t ^ (2 * p) := by
      gcongr
    have hexpOne : 1 ≤ Real.exp (alpha * t) := Real.one_le_exp (by positivity)
    have hexpSum :
        1 ≤ Real.exp (alpha * t) + Real.exp (-alpha * t) :=
      hexpOne.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    calc
      hardyXiAbelPositiveBase t * A ^ (2 * p) ≤
          hardyXiAbelPositiveBase t * t ^ (2 * p) := by
        gcongr
      _ ≤ (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
          t ^ (2 * p) * hardyXiAbelPositiveBase t := by
        calc
          hardyXiAbelPositiveBase t * t ^ (2 * p) =
              1 * (t ^ (2 * p) * hardyXiAbelPositiveBase t) := by ring
          _ ≤ (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
              (t ^ (2 * p) * hardyXiAbelPositiveBase t) := by
            exact mul_le_mul_of_nonneg_right hexpSum
              (mul_nonneg (pow_nonneg ht0.le _) hbase.le)
          _ = (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
              t ^ (2 * p) * hardyXiAbelPositiveBase t := by ring
      _ = hardyXiAbelMomentIntegrand alpha p t := by
        unfold hardyXiAbelPositiveBase hardyXiAbelMomentIntegrand
        field_simp [show (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 by positivity]
  have hC_set :
      (∫ t : ℝ in Ioc A B, hardyXiAbelPositiveBase t) = C := by
    dsimp only [C]
    rw [intervalIntegral.integral_of_le hAB.le]
  calc
    C * (2 * T) ^ (2 * p) =
        ∫ t : ℝ in Ioc A B,
          hardyXiAbelPositiveBase t * A ^ (2 * p) := by
      rw [integral_mul_const, hC_set]
    _ ≤ ∫ t : ℝ in Ioc A B,
        hardyXiAbelMomentIntegrand alpha p t := hscaled_le
    _ ≤ ∫ t : ℝ in Ioi T,
        hardyXiAbelMomentIntegrand alpha p t := hinterval_le_tail

private def hardyXiAbelNegativeBase (t : ℝ) : ℝ :=
  -hardyXi (2 * t) / (1 / 4 + 4 * t ^ 2)

private theorem continuous_hardyXiAbelNegativeBase :
    Continuous hardyXiAbelNegativeBase := by
  unfold hardyXiAbelNegativeBase
  refine (continuous_hardyXi.comp (by fun_prop)).neg.div (by fun_prop) ?_
  intro t
  positivity

private theorem exists_hardyXiAbelMoment_negative_tail_bound
    (hLaw : HardyXiAbelMomentLaw) {T : ℝ} (hT : 1 < T)
    (hxi : ∀ t, T < t → hardyXi (2 * t) < 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < Real.pi / 2 →
        ∀ p : ℕ,
          C * (2 * T) ^ (2 * p) ≤
            -(∫ t : ℝ in Ioi T, hardyXiAbelMomentIntegrand alpha p t) := by
  let A : ℝ := 2 * T
  let B : ℝ := A + 1
  let C : ℝ := ∫ t : ℝ in A..B, hardyXiAbelNegativeBase t
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hTA : T < A := by
    dsimp only [A]
    linarith
  have hAB : A < B := by
    dsimp only [B]
    linarith
  have hbasePos :
      ∀ t ∈ Icc A B, 0 < hardyXiAbelNegativeBase t := by
    intro t ht
    unfold hardyXiAbelNegativeBase
    exact div_pos (neg_pos.mpr (hxi t (hTA.trans_le ht.1))) (by positivity)
  have hC_pos : 0 < C := by
    dsimp only [C]
    apply intervalIntegral.integral_pos hAB
      continuous_hardyXiAbelNegativeBase.continuousOn
    · intro t ht
      exact (hbasePos t ⟨ht.1.le, ht.2⟩).le
    · exact ⟨A, left_mem_Icc.mpr hAB.le, hbasePos A (left_mem_Icc.mpr hAB.le)⟩
  refine ⟨C, hC_pos, ?_⟩
  intro alpha halpha halphaPi p
  have habs : |alpha| < Real.pi / 2 := by
    rw [abs_of_pos halpha]
    exact halphaPi
  have hfull : IntegrableOn
      (hardyXiAbelMomentIntegrand alpha p) (Ioi 0) :=
    hLaw.integrable alpha p habs
  have htail : IntegrableOn
      (hardyXiAbelMomentIntegrand alpha p) (Ioi T) :=
    hfull.mono_set (Ioi_subset_Ioi hT0.le)
  have hnegTail : IntegrableOn
      (fun t : ℝ ↦ -hardyXiAbelMomentIntegrand alpha p t) (Ioi T) :=
    htail.neg
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi T)]
        (fun t : ℝ ↦ -hardyXiAbelMomentIntegrand alpha p t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (neg_pos.mpr (hardyXiAbelMomentIntegrand_neg halpha
      (hT0.trans ht) (hxi t ht))).le
  have hsubset : Ioc A B ⊆ Ioi T := by
    intro t ht
    exact hTA.trans ht.1
  have hinterval_le_tail :
      (∫ t : ℝ in Ioc A B, -hardyXiAbelMomentIntegrand alpha p t) ≤
        ∫ t : ℝ in Ioi T, -hardyXiAbelMomentIntegrand alpha p t :=
    setIntegral_mono_set hnegTail hnonneg (ae_of_all volume hsubset)
  have hbaseInt : IntegrableOn hardyXiAbelNegativeBase (Ioc A B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB.le).mp
      (continuous_hardyXiAbelNegativeBase.intervalIntegrable A B)
  have hscaledInt :
      IntegrableOn
        (fun t : ℝ ↦ hardyXiAbelNegativeBase t * A ^ (2 * p))
        (Ioc A B) :=
    hbaseInt.mul_const _
  have hnegIntegrandInt :
      IntegrableOn
        (fun t : ℝ ↦ -hardyXiAbelMomentIntegrand alpha p t) (Ioc A B) :=
    hnegTail.mono_set hsubset
  have hscaled_le :
      (∫ t : ℝ in Ioc A B,
          hardyXiAbelNegativeBase t * A ^ (2 * p)) ≤
        ∫ t : ℝ in Ioc A B,
          -hardyXiAbelMomentIntegrand alpha p t := by
    apply setIntegral_mono_on hscaledInt hnegIntegrandInt measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := hT0.trans (hsubset ht)
    have hAt : A ≤ t := ht.1.le
    have hbase : 0 < hardyXiAbelNegativeBase t :=
      hbasePos t ⟨hAt, ht.2⟩
    have hpow : A ^ (2 * p) ≤ t ^ (2 * p) := by
      gcongr
    have hexpOne : 1 ≤ Real.exp (alpha * t) := Real.one_le_exp (by positivity)
    have hexpSum :
        1 ≤ Real.exp (alpha * t) + Real.exp (-alpha * t) :=
      hexpOne.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    calc
      hardyXiAbelNegativeBase t * A ^ (2 * p) ≤
          hardyXiAbelNegativeBase t * t ^ (2 * p) := by
        gcongr
      _ ≤ (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
          t ^ (2 * p) * hardyXiAbelNegativeBase t := by
        calc
          hardyXiAbelNegativeBase t * t ^ (2 * p) =
              1 * (t ^ (2 * p) * hardyXiAbelNegativeBase t) := by ring
          _ ≤ (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
              (t ^ (2 * p) * hardyXiAbelNegativeBase t) := by
            exact mul_le_mul_of_nonneg_right hexpSum
              (mul_nonneg (pow_nonneg ht0.le _) hbase.le)
          _ = (Real.exp (alpha * t) + Real.exp (-alpha * t)) *
              t ^ (2 * p) * hardyXiAbelNegativeBase t := by ring
      _ = -hardyXiAbelMomentIntegrand alpha p t := by
        unfold hardyXiAbelNegativeBase hardyXiAbelMomentIntegrand
        field_simp [show (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 by positivity]
  have hC_set :
      (∫ t : ℝ in Ioc A B, hardyXiAbelNegativeBase t) = C := by
    dsimp only [C]
    rw [intervalIntegral.integral_of_le hAB.le]
  calc
    C * (2 * T) ^ (2 * p) =
        ∫ t : ℝ in Ioc A B,
          hardyXiAbelNegativeBase t * A ^ (2 * p) := by
      rw [integral_mul_const, hC_set]
    _ ≤ ∫ t : ℝ in Ioc A B,
        -hardyXiAbelMomentIntegrand alpha p t := hscaled_le
    _ ≤ ∫ t : ℝ in Ioi T,
        -hardyXiAbelMomentIntegrand alpha p t := hinterval_le_tail
    _ = -(∫ t : ℝ in Ioi T,
        hardyXiAbelMomentIntegrand alpha p t) := by
      rw [integral_neg]

private theorem exists_odd_hardyXiAbel_power_gap
    {K C : ℝ} (_hK : 0 < K) (hC : 0 < C) :
    ∃ n : ℕ, K < C * 2 ^ (2 * (2 * n + 1)) := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (K / (4 * C)) (by norm_num : (1 : ℝ) < 16)
  refine ⟨n, ?_⟩
  have hfourC : 0 < 4 * C := by positivity
  have hgap : K < (16 : ℝ) ^ n * (4 * C) := by
    exact (div_lt_iff₀ hfourC).mp hn
  calc
    K < (16 : ℝ) ^ n * (4 * C) := hgap
    _ = C * 2 ^ (2 * (2 * n + 1)) := by
      norm_num [pow_add, pow_mul]
      ring

private theorem exists_even_hardyXiAbel_power_gap
    {K C : ℝ} (_hK : 0 < K) (hC : 0 < C) :
    ∃ n : ℕ, K < C * 2 ^ (2 * (2 * n)) := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (K / C) (by norm_num : (1 : ℝ) < 16)
  refine ⟨n, ?_⟩
  have hgap : K < C * (16 : ℝ) ^ n := by
    simpa only [mul_comm] using (div_lt_iff₀ hC).mp hn
  calc
    K < C * (16 : ℝ) ^ n := hgap
    _ = C * 2 ^ (2 * (2 * n)) := by
      norm_num [pow_mul]

private theorem hardyXiAbelMoment_split
    {alpha T : ℝ} {p : ℕ} (hT : 0 ≤ T)
    (hint : IntegrableOn (hardyXiAbelMomentIntegrand alpha p) (Ioi 0)) :
    hardyXiAbelMoment alpha p =
      (∫ t : ℝ in Ioc 0 T, hardyXiAbelMomentIntegrand alpha p t) +
        ∫ t : ℝ in Ioi T, hardyXiAbelMomentIntegrand alpha p t := by
  unfold hardyXiAbelMoment
  rw [← Ioc_union_Ioi_eq_Ioi hT,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · exact hint.mono_set Ioc_subset_Ioi_self
  · exact hint.mono_set (Ioi_subset_Ioi hT)

theorem not_eventually_hardyXi_two_mul_pos
    (hLaw : HardyXiAbelMomentLaw) :
    ¬ ∃ T : ℝ, 1 < T ∧
      ∀ t : ℝ, T < t → 0 < hardyXi (2 * t) := by
  rintro ⟨T, hT, hxi⟩
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨K, hK, hinitial⟩ :=
    exists_hardyXiAbelMoment_initial_bound hT
  obtain ⟨C, hC, htail⟩ :=
    exists_hardyXiAbelMoment_positive_tail_bound hLaw hT hxi
  obtain ⟨n, hgap⟩ := exists_odd_hardyXiAbel_power_gap hK hC
  obtain ⟨alpha, halpha, halphaPi, hmoment⟩ :=
    exists_interior_hardyXiAbelMoment_odd_neg hLaw n
  have habs : |alpha| < Real.pi / 2 := by
    rw [abs_of_pos halpha]
    exact halphaPi
  have hint :
      IntegrableOn
        (hardyXiAbelMomentIntegrand alpha (2 * n + 1)) (Ioi 0) :=
    hLaw.integrable alpha (2 * n + 1) habs
  have hsplit :=
    hardyXiAbelMoment_split hT0.le hint
  have hinitialBound :=
    hinitial alpha halpha halphaPi (2 * n + 1)
  rw [Real.norm_eq_abs] at hinitialBound
  have htailBound :=
    htail alpha halpha halphaPi (2 * n + 1)
  have hTpow :
      0 < T ^ (2 * (2 * n + 1)) :=
    pow_pos hT0 _
  have hgrowth :
      K * T ^ (2 * (2 * n + 1)) <
        C * (2 * T) ^ (2 * (2 * n + 1)) := by
    calc
      K * T ^ (2 * (2 * n + 1)) <
          (C * 2 ^ (2 * (2 * n + 1))) *
            T ^ (2 * (2 * n + 1)) :=
        mul_lt_mul_of_pos_right hgap hTpow
      _ = C * (2 * T) ^ (2 * (2 * n + 1)) := by
        rw [mul_pow]
        ring
  have htail_lt_initial :
      (∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t) <
        |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t| := by
    calc
      (∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t) <
          -(∫ t : ℝ in Ioc 0 T,
            hardyXiAbelMomentIntegrand alpha (2 * n + 1) t) := by
        rw [hsplit] at hmoment
        linarith
      _ ≤ |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t| :=
        neg_le_abs _
  have hinitial_lt_tail :
      |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t| <
        ∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n + 1) t :=
    lt_of_le_of_lt hinitialBound (hgrowth.trans_le htailBound)
  exact (lt_asymm hinitial_lt_tail htail_lt_initial).elim

theorem not_eventually_hardyXi_two_mul_neg
    (hLaw : HardyXiAbelMomentLaw) :
    ¬ ∃ T : ℝ, 1 < T ∧
      ∀ t : ℝ, T < t → hardyXi (2 * t) < 0 := by
  rintro ⟨T, hT, hxi⟩
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨K, hK, hinitial⟩ :=
    exists_hardyXiAbelMoment_initial_bound hT
  obtain ⟨C, hC, htail⟩ :=
    exists_hardyXiAbelMoment_negative_tail_bound hLaw hT hxi
  obtain ⟨n, hgap⟩ := exists_even_hardyXiAbel_power_gap hK hC
  obtain ⟨alpha, halpha, halphaPi, hmoment⟩ :=
    exists_interior_hardyXiAbelMoment_even_pos hLaw n
  have habs : |alpha| < Real.pi / 2 := by
    rw [abs_of_pos halpha]
    exact halphaPi
  have hint :
      IntegrableOn
        (hardyXiAbelMomentIntegrand alpha (2 * n)) (Ioi 0) :=
    hLaw.integrable alpha (2 * n) habs
  have hsplit :=
    hardyXiAbelMoment_split hT0.le hint
  have hinitialBound :=
    hinitial alpha halpha halphaPi (2 * n)
  rw [Real.norm_eq_abs] at hinitialBound
  have htailBound :=
    htail alpha halpha halphaPi (2 * n)
  have hTpow :
      0 < T ^ (2 * (2 * n)) :=
    pow_pos hT0 _
  have hgrowth :
      K * T ^ (2 * (2 * n)) <
        C * (2 * T) ^ (2 * (2 * n)) := by
    calc
      K * T ^ (2 * (2 * n)) <
          (C * 2 ^ (2 * (2 * n))) * T ^ (2 * (2 * n)) :=
        mul_lt_mul_of_pos_right hgap hTpow
      _ = C * (2 * T) ^ (2 * (2 * n)) := by
        rw [mul_pow]
        ring
  have hnegTail_lt_initial :
      -(∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t) <
        |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t| := by
    calc
      -(∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t) <
          ∫ t : ℝ in Ioc 0 T,
            hardyXiAbelMomentIntegrand alpha (2 * n) t := by
        rw [hsplit] at hmoment
        linarith
      _ ≤ |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t| :=
        le_abs_self _
  have hinitial_lt_negTail :
      |∫ t : ℝ in Ioc 0 T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t| <
        -(∫ t : ℝ in Ioi T,
          hardyXiAbelMomentIntegrand alpha (2 * n) t) :=
    lt_of_le_of_lt hinitialBound (hgrowth.trans_le htailBound)
  exact (lt_asymm hinitial_lt_negTail hnegTail_lt_initial).elim

private theorem continuous_tail_has_constant_sign
    {f : ℝ → ℝ} (hf : Continuous f) {S : ℝ}
    (hnz : ∀ t, S < t → f t ≠ 0) :
    (∀ t, S < t → 0 < f t) ∨
      (∀ t, S < t → f t < 0) := by
  let t₀ : ℝ := S + 1
  have ht₀ : S < t₀ := by
    dsimp only [t₀]
    linarith
  have hne₀ : f t₀ ≠ 0 := hnz t₀ ht₀
  rcases lt_or_gt_of_ne hne₀ with hneg₀ | hpos₀
  · right
    intro t ht
    have hnet : f t ≠ 0 := hnz t ht
    rcases lt_or_gt_of_ne hnet with hneg | hpos
    · exact hneg
    · exfalso
      rcases le_total t t₀ with htt₀ | ht₀t
      · obtain ⟨u, hu, hzero⟩ :=
          intermediate_value_Icc' htt₀ hf.continuousOn ⟨hneg₀.le, hpos.le⟩
        exact hnz u (ht.trans_le hu.1) hzero
      · obtain ⟨u, hu, hzero⟩ :=
          intermediate_value_Icc ht₀t hf.continuousOn ⟨hneg₀.le, hpos.le⟩
        exact hnz u (ht₀.trans_le hu.1) hzero
  · left
    intro t ht
    have hnet : f t ≠ 0 := hnz t ht
    rcases lt_or_gt_of_ne hnet with hneg | hpos
    · exfalso
      rcases le_total t t₀ with htt₀ | ht₀t
      · obtain ⟨u, hu, hzero⟩ :=
          intermediate_value_Icc htt₀ hf.continuousOn ⟨hneg.le, hpos₀.le⟩
        exact hnz u (ht.trans_le hu.1) hzero
      · obtain ⟨u, hu, hzero⟩ :=
          intermediate_value_Icc' ht₀t hf.continuousOn ⟨hneg.le, hpos₀.le⟩
        exact hnz u (ht₀.trans_le hu.1) hzero
    · exact hpos

theorem exists_hardyXi_zero_above_of_abelMomentLaw
    (hLaw : HardyXiAbelMomentLaw) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ hardyXi t = 0 := by
  by_contra hzero
  have hnz : ∀ t : ℝ, T < t → hardyXi t ≠ 0 := by
    intro t ht htZero
    exact hzero ⟨t, ht, htZero⟩
  let S : ℝ := max 2 (T + 1)
  have hS1 : 1 < S := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hscaledNonzero :
      ∀ t : ℝ, S < t → hardyXi (2 * t) ≠ 0 := by
    intro t ht
    apply hnz
    have hTt : T < t := by
      have hST : T + 1 ≤ S := le_max_right _ _
      linarith
    have ht0 : 0 < t := by
      have hS2 : 2 ≤ S := le_max_left _ _
      linarith
    nlinarith
  have hscaledContinuous :
      Continuous (fun t : ℝ ↦ hardyXi (2 * t)) :=
    continuous_hardyXi.comp (by fun_prop)
  rcases continuous_tail_has_constant_sign hscaledContinuous hscaledNonzero with
    hpos | hneg
  · exact not_eventually_hardyXi_two_mul_pos hLaw ⟨S, hS1, hpos⟩
  · exact not_eventually_hardyXi_two_mul_neg hLaw ⟨S, hS1, hneg⟩

theorem infinite_criticalLineZeros_of_hardyXiAbelMomentLaw
    (hLaw : HardyXiAbelMomentLaw) :
    Set.Infinite {t : ℝ |
      IsNontrivialZero (hardyCriticalLinePoint t)} := by
  intro hfinite
  obtain ⟨T, hT⟩ := hfinite.bddAbove
  obtain ⟨t, hTt, hzero⟩ :=
    exists_hardyXi_zero_above_of_abelMomentLaw hLaw T
  have htmem :
      t ∈ {u : ℝ | IsNontrivialZero (hardyCriticalLinePoint u)} := by
    exact (hardyXi_eq_zero_iff_isNontrivialZero t).mp hzero
  exact (not_lt_of_ge (hT htmem)) hTt

/-- Aggregate certificate for the exact conditional Hardy 1914 contradiction consumer. -/
structure HardyXiAbelMomentAmplificationCertificate : Prop where
  scaling :
    ∀ t : ℝ,
      hardyXi (2 * t) =
        8 * (deBruijnNewmanH 0 (4 * t)).re
  oddInterior :
    ∀ (_hLaw : HardyXiAbelMomentLaw) (n : ℕ),
      ∃ alpha : ℝ,
        0 < alpha ∧ alpha < Real.pi / 2 ∧
          hardyXiAbelMoment alpha (2 * n + 1) < 0
  evenInterior :
    ∀ (_hLaw : HardyXiAbelMomentLaw) (n : ℕ),
      ∃ alpha : ℝ,
        0 < alpha ∧ alpha < Real.pi / 2 ∧
          0 < hardyXiAbelMoment alpha (2 * n)
  noPositiveTail :
    ∀ _hLaw : HardyXiAbelMomentLaw,
      ¬ ∃ T : ℝ, 1 < T ∧
        ∀ t : ℝ, T < t → 0 < hardyXi (2 * t)
  noNegativeTail :
    ∀ _hLaw : HardyXiAbelMomentLaw,
      ¬ ∃ T : ℝ, 1 < T ∧
        ∀ t : ℝ, T < t → hardyXi (2 * t) < 0
  zeroAbove :
    ∀ (_hLaw : HardyXiAbelMomentLaw) (T : ℝ),
      ∃ t : ℝ, T < t ∧ hardyXi t = 0
  infiniteZeros :
    ∀ _hLaw : HardyXiAbelMomentLaw,
      Set.Infinite {t : ℝ |
        IsNontrivialZero (hardyCriticalLinePoint t)}

theorem hardyXiAbelMomentAmplification_endpoint :
    HardyXiAbelMomentAmplificationCertificate where
  scaling := hardyXi_two_mul_eq_deBruijnNewmanH_zero_four_mul
  oddInterior := exists_interior_hardyXiAbelMoment_odd_neg
  evenInterior := exists_interior_hardyXiAbelMoment_even_pos
  noPositiveTail := not_eventually_hardyXi_two_mul_pos
  noNegativeTail := not_eventually_hardyXi_two_mul_neg
  zeroAbove := exists_hardyXi_zero_above_of_abelMomentLaw
  infiniteZeros := infinite_criticalLineZeros_of_hardyXiAbelMomentLaw

end

end LeanLab.Riemann
