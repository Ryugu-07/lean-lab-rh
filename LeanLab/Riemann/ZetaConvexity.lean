import LeanLab.Riemann.BaezDuarteZetaRatio
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.Bounds

set_option linter.style.header false

/-!
# A sufficient convexity bound for the Riemann zeta function

This file follows the corrected midpoint Phragmen-Lindelof argument of Fiori. The pole-removed
zeta function is bounded on `Re(s)=1` by Abel truncation and on `Re(s)=0` by the functional
equation and exact Gamma identities. Analytic symmetrization then interpolates the polynomial
boundary powers at the midpoint `Re(s)=1/2`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace LeanLab.Riemann

/-- The removable entire extension of `(s - 1) * zeta(s)`. -/
def zetaPoleRemoved (s : ℂ) : ℂ :=
  Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1 s

@[simp]
theorem zetaPoleRemoved_one : zetaPoleRemoved 1 = 1 := by
  simp [zetaPoleRemoved]

theorem zetaPoleRemoved_eq {s : ℂ} (hs : s ≠ 1) :
    zetaPoleRemoved s = (s - 1) * riemannZeta s := by
  simp [zetaPoleRemoved, hs]

private theorem zetaPoleRemoved_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaPoleRemoved =ᶠ[nhds s] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
  exact zetaPoleRemoved_eq (Set.mem_compl_singleton_iff.mp hw)

/-- The pole removal is an entire function, including at the patched value `s=1`. -/
theorem differentiable_zetaPoleRemoved : Differentiable ℂ zetaPoleRemoved := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (c := (1 : ℂ)) Filter.univ_mem]
  constructor
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hd : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    exact (hd.congr_of_eventuallyEq (zetaPoleRemoved_eventuallyEq hs1)).differentiableWithinAt
  · have hev : (fun w : ℂ => (w - 1) * riemannZeta w) =ᶠ[nhdsWithin 1 {(1 : ℂ)}ᶜ]
        zetaPoleRemoved := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (zetaPoleRemoved_eq (Set.mem_compl_singleton_iff.mp hw)).symm
    have hlim : Tendsto zetaPoleRemoved (nhdsWithin 1 {(1 : ℂ)}ᶜ)
        (nhds (zetaPoleRemoved 1)) := by
      rw [zetaPoleRemoved_one]
      exact Tendsto.congr' hev riemannZeta_residue_one
    exact continuousWithinAt_compl_self.mp hlim

/-- Abel summation with a finite Dirichlet sum and an explicit tail, valid on the already
formalized Abel-continuation half-plane. -/
theorem riemannZeta_eq_zetaPartialSum_sub_tail
    (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s =
      zetaPartialSum s N - (N : ℂ) ^ (1 - s) / (1 - s) -
        s * ∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u := by
  have hs_re : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htail : IntegrableOn (fun u => zetaAbelFractKernel s u)
      (Set.Ioi (N : ℝ)) volume := by
    exact IntegrableOn.mono_set (μ := volume)
      (show IntegrableOn (fun u => zetaAbelFractKernel s u) (Set.Ioi (1 : ℝ)) volume from
        ZetaAbelFractKernel.integrableOn_Ioi s hs_re)
      (fun u hu => lt_of_le_of_lt hN_real hu)
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (ZetaAbelFractKernel.intervalIntegrable s le_rfl hN_real) htail
  have habel := ZetaPartialSum.abel_formula s hs.1 N hN
  rw [riemannZeta_eq_zetaAbelContinuationFormula s hs, zetaAbelContinuationFormula]
  rw [← hsplit]
  linear_combination -habel

private theorem norm_zetaPartialSum_one_add_mul_I_le (t : ℝ) (N : ℕ) :
    ‖zetaPartialSum ((1 : ℂ) + t * Complex.I) N‖ ≤ (harmonic N : ℝ) := by
  rw [zetaPartialSum]
  calc
    ‖∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-((1 : ℂ) + t * Complex.I))‖
        ≤ ∑ n ∈ Finset.range N,
            ‖((n : ℂ) + 1) ^ (-((1 : ℂ) + t * Complex.I))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
      norm_num
      rw [Real.rpow_neg_one]
    _ = (harmonic N : ℝ) := Complex.sum_inv_natCast_add_one_real N

private theorem norm_zetaAbel_tail_le
    (s : ℂ) (hs_re : s.re = 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖s * ∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / N := by
  let μ := volume.restrict (Set.Ioi (N : ℝ))
  let g : ℝ → ℝ := fun u => u ^ (-2 : ℝ)
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hg : Integrable g μ := by
    simpa [μ, g, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hN_pos)
  have hbound : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu1 : 1 ≤ u := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      exact hNR.trans hu.le
    change ‖zetaAbelFractKernel s u‖ ≤ u ^ (-2 : ℝ)
    convert norm_zetaAbelFractKernel_le u hu1 s using 1
    rw [hs_re]
    ring
  have hint : ‖∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u‖ ≤ (N : ℝ)⁻¹ := by
    calc
      ‖∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u‖
          ≤ ∫ u in Set.Ioi (N : ℝ), g u :=
        MeasureTheory.norm_integral_le_of_norm_le hg hbound
      _ = (N : ℝ)⁻¹ := by
        change (∫ u in Set.Ioi (N : ℝ), u ^ (-2 : ℝ)) = (N : ℝ)⁻¹
        rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hN_pos]
        norm_num
        rw [Real.rpow_neg_one]
  rw [norm_mul, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hint (norm_nonneg s)

/-- The one-line zeta value is controlled by a harmonic partial sum and two explicit tails. -/
theorem norm_riemannZeta_one_add_mul_I_le
    (t : ℝ) (ht : 1 ≤ |t|) (N : ℕ) (hN : 1 ≤ N) :
    ‖riemannZeta ((1 : ℂ) + t * Complex.I)‖ ≤
      (harmonic N : ℝ) + 1 / |t| + ‖(1 : ℂ) + t * Complex.I‖ / N := by
  let s : ℂ := (1 : ℂ) + t * Complex.I
  have hs_ne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s] at him
    subst t
    norm_num at ht
  have hs_mem : s ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hs_ne (by
      rw [show s.re = 1 by simp [s]]
      exact one_lt_zetaAbelContinuationReLower)
  have hformula := riemannZeta_eq_zetaPartialSum_sub_tail s hs_mem N hN
  have hpow : ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ = 1 / |t| := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hN)]
    norm_num [s, Complex.norm_def, Complex.normSq]
  rw [hformula]
  calc
    ‖zetaPartialSum s N - (N : ℂ) ^ (1 - s) / (1 - s) -
          s * ∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u‖
        ≤ ‖zetaPartialSum s N‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖ +
            ‖s * ∫ u in Set.Ioi (N : ℝ), zetaAbelFractKernel s u‖ := by
      grw [norm_sub_le, norm_sub_le]
    _ ≤ (harmonic N : ℝ) + 1 / |t| + ‖s‖ / N := by
      gcongr
      · exact norm_zetaPartialSum_one_add_mul_I_le t N
      · exact le_of_eq hpow
      · exact norm_zetaAbel_tail_le s (by simp [s]) N hN
    _ = (harmonic N : ℝ) + 1 / |t| + ‖(1 : ℂ) + t * Complex.I‖ / N := rfl

/-- A deliberately non-optimal polynomial bound on the line `Re(s) = 1`. The exponent `1/8`
is chosen to match the integer powers in the corrected midpoint interpolation argument. -/
theorem exists_norm_riemannZeta_one_add_mul_I_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 : ℂ) + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (1 / 8 : ℝ) := by
  refine ⟨20, by norm_num, ?_⟩
  intro t ht
  let x : ℝ := 1 + |t|
  let N : ℕ := ⌈x⌉₊
  have hx_two : 2 ≤ x := by simp only [x]; linarith
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_two
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hN : 1 ≤ N := by
    exact Nat.one_le_ceil_iff.mpr hx_pos
  have hxN : x ≤ (N : ℝ) := by
    exact Nat.le_ceil x
  have hN_two_x : (N : ℝ) ≤ 2 * x := by
    exact Nat.ceil_le_two_mul (by linarith [hx_two])
  have hx_rpow_one : 1 ≤ x ^ (1 / 8 : ℝ) := by
    exact Real.one_le_rpow (by linarith [hx_two]) (by norm_num)
  have htwo_rpow : (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hN_rpow : (N : ℝ) ^ (1 / 8 : ℝ) ≤ 2 * x ^ (1 / 8 : ℝ) := by
    calc
      (N : ℝ) ^ (1 / 8 : ℝ) ≤ (2 * x) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hN_two_x (by norm_num)
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) :=
        Real.mul_rpow (by norm_num) hx_nonneg
      _ ≤ 2 * x ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right htwo_rpow (Real.rpow_nonneg hx_nonneg _)
  have hharmonic : (harmonic N : ℝ) ≤ 17 * x ^ (1 / 8 : ℝ) := by
    have hlog := Real.log_natCast_le_rpow_div N (show (0 : ℝ) < 1 / 8 by norm_num)
    norm_num at hlog
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
      _ ≤ 1 + 8 * (N : ℝ) ^ (1 / 8 : ℝ) := by linarith
      _ ≤ 17 * x ^ (1 / 8 : ℝ) := by nlinarith
  have htail_one : 1 / |t| ≤ x ^ (1 / 8 : ℝ) := by
    have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
    have hdiv : 1 / |t| ≤ 1 := (div_le_one ht_pos).mpr ht
    exact hdiv.trans hx_rpow_one
  have hnorm : ‖(1 : ℂ) + t * Complex.I‖ ≤ x := by
    calc
      ‖(1 : ℂ) + t * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = x := by simp [x, Real.norm_eq_abs]
  have htail_two : ‖(1 : ℂ) + t * Complex.I‖ / N ≤ x ^ (1 / 8 : ℝ) := by
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hquot : ‖(1 : ℂ) + t * Complex.I‖ / N ≤ 1 := by
      rw [div_le_one hN_pos]
      exact hnorm.trans hxN
    exact hquot.trans hx_rpow_one
  calc
    ‖riemannZeta ((1 : ℂ) + t * Complex.I)‖
        ≤ (harmonic N : ℝ) + 1 / |t| + ‖(1 : ℂ) + t * Complex.I‖ / N :=
      norm_riemannZeta_one_add_mul_I_le t ht N hN
    _ ≤ 20 * x ^ (1 / 8 : ℝ) := by nlinarith
    _ = 20 * (1 + |t|) ^ (1 / 8 : ℝ) := rfl

private theorem sin_pi_mul_I (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.sinh (Real.pi * t) : ℂ) * Complex.I := by
  rw [show (Real.pi : ℂ) * ((t : ℂ) * Complex.I) =
    ((Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  simpa [Complex.ofReal_sinh] using
    (Complex.sin_mul_I ((Real.pi * t : ℝ) : ℂ))

/-- Exact norm-square formula on the line `Re(s) = 1`, away from its removable expression at
`t = 0`. -/
theorem norm_Gamma_one_add_mul_I_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      Real.pi * t / Real.sinh (Real.pi * t) := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hz : z ≠ 0 := by simp [z, ht]
  have hsinh : Real.sinh (Real.pi * t) ≠ 0 := by
    intro hsinh_zero
    have harg : Real.pi * t = 0 := by
      apply Real.sinh_injective
      simpa only [Real.sinh_zero] using hsinh_zero
    exact ht (mul_eq_zero.mp harg |>.resolve_left Real.pi_ne_zero)
  have hconj : (starRingEnd ℂ) ((1 : ℂ) + z) = 1 - z := by
    apply Complex.ext <;> simp [z]
  have hleft :
      Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - z) =
        ((‖Complex.Gamma ((1 : ℂ) + z)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcomplex :
      ((‖Complex.Gamma ((1 : ℂ) + z)‖ ^ 2 : ℝ) : ℂ) =
        ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
    calc
      ((‖Complex.Gamma ((1 : ℂ) + z)‖ ^ 2 : ℝ) : ℂ) =
          Complex.Gamma ((1 : ℂ) + z) * Complex.Gamma (1 - z) := hleft.symm
      _ = z * (Complex.Gamma z * Complex.Gamma (1 - z)) := by
        rw [show (1 : ℂ) + z = z + 1 by ring, Complex.Gamma_add_one z hz]
        ring
      _ = z * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z)) := by
        rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = ((Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
        rw [show Complex.sin ((Real.pi : ℂ) * z) =
          (Real.sinh (Real.pi * t) : ℂ) * Complex.I by simpa [z] using sin_pi_mul_I t]
        push_cast
        field_simp
        ring
  simpa [z] using Complex.ofReal_injective hcomplex

private theorem norm_cos_pi_one_sub_mul_I_div_two_sq (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * ((1 : ℂ) - t * Complex.I) / 2)‖ ^ 2 =
      Real.sinh (Real.pi * t / 2) ^ 2 := by
  have harg :
      (Real.pi : ℂ) * ((1 : ℂ) - t * Complex.I) / 2 =
        (Real.pi : ℂ) / 2 - ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_pi_div_two_sub, Complex.sin_mul_I,
    ← Complex.ofReal_sinh, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, sq_abs]

/-- The exponential factors in `Gamma (1-it)` and `cos (pi(1-it)/2)` cancel exactly, leaving
only square-root growth. -/
theorem norm_Gamma_mul_cos_one_sub_mul_I_le (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) - t * Complex.I) *
        Complex.cos ((Real.pi : ℂ) * ((1 : ℂ) - t * Complex.I) / 2)‖ ≤
      Real.sqrt (Real.pi * |t| / 2) := by
  let u : ℝ := Real.pi * t / 2
  have hu : u ≠ 0 := by
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero ht) (by norm_num)
  have hsinh_u : Real.sinh u ≠ 0 := by
    intro hsinh_zero
    apply hu
    apply Real.sinh_injective
    simpa only [Real.sinh_zero] using hsinh_zero
  have hcosh_u : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hproduct_sq :
      ‖Complex.Gamma ((1 : ℂ) - t * Complex.I) *
          Complex.cos ((Real.pi : ℂ) * ((1 : ℂ) - t * Complex.I) / 2)‖ ^ 2 =
        Real.pi * t / 2 * Real.tanh u := by
    rw [norm_mul, mul_pow]
    have hgamma :
        ‖Complex.Gamma ((1 : ℂ) - t * Complex.I)‖ ^ 2 =
          Real.pi * (-t) / Real.sinh (Real.pi * (-t)) := by
      rw [show (1 : ℂ) - t * Complex.I = (1 : ℂ) + (-t) * Complex.I by
        push_cast
        ring]
      simpa only [Complex.ofReal_neg] using
        norm_Gamma_one_add_mul_I_sq (-t) (neg_ne_zero.mpr ht)
    rw [hgamma, norm_cos_pi_one_sub_mul_I_div_two_sq]
    have harg : Real.pi * t = 2 * u := by simp [u]; ring
    rw [show Real.pi * (-t) = -(Real.pi * t) by ring, Real.sinh_neg, neg_div_neg_eq,
      show Real.pi * t / 2 = u by rfl, harg, Real.sinh_two_mul,
      Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hproduct_sq_le :
      ‖Complex.Gamma ((1 : ℂ) - t * Complex.I) *
          Complex.cos ((Real.pi : ℂ) * ((1 : ℂ) - t * Complex.I) / 2)‖ ^ 2 ≤
        Real.pi * |t| / 2 := by
    rw [hproduct_sq]
    calc
      Real.pi * t / 2 * Real.tanh u ≤ |Real.pi * t / 2 * Real.tanh u| :=
        le_abs_self _
      _ = Real.pi * |t| / 2 * |Real.tanh u| := by
        rw [abs_mul, abs_div, abs_mul, abs_of_pos Real.pi_pos]
        norm_num
      _ ≤ Real.pi * |t| / 2 * 1 := by
        exact mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one u).le (by positivity)
      _ = Real.pi * |t| / 2 := by ring
  refine (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
  rw [Real.sq_sqrt (by positivity)]
  exact hproduct_sq_le

/-- The functional equation transfers the `1/8` bound from `Re(s)=1` to a `5/8` bound on
`Re(s)=0`. -/
theorem exists_norm_riemannZeta_mul_I_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta (t * Complex.I)‖ ≤ C * (1 + |t|) ^ (5 / 8 : ℝ) := by
  obtain ⟨C, hC, hright⟩ := exists_norm_riemannZeta_one_add_mul_I_le_rpow
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro t ht
  let x : ℝ := 1 + |t|
  let s : ℂ := (1 : ℂ) - t * Complex.I
  have ht_ne : t ≠ 0 := by
    intro ht_zero
    subst t
    norm_num at ht
  have hx_pos : 0 < x := by simp only [x]; positivity
  have hs_nat : ∀ n : ℕ, s ≠ -n := by
    intro n hs
    have hre := congrArg Complex.re hs
    norm_num [s] at hre
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs_one : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    exact ht_ne him
  have hfe :
      riemannZeta (t * Complex.I) =
        2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s *
          Complex.cos (Real.pi * s / 2) * riemannZeta s := by
    convert riemannZeta_one_sub (s := s) hs_nat hs_one using 1 <;> simp only [s] <;> ring
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = 1 / (2 * Real.pi) := by
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    norm_num [s]
    rw [Real.rpow_neg_one]
    field_simp
  have hscalar : 2 * (1 / (2 * Real.pi)) ≤ 1 := by
    have heq : 2 * (1 / (2 * Real.pi)) = 1 / Real.pi := by
      field_simp
    rw [heq]
    exact (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have hgamma :
      ‖Complex.Gamma s * Complex.cos (Real.pi * s / 2)‖ ≤ 2 * Real.sqrt x := by
    have hraw := norm_Gamma_mul_cos_one_sub_mul_I_le t ht_ne
    have hsqrt : Real.sqrt (Real.pi * |t| / 2) ≤ 2 * Real.sqrt x := by
      have hrhs_nonneg : 0 ≤ 2 * Real.sqrt x :=
        mul_nonneg (by norm_num) (Real.sqrt_nonneg x)
      refine (sq_le_sq₀ (a := Real.sqrt (Real.pi * |t| / 2))
        (b := 2 * Real.sqrt x) (Real.sqrt_nonneg _) hrhs_nonneg).mp ?_
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hx_pos.le]
      norm_num
      have habs_le : |t| ≤ x := by simp [x]
      nlinarith [Real.pi_le_four, abs_nonneg t]
    have hraw' :
        ‖Complex.Gamma s * Complex.cos (Real.pi * s / 2)‖ ≤
          Real.sqrt (Real.pi * |t| / 2) := by
      simpa only [s] using hraw
    exact hraw'.trans hsqrt
  have hright_s : ‖riemannZeta s‖ ≤ C * x ^ (1 / 8 : ℝ) := by
    have hs_arg : s = (1 : ℂ) + (-t) * Complex.I := by
      simp only [s]
      push_cast
      ring
    rw [hs_arg]
    simpa only [Complex.ofReal_neg, x, abs_neg] using hright (-t) (by simpa using ht)
  rw [hfe]
  calc
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
          Complex.cos (Real.pi * s / 2) * riemannZeta s‖
        = (2 * (1 / (2 * Real.pi))) *
            ‖Complex.Gamma s * Complex.cos (Real.pi * s / 2)‖ * ‖riemannZeta s‖ := by
          have hnorm_two : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
          simp only [norm_mul, hpow, hnorm_two]
          ring
    _ ≤ 1 * (2 * Real.sqrt x) * ‖riemannZeta s‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hscalar hgamma (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    _ ≤ 1 * (2 * Real.sqrt x) * (C * x ^ (1 / 8 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hright_s (by positivity)
    _ = 2 * C * x ^ (5 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc
        1 * (2 * x ^ (1 / 2 : ℝ)) * (C * x ^ (1 / 8 : ℝ)) =
            2 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ)) := by ring
        _ = 2 * C * x ^ (5 / 8 : ℝ) := by
          rw [← Real.rpow_add hx_pos]
          norm_num
    _ = 2 * C * (1 + |t|) ^ (5 / 8 : ℝ) := rfl

/-- The pole-removed zeta function has exponent `9/8` on the right edge of the strip. -/
theorem exists_norm_zetaPoleRemoved_one_add_mul_I_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖zetaPoleRemoved ((1 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (9 / 8 : ℝ) := by
  obtain ⟨C, hC, hzeta⟩ := exists_norm_riemannZeta_one_add_mul_I_le_rpow
  refine ⟨C, hC, ?_⟩
  intro t ht
  let x : ℝ := 1 + |t|
  have hx_pos : 0 < x := by simp only [x]; positivity
  have hs_ne : (1 : ℂ) + t * Complex.I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    subst t
    norm_num at ht
  rw [zetaPoleRemoved_eq hs_ne, norm_mul]
  have hfactor : ‖(1 : ℂ) + t * Complex.I - 1‖ ≤ x := by
    simp [x, Real.norm_eq_abs]
  calc
    ‖(1 : ℂ) + t * Complex.I - 1‖ * ‖riemannZeta ((1 : ℂ) + t * Complex.I)‖
        ≤ x * (C * x ^ (1 / 8 : ℝ)) :=
      mul_le_mul hfactor (by simpa only [x] using hzeta t ht) (norm_nonneg _) hx_pos.le
    _ = C * x ^ (9 / 8 : ℝ) := by
      calc
        x * (C * x ^ (1 / 8 : ℝ)) =
            C * (x ^ (1 : ℝ) * x ^ (1 / 8 : ℝ)) := by rw [Real.rpow_one]; ring
        _ = C * x ^ (9 / 8 : ℝ) := by
          rw [← Real.rpow_add hx_pos]
          norm_num
    _ = C * (1 + |t|) ^ (9 / 8 : ℝ) := rfl

/-- The pole-removed zeta function has exponent `13/8` on the left edge of the strip. -/
theorem exists_norm_zetaPoleRemoved_mul_I_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖zetaPoleRemoved (t * Complex.I)‖ ≤ C * (1 + |t|) ^ (13 / 8 : ℝ) := by
  obtain ⟨C, hC, hzeta⟩ := exists_norm_riemannZeta_mul_I_le_rpow
  refine ⟨C, hC, ?_⟩
  intro t ht
  let x : ℝ := 1 + |t|
  have hx_pos : 0 < x := by simp only [x]; positivity
  have hs_ne : (t : ℂ) * Complex.I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num at hre
  rw [zetaPoleRemoved_eq hs_ne, norm_mul]
  have hfactor : ‖(t : ℂ) * Complex.I - 1‖ ≤ x := by
    calc
      ‖(t : ℂ) * Complex.I - 1‖ ≤ ‖(t : ℂ) * Complex.I‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = x := by simp [x, Real.norm_eq_abs, add_comm]
  calc
    ‖(t : ℂ) * Complex.I - 1‖ * ‖riemannZeta (t * Complex.I)‖
        ≤ x * (C * x ^ (5 / 8 : ℝ)) :=
      mul_le_mul hfactor (by simpa only [x] using hzeta t ht) (norm_nonneg _) hx_pos.le
    _ = C * x ^ (13 / 8 : ℝ) := by
      calc
        x * (C * x ^ (5 / 8 : ℝ)) =
            C * (x ^ (1 : ℝ) * x ^ (5 / 8 : ℝ)) := by rw [Real.rpow_one]; ring
        _ = C * x ^ (13 / 8 : ℝ) := by
          rw [← Real.rpow_add hx_pos]
          norm_num
    _ = C * (1 + |t|) ^ (13 / 8 : ℝ) := rfl

end LeanLab.Riemann
