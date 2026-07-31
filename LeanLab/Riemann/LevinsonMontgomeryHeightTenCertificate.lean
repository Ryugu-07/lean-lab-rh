import LeanLab.Riemann.HardyLittlewoodEtaRemainder
import LeanLab.Riemann.LevinsonMontgomeryCriticalStrip
import LeanLab.Riemann.LevinsonMontgomeryLogDerivMassBridge
import Mathlib.Analysis.Complex.Liouville

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Rigorous evaluators for the Levinson--Montgomery height-ten certificate

This module develops explicit finite-sum error bounds for the actual eta, zeta, and zeta
derivative functions needed by the low-height certificate isolated from Levinson--Montgomery's
counting argument.
-/

open Complex Filter Finset Real Set Topology
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

/-- The entire factor relating Dirichlet eta to Riemann zeta. -/
def hardyLittlewoodEtaFactor (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (1 - s)

theorem hardyLittlewoodEtaFactor_ne_zero_of_re_lt_one
    {s : ℂ} (hs : s.re < 1) :
    hardyLittlewoodEtaFactor s ≠ 0 := by
  intro hzero
  have hpow : (2 : ℂ) ^ (1 - s) = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hpow
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), norm_one] at hnorm
  have hgt : 1 < (2 : ℝ) ^ (1 - s).re := by
    exact Real.one_lt_rpow (by norm_num) (by norm_num; linarith)
  rw [hnorm] at hgt
  exact (lt_irrefl 1) hgt

/-- The finite eta-sum approximation to Riemann zeta. -/
def hardyLittlewoodZetaApprox (s : ℂ) (N : ℕ) : ℂ :=
  hardyLittlewoodEtaPartialSum s N / hardyLittlewoodEtaFactor s

/-- The differentiated finite eta-sum approximation to the zeta derivative. -/
def hardyLittlewoodZetaDerivApprox (s : ℂ) (N : ℕ) : ℂ :=
  (deriv (fun z => hardyLittlewoodEtaPartialSum z N) s *
      hardyLittlewoodEtaFactor s -
    hardyLittlewoodEtaPartialSum s N * deriv hardyLittlewoodEtaFactor s) /
    hardyLittlewoodEtaFactor s ^ 2

/-- The explicit value error radius for the finite eta quotient. -/
def hardyLittlewoodZetaError (s : ℂ) (N : ℕ) : ℝ :=
  (4 * (N : ℝ) ^ (-s.re)) / ‖hardyLittlewoodEtaFactor s‖

/-- The explicit derivative error radius obtained from a Cauchy circle of radius `r`. -/
def hardyLittlewoodZetaDerivError (s : ℂ) (r : ℝ) (N : ℕ) : ℝ :=
  (((4 * (N : ℝ) ^ (-(s.re - r))) / r) *
      ‖hardyLittlewoodEtaFactor s‖ +
    (4 * (N : ℝ) ^ (-s.re)) * ‖deriv hardyLittlewoodEtaFactor s‖) /
    ‖hardyLittlewoodEtaFactor s‖ ^ 2

/-- The complex pole/Gamma correction in the logarithmic derivative of zeta. -/
def levinsonMontgomeryLogDerivArchimedeanComplex (s : ℂ) : ℂ :=
  -1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 -
    Complex.digamma (s / 2 + 1) / 2

/-- The elementary center of the explicit digamma--Stirling enclosure. -/
def levinsonMontgomeryArchimedeanApprox (s : ℂ) : ℝ :=
  -(1 / (s - 1)).re + Real.log Real.pi / 2 -
    (Complex.log (s / 2 + 1) - 1 / (2 * (s / 2 + 1))).re / 2

/-- The radius inherited from the compiled Stieltjes digamma remainder. -/
def levinsonMontgomeryArchimedeanError (s : ℂ) : ℝ :=
  27 / (128 * ‖s / 2 + 1‖ ^ 2)

/-- A certified upper center for the sum of the two reflected pole/Gamma corrections. -/
def levinsonMontgomeryReflectedArchimedeanUpper (s : ℂ) : ℝ :=
  levinsonMontgomeryArchimedeanApprox s +
    levinsonMontgomeryArchimedeanError s +
    levinsonMontgomeryArchimedeanApprox (1 - s) +
    levinsonMontgomeryArchimedeanError (1 - s)

theorem levinsonMontgomeryLogDerivArchimedeanComplex_re (s : ℂ) :
    (levinsonMontgomeryLogDerivArchimedeanComplex s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s := by
  unfold levinsonMontgomeryLogDerivArchimedeanComplex
    levinsonMontgomeryLogDerivArchimedeanTerm
  rw [show (-1 : ℂ) / (s - 1) = -(1 / (s - 1)) by ring]
  norm_num

/-- Explicit enclosure of the real pole/Gamma correction. -/
theorem abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_approx_le
    {s : ℂ} (hs : -2 < s.re) :
    |levinsonMontgomeryLogDerivArchimedeanTerm s -
        levinsonMontgomeryArchimedeanApprox s| ≤
      levinsonMontgomeryArchimedeanError s := by
  let w : ℂ := s / 2 + 1
  have hwRe : 0 < w.re := by
    dsimp only [w]
    norm_num [div_re]
    linarith
  have hdigamma := levinsonMontgomery_digamma_stirling hwRe
  have hrem :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hwRe
  have hdiff :
      levinsonMontgomeryLogDerivArchimedeanTerm s -
          levinsonMontgomeryArchimedeanApprox s =
        -(levinsonMontgomeryDigammaStirlingRemainder w).re / 2 := by
    unfold levinsonMontgomeryLogDerivArchimedeanTerm
      levinsonMontgomeryArchimedeanApprox
    change
      (-(1 / (s - 1)).re + Real.log Real.pi / 2 -
          (Complex.digamma w).re / 2) -
          (-(1 / (s - 1)).re + Real.log Real.pi / 2 -
            (Complex.log w - 1 / (2 * w)).re / 2) = _
    rw [hdigamma]
    norm_num
    ring
  rw [hdiff, abs_div, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold levinsonMontgomeryArchimedeanError
  change
    |(levinsonMontgomeryDigammaStirlingRemainder w).re| / 2 ≤
      27 / (128 * ‖w‖ ^ 2)
  calc
    |(levinsonMontgomeryDigammaStirlingRemainder w).re| / 2 ≤
        ‖levinsonMontgomeryDigammaStirlingRemainder w‖ / 2 := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ (27 / (64 * ‖w‖ ^ 2)) / 2 := by gcongr
    _ = 27 / (128 * ‖w‖ ^ 2) := by ring

/-- Exact logarithmic-derivative decomposition with the pole moved into the shifted digamma
term, which stays regular as the real part approaches zero at nonzero height. -/
theorem logDeriv_riemannZeta_eq_logDeriv_riemannXi_add_archimedean
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = logDeriv riemannXi s +
      levinsonMontgomeryLogDerivArchimedeanComplex s := by
  have hxi :=
    logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta
      hs hs1 hzeta
  have hgamma := logDeriv_GammaR_eq_digamma hs
  have hhalfRe : 0 < (s / 2).re := by
    norm_num [div_re]
    linarith
  have hnotpole : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpsi := Complex.digamma_apply_add_one (s / 2) hnotpole
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hhalfInv : (s / 2)⁻¹ = 2 / s := by
    field_simp [hsZero]
  rw [hgamma] at hxi
  unfold levinsonMontgomeryLogDerivArchimedeanComplex
  rw [hpsi, hhalfInv]
  rw [hxi]
  simp only [div_eq_mul_inv]
  ring

/-- Nonvanishing on the reflected right-half point transfers back through the completed zeta
functional equation without evaluating the Gamma factor numerically. -/
theorem riemannZeta_ne_zero_of_one_sub_ne_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hreflected : riemannZeta (1 - s) ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hs0
    norm_num at hs0
  have hsOne : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hwRe : 0 < (1 - s).re := by
    norm_num
    linarith
  have hwZero : 1 - s ≠ 0 := sub_ne_zero.mpr hsOne.symm
  have hwOne : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hxiReflected : riemannXi (1 - s) ≠ 0 := by
    rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos
      hwRe hwOne]
    have hgamma : Gammaℝ (1 - s) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos hwRe
    have hfactor : (1 - s) * (1 - s - 1) / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hwZero (sub_ne_zero.mpr hwOne)) (by norm_num)
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) hreflected
  intro hzeta
  apply hxiReflected
  rw [riemannXi_one_sub]
  rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos
    hs0 hsOne]
  simp only [hzeta, mul_zero]

/-- Reflection turns the left-half zeta logarithmic derivative into a right-half evaluator plus
two explicit pole/Gamma corrections. -/
theorem logDeriv_riemannZeta_re_reflection
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hzeta : riemannZeta s ≠ 0)
    (hreflected : riemannZeta (1 - s) ≠ 0) :
    (logDeriv riemannZeta s).re =
      -(logDeriv riemannZeta (1 - s)).re +
        levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryLogDerivArchimedeanTerm (1 - s) := by
  have hsOne : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hwRe : 0 < (1 - s).re := by
    norm_num
    linarith
  have hwOne : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hsFormula :=
    logDeriv_riemannZeta_eq_logDeriv_riemannXi_add_archimedean
      hs0 hsOne hzeta
  have hwFormula :=
    logDeriv_riemannZeta_eq_logDeriv_riemannXi_add_archimedean
      hwRe hwOne hreflected
  have hxiReflection :
      logDeriv riemannXi s = -logDeriv riemannXi (1 - s) := by
    simpa only [sub_sub_cancel] using
      (logDeriv_riemannXi_one_sub (1 - s))
  have hcomplex :
      logDeriv riemannZeta s =
        -logDeriv riemannZeta (1 - s) +
          levinsonMontgomeryLogDerivArchimedeanComplex s +
          levinsonMontgomeryLogDerivArchimedeanComplex (1 - s) := by
    rw [hsFormula, hwFormula, hxiReflection]
    ring
  have hre := congrArg Complex.re hcomplex
  simp only [Complex.add_re, Complex.neg_re] at hre
  rw [levinsonMontgomeryLogDerivArchimedeanComplex_re,
    levinsonMontgomeryLogDerivArchimedeanComplex_re] at hre
  linarith

/-- Cauchy's estimate transfers the uniform ordered eta remainder to its first derivative. -/
theorem norm_deriv_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
    (s : ℂ) {r : ℝ} (hr : 0 < r) (hrRe : r < s.re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |s.im| + r ≤ N) :
    ‖deriv hardyLittlewoodEtaSeriesValue s -
        deriv (fun z => hardyLittlewoodEtaPartialSum z N) s‖ ≤
      (4 * (N : ℝ) ^ (-(s.re - r))) / r := by
  let U : Set ℂ := {z | 0 < z.re}
  let f : ℂ → ℂ := fun z =>
    hardyLittlewoodEtaSeriesValue z - hardyLittlewoodEtaPartialSum z N
  have hsRe : 0 < s.re := hr.trans hrRe
  have hclosed : Metric.closedBall s r ⊆ U := by
    intro z hz
    have hnorm : ‖z - s‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hreDiff : |z.re - s.re| ≤ r :=
      (Complex.abs_re_le_norm (z - s)).trans hnorm
    change 0 < z.re
    have hleft := (abs_le.mp hreDiff).1
    linarith
  have hdiffOn : DifferentiableOn ℂ f U := by
    exact differentiableOn_hardyLittlewoodEtaSeriesValue.sub
      (differentiable_hardyLittlewoodEtaPartialSum N).differentiableOn
  have hdiffCl : DiffContOnCl ℂ f (Metric.ball s r) :=
    hdiffOn.diffContOnCl_ball hclosed
  have hsphere :
      ∀ z ∈ Metric.sphere s r,
        ‖f z‖ ≤ 4 * (N : ℝ) ^ (-(s.re - r)) := by
    intro z hz
    have hnorm : ‖z - s‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hreDiff : |z.re - s.re| ≤ r :=
      (Complex.abs_re_le_norm (z - s)).trans hnorm.le
    have himDiff : |z.im - s.im| ≤ r :=
      (Complex.abs_im_le_norm (z - s)).trans hnorm.le
    have hzRe : s.re - r ≤ z.re := by
      have hleft := (abs_le.mp hreDiff).1
      linarith
    have hzRePos : 0 < z.re := by
      linarith
    have hzIm : |z.im| ≤ (N : ℝ) := by
      calc
        |z.im| = |(z.im - s.im) + s.im| := by ring_nf
        _ ≤ |z.im - s.im| + |s.im| := abs_add_le _ _
        _ ≤ r + |s.im| := by linarith
        _ = |s.im| + r := by ring
        _ ≤ (N : ℝ) := by exact_mod_cast hNim
    have hpow :
        (N : ℝ) ^ (-z.re) ≤ (N : ℝ) ^ (-(s.re - r)) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN) (by linarith)
    exact
      (norm_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
        z hzRePos hN hzIm).trans
        (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hCauchy :
      ‖deriv f s‖ ≤ (4 * (N : ℝ) ^ (-(s.re - r))) / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      hr hdiffCl hsphere
  have hopen : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsMem : s ∈ U := hsRe
  have hseriesAt : DifferentiableAt ℂ hardyLittlewoodEtaSeriesValue s :=
    (differentiableOn_hardyLittlewoodEtaSeriesValue s hsMem).differentiableAt
      (hopen.mem_nhds hsMem)
  have hpartialAt :
      DifferentiableAt ℂ (fun z => hardyLittlewoodEtaPartialSum z N) s :=
    differentiable_hardyLittlewoodEtaPartialSum N s
  simpa only [f, deriv_fun_sub hseriesAt hpartialAt] using hCauchy

/-- The first-derivative eta remainder for the actual project eta normalization. -/
theorem norm_deriv_hardyLittlewoodEta_sub_partialSum_le
    (s : ℂ) (hs_ne : s ≠ 1) {r : ℝ} (hr : 0 < r) (hrRe : r < s.re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |s.im| + r ≤ N) :
    ‖deriv hardyLittlewoodEta s -
        deriv (fun z => hardyLittlewoodEtaPartialSum z N) s‖ ≤
      (4 * (N : ℝ) ^ (-(s.re - r))) / r := by
  have hsRe : 0 < s.re := hr.trans hrRe
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq :
      hardyLittlewoodEtaSeriesValue =ᶠ[𝓝 s] hardyLittlewoodEta := by
    filter_upwards [isOpen_ne.mem_nhds hs_ne,
      hopen.mem_nhds hsRe] with z hzNe hzRe
    exact hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta z hzNe hzRe
  rw [← heq.deriv_eq]
  exact norm_deriv_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
    s hr hrRe hN hNim

/-- The ordered eta remainder gives an actual finite-sum zeta evaluator wherever the eta factor
does not vanish. -/
theorem norm_riemannZeta_sub_hardyLittlewoodZetaApprox_le
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |s.im| ≤ N)
    (hfactor : hardyLittlewoodEtaFactor s ≠ 0) :
    ‖riemannZeta s - hardyLittlewoodZetaApprox s N‖ ≤
      (4 * (N : ℝ) ^ (-s.re)) / ‖hardyLittlewoodEtaFactor s‖ := by
  have hrem := norm_hardyLittlewoodEta_sub_partialSum_le
    s hs_ne hs_re hN hNim
  have hid :
      riemannZeta s - hardyLittlewoodZetaApprox s N =
        (hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N) /
          hardyLittlewoodEtaFactor s := by
    unfold hardyLittlewoodZetaApprox
    change
      riemannZeta s -
          hardyLittlewoodEtaPartialSum s N / hardyLittlewoodEtaFactor s =
        (hardyLittlewoodEtaFactor s * riemannZeta s -
            hardyLittlewoodEtaPartialSum s N) /
          hardyLittlewoodEtaFactor s
    field_simp [hfactor]
  rw [hid, norm_div]
  exact (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hfactor)).2 hrem

/-- The actual zeta derivative is approximated by differentiating the finite eta quotient. -/
theorem norm_deriv_riemannZeta_sub_hardyLittlewoodZetaDerivApprox_le
    (s : ℂ) (hs_ne : s ≠ 1) {r : ℝ} (hr : 0 < r) (hrRe : r < s.re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |s.im| + r ≤ N)
    (hfactor : hardyLittlewoodEtaFactor s ≠ 0) :
    ‖deriv riemannZeta s - hardyLittlewoodZetaDerivApprox s N‖ ≤
      (((4 * (N : ℝ) ^ (-(s.re - r))) / r) *
          ‖hardyLittlewoodEtaFactor s‖ +
        (4 * (N : ℝ) ^ (-s.re)) *
          ‖deriv hardyLittlewoodEtaFactor s‖) /
        ‖hardyLittlewoodEtaFactor s‖ ^ 2 := by
  have hsRe : 0 < s.re := hr.trans hrRe
  have hNimValue : |s.im| ≤ (N : ℝ) := by
    have hrNonneg : 0 ≤ r := hr.le
    exact (le_add_of_nonneg_right hrNonneg).trans (by exact_mod_cast hNim)
  have hvalueRem := norm_hardyLittlewoodEta_sub_partialSum_le
    s hs_ne hsRe hN hNimValue
  have hderivRem := norm_deriv_hardyLittlewoodEta_sub_partialSum_le
    s hs_ne hr hrRe hN hNim
  have hfactorDiff : DifferentiableAt ℂ hardyLittlewoodEtaFactor s := by
    unfold hardyLittlewoodEtaFactor
    fun_prop
  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs_ne
  have hetaDeriv :
      deriv hardyLittlewoodEta s =
        deriv hardyLittlewoodEtaFactor s * riemannZeta s +
          hardyLittlewoodEtaFactor s * deriv riemannZeta s := by
    unfold hardyLittlewoodEta hardyLittlewoodEtaFactor
    exact deriv_fun_mul hfactorDiff hzetaDiff
  have hzetaDeriv :
      deriv riemannZeta s =
        (deriv hardyLittlewoodEta s * hardyLittlewoodEtaFactor s -
          hardyLittlewoodEta s * deriv hardyLittlewoodEtaFactor s) /
          hardyLittlewoodEtaFactor s ^ 2 := by
    rw [hetaDeriv]
    change
      deriv riemannZeta s =
        ((deriv hardyLittlewoodEtaFactor s * riemannZeta s +
              hardyLittlewoodEtaFactor s * deriv riemannZeta s) *
            hardyLittlewoodEtaFactor s -
          (hardyLittlewoodEtaFactor s * riemannZeta s) *
            deriv hardyLittlewoodEtaFactor s) /
          hardyLittlewoodEtaFactor s ^ 2
    field_simp [hfactor]
    ring
  have hdiff :
      deriv riemannZeta s - hardyLittlewoodZetaDerivApprox s N =
        (((deriv hardyLittlewoodEta s -
              deriv (fun z => hardyLittlewoodEtaPartialSum z N) s) *
            hardyLittlewoodEtaFactor s) -
          ((hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N) *
            deriv hardyLittlewoodEtaFactor s)) /
          hardyLittlewoodEtaFactor s ^ 2 := by
    rw [hzetaDeriv]
    unfold hardyLittlewoodZetaDerivApprox
    ring
  rw [hdiff, norm_div, norm_pow]
  have hnum :
      ‖(deriv hardyLittlewoodEta s -
            deriv (fun z => hardyLittlewoodEtaPartialSum z N) s) *
          hardyLittlewoodEtaFactor s -
        (hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N) *
          deriv hardyLittlewoodEtaFactor s‖ ≤
        ‖deriv hardyLittlewoodEta s -
            deriv (fun z => hardyLittlewoodEtaPartialSum z N) s‖ *
            ‖hardyLittlewoodEtaFactor s‖ +
          ‖hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N‖ *
            ‖deriv hardyLittlewoodEtaFactor s‖ := by
    calc
      _ ≤ ‖(deriv hardyLittlewoodEta s -
              deriv (fun z => hardyLittlewoodEtaPartialSum z N) s) *
            hardyLittlewoodEtaFactor s‖ +
          ‖(hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N) *
            deriv hardyLittlewoodEtaFactor s‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hfactor))).2
  exact add_le_add
    (mul_le_mul_of_nonneg_right hderivRem (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hvalueRem (norm_nonneg _)) |>.trans' hnum

/-- A pair of certified complex error balls gives nonvanishing and a strict left-half-plane
quotient once the finite center has enough margin. -/
theorem strictNegativeRatio_of_approx
    {z d Z D : ℂ} {ez ed : ℝ}
    (hz : ‖z - Z‖ ≤ ez) (hd : ‖d - D‖ ≤ ed)
    (hzMargin : ez < ‖Z‖) (hdMargin : ed < ‖D‖)
    (hleft :
      (D * conj Z).re + ed * (‖Z‖ + ez) + ‖D‖ * ez < 0) :
    z ≠ 0 ∧ d ≠ 0 ∧ (d / z).re < 0 := by
  have hzNe : z ≠ 0 := by
    intro hzZero
    rw [hzZero, zero_sub, norm_neg] at hz
    linarith
  have hdNe : d ≠ 0 := by
    intro hdZero
    rw [hdZero, zero_sub, norm_neg] at hd
    linarith
  have hez : 0 ≤ ez := (norm_nonneg (z - Z)).trans hz
  have hed : 0 ≤ ed := (norm_nonneg (d - D)).trans hd
  have hzNorm : ‖z‖ ≤ ‖Z‖ + ez := by
    calc
      ‖z‖ = ‖(z - Z) + Z‖ := by ring_nf
      _ ≤ ‖z - Z‖ + ‖Z‖ := norm_add_le _ _
      _ ≤ ez + ‖Z‖ := by linarith
      _ = ‖Z‖ + ez := by ring
  have hproductIdentity :
      d * conj z - D * conj Z =
        (d - D) * conj z + D * conj (z - Z) := by
    simp only [map_sub]
    ring
  have hproductNorm :
      ‖d * conj z - D * conj Z‖ ≤
        ed * (‖Z‖ + ez) + ‖D‖ * ez := by
    rw [hproductIdentity]
    calc
      ‖(d - D) * conj z + D * conj (z - Z)‖ ≤
          ‖(d - D) * conj z‖ +
            ‖D * conj (z - Z)‖ :=
        norm_add_le _ _
      _ = ‖d - D‖ * ‖z‖ + ‖D‖ * ‖z - Z‖ := by
        rw [norm_mul, norm_mul, norm_conj, norm_conj]
      _ ≤ ed * (‖Z‖ + ez) + ‖D‖ * ez := by
        exact add_le_add
          (mul_le_mul hd hzNorm (norm_nonneg _) hed)
          (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
  have hreDiff :
      |(d * conj z).re - (D * conj Z).re| ≤
        ed * (‖Z‖ + ez) + ‖D‖ * ez := by
    have hreNorm := Complex.abs_re_le_norm (d * conj z - D * conj Z)
    have hreEq :
        (d * conj z - D * conj Z).re =
          (d * conj z).re - (D * conj Z).re := rfl
    rw [hreEq] at hreNorm
    exact hreNorm.trans hproductNorm
  have hproductRe : (d * conj z).re < 0 := by
    have hupper := (abs_le.mp hreDiff).2
    linarith
  refine ⟨hzNe, hdNe, ?_⟩
  rw [Complex.div_re, ← add_div]
  have hnum :
      d.re * z.re + d.im * z.im = (d * conj z).re := by
    simp only [mul_re, conj_re, conj_im]
    ring
  rw [hnum]
  exact div_neg_of_neg_of_pos hproductRe (Complex.normSq_pos.mpr hzNe)

/-- A cross-multiplied finite-center inequality gives a certified lower bound for the real part
of a quotient. The negative threshold lets a lower bound for the denominator suffice. -/
theorem ratio_re_gt_of_approx
    {z d Z D : ℂ} {ez ed U : ℝ}
    (hz : ‖z - Z‖ ≤ ez) (hd : ‖d - D‖ ≤ ed)
    (hzMargin : ez < ‖Z‖) (hU : U < 0)
    (hcross :
      U * (‖Z‖ - ez) ^ 2 <
        (D * conj Z).re -
          (ed * (‖Z‖ + ez) + ‖D‖ * ez)) :
    z ≠ 0 ∧ U < (d / z).re := by
  have hzNe : z ≠ 0 := by
    intro hzZero
    rw [hzZero, zero_sub, norm_neg] at hz
    linarith
  have hez : 0 ≤ ez := (norm_nonneg (z - Z)).trans hz
  have hed : 0 ≤ ed := (norm_nonneg (d - D)).trans hd
  have hzNormUpper : ‖z‖ ≤ ‖Z‖ + ez := by
    calc
      ‖z‖ = ‖(z - Z) + Z‖ := by ring_nf
      _ ≤ ‖z - Z‖ + ‖Z‖ := norm_add_le _ _
      _ ≤ ez + ‖Z‖ := by linarith
      _ = ‖Z‖ + ez := by ring
  have hzNormLower : ‖Z‖ - ez ≤ ‖z‖ := by
    have htriangle : ‖Z‖ ≤ ‖Z - z‖ + ‖z‖ := by
      calc
        ‖Z‖ = ‖(Z - z) + z‖ := by ring_nf
        _ ≤ ‖Z - z‖ + ‖z‖ := norm_add_le _ _
    have hsymm : ‖Z - z‖ = ‖z - Z‖ := by
      rw [← norm_neg (Z - z)]
      congr 1
      ring
    rw [hsymm] at htriangle
    linarith
  have hdenLower : (‖Z‖ - ez) ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hproductIdentity :
      d * conj z - D * conj Z =
        (d - D) * conj z + D * conj (z - Z) := by
    simp only [map_sub]
    ring
  have hproductNorm :
      ‖d * conj z - D * conj Z‖ ≤
        ed * (‖Z‖ + ez) + ‖D‖ * ez := by
    rw [hproductIdentity]
    calc
      ‖(d - D) * conj z + D * conj (z - Z)‖ ≤
          ‖(d - D) * conj z‖ + ‖D * conj (z - Z)‖ :=
        norm_add_le _ _
      _ = ‖d - D‖ * ‖z‖ + ‖D‖ * ‖z - Z‖ := by
        rw [norm_mul, norm_mul, norm_conj, norm_conj]
      _ ≤ ed * (‖Z‖ + ez) + ‖D‖ * ez := by
        exact add_le_add
          (mul_le_mul hd hzNormUpper (norm_nonneg _) hed)
          (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
  have hreDiff :
      |(d * conj z).re - (D * conj Z).re| ≤
        ed * (‖Z‖ + ez) + ‖D‖ * ez := by
    have hreNorm := Complex.abs_re_le_norm (d * conj z - D * conj Z)
    have hreEq :
        (d * conj z - D * conj Z).re =
          (d * conj z).re - (D * conj Z).re := rfl
    rw [hreEq] at hreNorm
    exact hreNorm.trans hproductNorm
  have hnumLower :
      (D * conj Z).re -
          (ed * (‖Z‖ + ez) + ‖D‖ * ez) ≤
        (d * conj z).re := by
    have hlower := (abs_le.mp hreDiff).1
    linarith
  have hthresholdDenom :
      U * Complex.normSq z ≤ U * (‖Z‖ - ez) ^ 2 :=
    mul_le_mul_of_nonpos_left hdenLower hU.le
  refine ⟨hzNe, ?_⟩
  rw [Complex.div_re, ← add_div]
  have hnum :
      d.re * z.re + d.im * z.im = (d * conj z).re := by
    simp only [mul_re, conj_re, conj_im]
    ring
  rw [hnum]
  apply (lt_div_iff₀ (Complex.normSq_pos.mpr hzNe)).2
  exact hthresholdDenom.trans_lt (hcross.trans_le hnumLower)

/-- Finite eta centers at the reflected right-half point, together with the compiled digamma
remainder, certify the full pointwise Speiser sign condition on the left half of the strip. -/
theorem speiserStrictNegativePoint_of_reflected_hardyLittlewood_margins
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {r : ℝ} (hr : 0 < r) (hrRe : r < (1 - s).re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |(1 - s).im| + r ≤ N)
    (hzMargin :
      hardyLittlewoodZetaError (1 - s) N <
        ‖hardyLittlewoodZetaApprox (1 - s) N‖)
    (hupper : levinsonMontgomeryReflectedArchimedeanUpper s < 0)
    (hcross :
      levinsonMontgomeryReflectedArchimedeanUpper s *
          (‖hardyLittlewoodZetaApprox (1 - s) N‖ -
            hardyLittlewoodZetaError (1 - s) N) ^ 2 <
        (hardyLittlewoodZetaDerivApprox (1 - s) N *
            conj (hardyLittlewoodZetaApprox (1 - s) N)).re -
          (hardyLittlewoodZetaDerivError (1 - s) r N *
              (‖hardyLittlewoodZetaApprox (1 - s) N‖ +
                hardyLittlewoodZetaError (1 - s) N) +
            ‖hardyLittlewoodZetaDerivApprox (1 - s) N‖ *
              hardyLittlewoodZetaError (1 - s) N)) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 ∧
      (speiserZetaDerivRatio s).re < 0 := by
  have hwOne : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hfactor : hardyLittlewoodEtaFactor (1 - s) ≠ 0 :=
    hardyLittlewoodEtaFactor_ne_zero_of_re_lt_one (by norm_num; linarith)
  have hzBound := norm_riemannZeta_sub_hardyLittlewoodZetaApprox_le
    (1 - s) hwOne (hr.trans hrRe) hN
      ((le_add_of_nonneg_right hr.le).trans (by exact_mod_cast hNim)) hfactor
  change
    ‖riemannZeta (1 - s) - hardyLittlewoodZetaApprox (1 - s) N‖ ≤
      hardyLittlewoodZetaError (1 - s) N at hzBound
  have hdBound :=
    norm_deriv_riemannZeta_sub_hardyLittlewoodZetaDerivApprox_le
      (1 - s) hwOne hr hrRe hN hNim hfactor
  change
    ‖deriv riemannZeta (1 - s) -
        hardyLittlewoodZetaDerivApprox (1 - s) N‖ ≤
      hardyLittlewoodZetaDerivError (1 - s) r N at hdBound
  have hratio := ratio_re_gt_of_approx hzBound hdBound hzMargin hupper hcross
  have hreflected : riemannZeta (1 - s) ≠ 0 := hratio.1
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_sub_ne_zero hs0 hs1 hreflected
  have hsArchAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_approx_le
      (s := s) (by linarith)
  have hwArchAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_approx_le
      (s := 1 - s) (by norm_num; linarith)
  have harchUpper :
      levinsonMontgomeryLogDerivArchimedeanTerm s +
          levinsonMontgomeryLogDerivArchimedeanTerm (1 - s) ≤
        levinsonMontgomeryReflectedArchimedeanUpper s := by
    have hsUpper := (abs_le.mp hsArchAbs).2
    have hwUpper := (abs_le.mp hwArchAbs).2
    unfold levinsonMontgomeryReflectedArchimedeanUpper
    linarith
  have hreflection :=
    logDeriv_riemannZeta_re_reflection hs0 hs1 hzeta hreflected
  have hratioLog :
      levinsonMontgomeryReflectedArchimedeanUpper s <
        (logDeriv riemannZeta (1 - s)).re := by
    simpa only [logDeriv_apply] using hratio.2
  have hlogNegative : (logDeriv riemannZeta s).re < 0 := by
    rw [hreflection]
    linarith [hratioLog, harchUpper]
  have hderiv : deriv riemannZeta s ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hlogNegative
    exact (lt_irrefl 0) hlogNegative
  refine ⟨hzeta, hderiv, ?_⟩
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using hlogNegative

/-- Computable finite-sum margins certify the pointwise sign condition used on the
Levinson--Montgomery height-ten horizontal. -/
theorem speiserStrictNegativePoint_of_hardyLittlewood_margins
    (s : ℂ) (hs_ne : s ≠ 1) {r : ℝ} (hr : 0 < r) (hrRe : r < s.re)
    {N : ℕ} (hN : 1 ≤ N) (hNim : |s.im| + r ≤ N)
    (hfactor : hardyLittlewoodEtaFactor s ≠ 0)
    (hzMargin :
      hardyLittlewoodZetaError s N < ‖hardyLittlewoodZetaApprox s N‖)
    (hdMargin :
      hardyLittlewoodZetaDerivError s r N <
        ‖hardyLittlewoodZetaDerivApprox s N‖)
    (hleft :
      (hardyLittlewoodZetaDerivApprox s N *
          conj (hardyLittlewoodZetaApprox s N)).re +
        hardyLittlewoodZetaDerivError s r N *
          (‖hardyLittlewoodZetaApprox s N‖ +
            hardyLittlewoodZetaError s N) +
        ‖hardyLittlewoodZetaDerivApprox s N‖ *
          hardyLittlewoodZetaError s N < 0) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 ∧
      (speiserZetaDerivRatio s).re < 0 := by
  have hz := norm_riemannZeta_sub_hardyLittlewoodZetaApprox_le
    s hs_ne (hr.trans hrRe) hN
      ((le_add_of_nonneg_right hr.le).trans (by exact_mod_cast hNim)) hfactor
  have hd := norm_deriv_riemannZeta_sub_hardyLittlewoodZetaDerivApprox_le
    s hs_ne hr hrRe hN hNim hfactor
  have hcert := strictNegativeRatio_of_approx hz hd hzMargin hdMargin hleft
  simpa only [speiserZetaDerivRatio] using hcert

end

end LeanLab.Riemann
