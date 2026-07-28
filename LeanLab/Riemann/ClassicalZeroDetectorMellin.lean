import LeanLab.Riemann.BettinGonekMellinIdentity
import LeanLab.Riemann.ComplexLaplaceGamma
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

set_option linter.style.header false

/-!
# The classical zero-density detector: arithmetic and finite logic

This module formalizes the truncated-Mobius coefficient gap and the finite pigeonhole logic in
the Ingham--Huxley zero detector as reconstructed in Maynard--Pratt, Appendix C. The
Gamma--Mellin inversion and contour shift at an actual zeta zero are deliberately left to a
separate analytic continuation stage.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Real Set Topology
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

/-- The Mobius arithmetic function cut off at the positive integer `M`. -/
def classicalDetectorTruncatedMobius (M : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n =>
    if n ≤ M then ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0,
    by simp⟩

/-- The coefficients of the product of the truncated Mobius polynomial with zeta. -/
def classicalDetectorCoefficient (M : ℕ) : ArithmeticFunction ℂ :=
  classicalDetectorTruncatedMobius M *
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)

theorem classicalDetectorCoefficient_eq_divisorSum (M n : ℕ) :
    classicalDetectorCoefficient M n =
      ∑ d ∈ n.divisors,
        if d ≤ M then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
  rw [classicalDetectorCoefficient, ArithmeticFunction.coe_mul_zeta_apply]
  rfl

theorem classicalDetectorCoefficient_one {M : ℕ} (hM : 1 ≤ M) :
    classicalDetectorCoefficient M 1 = 1 := by
  rw [classicalDetectorCoefficient_eq_divisorSum]
  simp [hM]

theorem classicalDetectorCoefficient_eq_zero
    {M n : ℕ} (hn : 2 ≤ n) (hnM : n ≤ M) :
    classicalDetectorCoefficient M n = 0 := by
  rw [classicalDetectorCoefficient_eq_divisorSum]
  have hn0 : n ≠ 0 := by omega
  calc
    (∑ d ∈ n.divisors,
        if d ≤ M then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) =
        ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn0) hdn
      simp [hdle.trans hnM]
    _ = ((((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℂ) *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℂ)) n) := by
      exact (ArithmeticFunction.coe_mul_zeta_apply
        (f := ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
          ArithmeticFunction ℂ)) (x := n)).symm
    _ = 0 := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      simp [show n ≠ 1 by omega]

/-- The finite Dirichlet polynomial used in the classical detector. -/
def classicalDetectorMollifier (M : ℕ) (s : ℂ) : ℂ :=
  LSeries (classicalDetectorTruncatedMobius M) s

theorem classicalDetectorMollifier_eq_mobiusDirichletPartialSum (M : ℕ) (s : ℂ) :
    classicalDetectorMollifier M s = mobiusDirichletPartialSum M s := by
  rw [classicalDetectorMollifier, LSeries, mobiusDirichletPartialSum]
  rw [tsum_eq_sum (s := Finset.Icc 1 M)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1
    rw [LSeries.term_of_ne_zero hn0]
    simp only [classicalDetectorTruncatedMobius, ArithmeticFunction.coe_mk]
    rw [if_pos (Finset.mem_Icc.mp hn).2, div_eq_mul_inv, ← Complex.cpow_neg]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnM : ¬n ≤ M := by
        intro hnM
        exact hn (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)
      rw [LSeries.term_of_ne_zero hn0]
      simp [classicalDetectorTruncatedMobius, hnM]

theorem LSeriesSummable_classicalDetectorTruncatedMobius (M : ℕ) (s : ℂ) :
    LSeriesSummable (classicalDetectorTruncatedMobius M) s := by
  rw [LSeriesSummable]
  apply summable_of_ne_finset_zero (s := Finset.range (M + 1))
  intro n hn
  have hMn : M < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0]
  simp [classicalDetectorTruncatedMobius, Nat.not_le.mpr hMn]

theorem LSeriesSummable_classicalDetectorCoefficient
    {s : ℂ} (hs : 1 < s.re) (M : ℕ) :
    LSeriesSummable (classicalDetectorCoefficient M) s := by
  exact ArithmeticFunction.LSeriesSummable_mul
    (LSeriesSummable_classicalDetectorTruncatedMobius M s)
    (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)

theorem LSeries_classicalDetectorCoefficient_eq
    {s : ℂ} (hs : 1 < s.re) (M : ℕ) :
    LSeries (classicalDetectorCoefficient M) s =
      classicalDetectorMollifier M s * riemannZeta s := by
  let zetaC : ArithmeticFunction ℂ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
  have htrunc : LSeriesSummable (classicalDetectorTruncatedMobius M) s :=
    LSeriesSummable_classicalDetectorTruncatedMobius M s
  have hzeta : LSeriesSummable zetaC s := by
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hzetaEq : LSeries (fun n => zetaC n) s = riemannZeta s := by
    calc
      _ = LSeries
          (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) s := by
        apply LSeries_congr
        intro n hn
        simp [zetaC, ArithmeticFunction.zeta_apply, hn]
      _ = _ := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  rw [classicalDetectorCoefficient, classicalDetectorMollifier]
  change LSeries (fun n => (classicalDetectorTruncatedMobius M * zetaC) n) s =
    LSeries (classicalDetectorTruncatedMobius M) s * riemannZeta s
  rw [ArithmeticFunction.LSeries_mul' htrunc hzeta]
  rw [hzetaEq]

/-- One exponentially smoothed term of the classical zero detector. -/
def classicalDetectorSmoothedTerm (M : ℕ) (Y : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (classicalDetectorCoefficient M) z n *
    Complex.exp (-((n : ℝ) / Y))

/-- The exponentially smoothed Dirichlet series on its initial half-plane. -/
def classicalDetectorSmoothedSeries (M : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, classicalDetectorSmoothedTerm M Y z n

theorem summable_classicalDetectorSmoothedTerm
    {z : ℂ} (hz : 1 < z.re) (M : ℕ) {Y : ℝ} (hY : 0 < Y) :
    Summable (classicalDetectorSmoothedTerm M Y z) := by
  have hbase := LSeriesSummable_classicalDetectorCoefficient hz M
  refine (summable_norm_iff.mpr hbase).of_norm_bounded ?_
  intro n
  rw [classicalDetectorSmoothedTerm, norm_mul, Complex.norm_exp]
  have hnonpos : -((n : ℝ) / Y) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg n) hY.le)
  have hexp : Real.exp (-((n : ℝ) / Y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hnonpos
  simpa using mul_le_of_le_one_right (norm_nonneg _) hexp

theorem classicalDetectorSmoothedTerm_one
    {M : ℕ} (hM : 1 ≤ M) (Y : ℝ) (z : ℂ) :
    classicalDetectorSmoothedTerm M Y z 1 = Complex.exp (-(1 / Y : ℝ)) := by
  rw [classicalDetectorSmoothedTerm, LSeries.term_of_ne_zero (by norm_num),
    classicalDetectorCoefficient_one hM]
  norm_num

theorem classicalDetectorSmoothedTerm_eq_zero
    {M n : ℕ} (hn : 2 ≤ n) (hnM : n ≤ M) (Y : ℝ) (z : ℂ) :
    classicalDetectorSmoothedTerm M Y z n = 0 := by
  rw [classicalDetectorSmoothedTerm, LSeries.term_of_ne_zero (by omega),
    classicalDetectorCoefficient_eq_zero hn hnM]
  simp

theorem classicalDetectorSmoothedSeries_eq_head_add_tail
    {M : ℕ} (hM : 1 ≤ M) {z : ℂ} (hz : 1 < z.re)
    {Y : ℝ} (hY : 0 < Y) :
    classicalDetectorSmoothedSeries M Y z =
      Complex.exp (-(1 / Y : ℝ)) +
        ∑' n : ℕ, classicalDetectorSmoothedTerm M Y z (n + (M + 1)) := by
  let f := classicalDetectorSmoothedTerm M Y z
  have hf : Summable f := summable_classicalDetectorSmoothedTerm hz M hY
  have hhead :
      (∑ n ∈ Finset.range (M + 1), f n) =
        Complex.exp (-(1 / Y : ℝ)) := by
    rw [Finset.sum_eq_single 1]
    · exact classicalDetectorSmoothedTerm_one hM Y z
    · intro n hn hn1
      have hnlt : n < M + 1 := Finset.mem_range.mp hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [f, classicalDetectorSmoothedTerm, LSeries.term]
      · exact classicalDetectorSmoothedTerm_eq_zero
          (by omega) (by omega) Y z
    · intro hnot
      have hmem : 1 ∈ Finset.range (M + 1) :=
        Finset.mem_range.mpr (by omega)
      exact (hnot hmem).elim
  have hsplit := hf.sum_add_tsum_nat_add (M + 1)
  rw [classicalDetectorSmoothedSeries]
  calc
    (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range (M + 1), f n) +
          ∑' n : ℕ, f (n + (M + 1)) := hsplit.symm
    _ = _ := by rw [hhead]

/-- The `n`th Dirichlet coefficient coupled to the Laplace--Mellin kernel. -/
def classicalDetectorLaplaceMellinTerm
    (M : ℕ) (z w : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (classicalDetectorCoefficient M) z n *
    deBruijnNewmanComplexLaplaceIntegrand w (n : ℂ) u

theorem integrableOn_classicalDetectorLaplaceMellinTerm
    (M : ℕ) (z : ℂ) {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (classicalDetectorLaplaceMellinTerm M z w n) (Ioi 0) := by
  have hnre : 0 < ((n : ℂ).re) := by
    simpa using (show 0 < (n : ℝ) by exact_mod_cast hn)
  exact (integrableOn_deBruijnNewmanComplexLaplaceIntegrand hw hnre).const_mul
    (LSeries.term (classicalDetectorCoefficient M) z n)

theorem classicalDetector_LSeriesTerm_mul_nat_cpow_neg
    (M : ℕ) (z w : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (classicalDetectorCoefficient M) z n * (n : ℂ) ^ (-w) =
      LSeries.term (classicalDetectorCoefficient M) (z + w) n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [mul_assoc, ← Complex.cpow_add _ _ hnC]
  congr 1
  ring_nf

theorem integral_classicalDetectorLaplaceMellinTerm
    (M : ℕ) (z : ℂ) {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 0 < n) :
    (∫ u : ℝ in Ioi 0, classicalDetectorLaplaceMellinTerm M z w n u) =
      LSeries.term (classicalDetectorCoefficient M) (z + w) n *
        Complex.Gamma w := by
  have hnre : 0 < ((n : ℂ).re) := by
    simpa using (show 0 < (n : ℝ) by exact_mod_cast hn)
  change
    (∫ u : ℝ in Ioi 0,
      LSeries.term (classicalDetectorCoefficient M) z n *
        deBruijnNewmanComplexLaplaceIntegrand w (n : ℂ) u) = _
  rw [MeasureTheory.integral_const_mul,
    deBruijnNewmanComplexLaplace_eq hw hnre, ← mul_assoc,
    classicalDetector_LSeriesTerm_mul_nat_cpow_neg M z w hn.ne']

/-- The exponential generating series whose Mellin transform is the detector Dirichlet series. -/
def classicalDetectorExponentialSeries (M : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ,
    LSeries.term (classicalDetectorCoefficient M) z n *
      (Real.exp (-((n : ℝ) * u)) : ℂ)

theorem classicalDetectorExponentialSeries_one_div_eq_smoothed
    (M : ℕ) (z : ℂ) (Y : ℝ) :
    classicalDetectorExponentialSeries M z (1 / Y) =
      classicalDetectorSmoothedSeries M Y z := by
  rw [classicalDetectorExponentialSeries, classicalDetectorSmoothedSeries]
  apply tsum_congr
  intro n
  rw [classicalDetectorSmoothedTerm]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem summable_classicalDetectorExponentialTerm
    {z : ℂ} (hz : 1 < z.re) (M : ℕ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ =>
      LSeries.term (classicalDetectorCoefficient M) z n *
        (Real.exp (-((n : ℝ) * u)) : ℂ) := by
  have hbase := LSeriesSummable_classicalDetectorCoefficient hz M
  refine (summable_norm_iff.mpr hbase).of_norm_bounded ?_
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hnonpos : -((n : ℝ) * u) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hu.le)
  have hexp : Real.exp (-((n : ℝ) * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hnonpos
  simpa using mul_le_of_le_one_right (norm_nonneg _) hexp

theorem classicalDetectorTerm_zero_or_frequency_pos
    (M : ℕ) (z : ℂ) (n : ℕ) :
    LSeries.term (classicalDetectorCoefficient M) z n = 0 ∨
      0 < (n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl (by simp [LSeries.term])
  · exact Or.inr (by exact_mod_cast Nat.pos_of_ne_zero hn)

theorem summable_norm_classicalDetectorTerm_div_frequency_rpow
    (M : ℕ) {z w : ℂ} (hzw : 1 < (z + w).re) :
    Summable fun n : ℕ =>
      ‖LSeries.term (classicalDetectorCoefficient M) z n‖ /
        (n : ℝ) ^ w.re := by
  have hbase :=
    (LSeriesSummable_classicalDetectorCoefficient hzw M).norm
  refine hbase.congr (fun n => ?_)
  simp only [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [if_neg hn, Complex.add_re]
    rw [Real.rpow_add hnpos]
    ring

theorem classicalDetectorTerm_div_frequency_cpow
    (M : ℕ) (z w : ℂ) (n : ℕ) :
    LSeries.term (classicalDetectorCoefficient M) z n /
        ((n : ℝ) : ℂ) ^ w =
      LSeries.term (classicalDetectorCoefficient M) (z + w) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [div_eq_mul_inv, ← Complex.cpow_neg]
    exact classicalDetector_LSeriesTerm_mul_nat_cpow_neg M z w hn

/-- Absolute convergence on the initial half-plane justifies the full sum--integral exchange. -/
theorem hasSum_classicalDetectorMellinSeries
    (M : ℕ) {z w : ℂ} (hz : 1 < z.re) (hw : 0 < w.re) :
    HasSum
      (fun n : ℕ =>
        Complex.Gamma w *
          LSeries.term (classicalDetectorCoefficient M) (z + w) n)
      (mellin (classicalDetectorExponentialSeries M z) w) := by
  have hsource := hasSum_mellin
    (a := fun n : ℕ => LSeries.term (classicalDetectorCoefficient M) z n)
    (p := fun n : ℕ => (n : ℝ))
    (F := classicalDetectorExponentialSeries M z)
    (s := w)
    (classicalDetectorTerm_zero_or_frequency_pos M z)
    hw
    (fun u hu => by
      simpa only [classicalDetectorExponentialSeries, neg_mul] using
        (summable_classicalDetectorExponentialTerm hz M hu).hasSum)
    (summable_norm_classicalDetectorTerm_div_frequency_rpow M
      (by simp only [Complex.add_re]; linarith))
  simpa only [mul_div_assoc,
    classicalDetectorTerm_div_frequency_cpow M z w] using hsource

/-- The forward Mellin identity for the complete exponentially smoothed detector series. -/
theorem mellin_classicalDetectorExponentialSeries_eq
    (M : ℕ) {z w : ℂ} (hz : 1 < z.re) (hw : 0 < w.re) :
    mellin (classicalDetectorExponentialSeries M z) w =
      Complex.Gamma w * LSeries (classicalDetectorCoefficient M) (z + w) := by
  have hzw : 1 < (z + w).re := by
    simp only [Complex.add_re]
    linarith
  have hsource := hasSum_classicalDetectorMellinSeries M hz hw
  have htarget :=
    (LSeriesSummable_classicalDetectorCoefficient hzw M).LSeriesHasSum.mul_left
      (Complex.Gamma w)
  exact hsource.unique htarget

/-- The same forward identity with the actual finite Mobius mollifier and Riemann zeta exposed. -/
theorem mellin_classicalDetectorExponentialSeries_eq_gamma_mul_mollifier_mul_zeta
    (M : ℕ) {z w : ℂ} (hz : 1 < z.re) (hw : 0 < w.re) :
    mellin (classicalDetectorExponentialSeries M z) w =
      Complex.Gamma w *
        (classicalDetectorMollifier M (z + w) * riemannZeta (z + w)) := by
  have hzw : 1 < (z + w).re := by
    simp only [Complex.add_re]
    linarith
  rw [mellin_classicalDetectorExponentialSeries_eq M hz hw,
    LSeries_classicalDetectorCoefficient_eq hzw M]

/-- The holomorphic replacement for `Gamma(w) * zeta(rho + w)` at the canceled pole `w = 0`. -/
def classicalDetectorCancelledGammaZeta (rho w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope riemannZeta rho (rho + w)

theorem classicalDetectorCancelledGammaZeta_eq_source
    {rho : ℂ} (hrho : IsNontrivialZero rho) {w : ℂ} (hw : w ≠ 0) :
    classicalDetectorCancelledGammaZeta rho w =
      Complex.Gamma w * riemannZeta (rho + w) := by
  have harg : rho + w ≠ rho := by
    intro h
    apply hw
    linear_combination h
  rw [classicalDetectorCancelledGammaZeta, dslope_of_ne _ harg,
    slope_fun_def_field, hrho.1]
  change
    Complex.Gamma (w + 1) *
        ((riemannZeta (rho + w) - 0) / (rho + w - rho)) =
      Complex.Gamma w * riemannZeta (rho + w)
  rw [sub_zero]
  have hden : rho + w - rho = w := by ring
  rw [hden, Complex.Gamma_add_one w hw]
  field_simp [hw]

theorem classicalDetectorCancelledGammaZeta_zero
    (rho : ℂ) :
    classicalDetectorCancelledGammaZeta rho 0 = deriv riemannZeta rho := by
  simp [classicalDetectorCancelledGammaZeta]

/-- The half-plane needed for the classical shift, with the translated zeta pole removed. -/
def classicalDetectorCancelledGammaZetaDomain (rho : ℂ) : Set ℂ :=
  {w | -1 < w.re ∧ rho + w ≠ 1}

theorem differentiableOn_classicalDetectorCancelledGammaZeta
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    DifferentiableOn ℂ (classicalDetectorCancelledGammaZeta rho)
      (classicalDetectorCancelledGammaZetaDomain rho) := by
  intro w hw
  have hgammaArg : ∀ n : ℕ, w + 1 ≠ -(n : ℂ) := by
    intro n hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.add_re] at hre
    exact (by linarith [hw.1] : False).elim
  have hgamma :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma (w + 1) hgammaArg).comp w (by fun_prop)
  have hrhoOne : rho ≠ 1 := hrho.2.2
  have hdslopeOn :
      DifferentiableOn ℂ (dslope riemannZeta rho) ({1}ᶜ : Set ℂ) := by
    rw [Complex.differentiableOn_dslope
      (isOpen_compl_singleton.mem_nhds hrhoOne)]
    exact differentiableOn_riemannZeta
  have hargMem : rho + w ∈ ({1}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw.2
  have hdslope :
      DifferentiableAt ℂ
        (fun z : ℂ => dslope riemannZeta rho (rho + z)) w :=
    (hdslopeOn.differentiableAt
      (isOpen_compl_singleton.mem_nhds hargMem)).comp w (by fun_prop)
  change DifferentiableWithinAt ℂ
    (fun z : ℂ =>
      Complex.Gamma (z + 1) * dslope riemannZeta rho (rho + z))
    (classicalDetectorCancelledGammaZetaDomain rho) w
  exact (hgamma.mul hdslope).differentiableWithinAt

/-- Translation of the zeta residue from `s = 1` to the detector pole `w = 1 - rho`. -/
theorem tendsto_classicalDetector_translatedZetaResidue (rho : ℂ) :
    Tendsto
      (fun w : ℂ => (w - (1 - rho)) * riemannZeta (rho + w))
      (𝓝[≠] (1 - rho)) (𝓝 1) := by
  have hshift :
      Tendsto (fun w : ℂ => rho + w)
        (𝓝[≠] (1 - rho)) (𝓝[≠] 1) := by
    have hcenter : rho + (1 - rho) = 1 := by ring
    change Filter.map (fun w : ℂ => rho + w) (𝓝[≠] (1 - rho)) ≤ 𝓝[≠] 1
    simpa only [Homeomorph.coe_addLeft, hcenter] using
      ((Homeomorph.addLeft rho).map_punctured_nhds_eq (1 - rho)).le
  have hsource := riemannZeta_residue_one.comp hshift
  have heq :
      (fun w : ℂ => (w - (1 - rho)) * riemannZeta (rho + w)) =
        (fun s : ℂ => (s - 1) * riemannZeta s) ∘
          (fun w : ℂ => rho + w) := by
    funext w
    dsimp only [Function.comp_apply]
    congr 1
    ring
  rw [heq]
  exact hsource

theorem tendsto_classicalDetector_translatedZetaResidue_mul_continuous
    (rho : ℂ) {A : ℂ → ℂ} (hA : ContinuousAt A (1 - rho)) :
    Tendsto
      (fun w : ℂ =>
        (w - (1 - rho)) * (A w * riemannZeta (rho + w)))
      (𝓝[≠] (1 - rho)) (𝓝 (A (1 - rho))) := by
  have hfactor :
      Tendsto A (𝓝[≠] (1 - rho)) (𝓝 (A (1 - rho))) :=
    hA.tendsto.mono_left nhdsWithin_le_nhds
  have hsource :=
    hfactor.mul (tendsto_classicalDetector_translatedZetaResidue rho)
  convert hsource using 1
  · funext w
    ring
  · simp

theorem continuous_classicalDetectorMollifier (M : ℕ) :
    Continuous (classicalDetectorMollifier M) := by
  have heq :
      classicalDetectorMollifier M = mobiusDirichletPartialSum M :=
    funext (classicalDetectorMollifier_eq_mobiusDirichletPartialSum M)
  rw [heq]
  change Continuous (fun s : ℂ =>
    ∑ n ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s))
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul continuous_const
  have hn0N : n ≠ 0 := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hn0C : (n : ℂ) ≠ 0 := by exact_mod_cast hn0N
  exact (continuous_iff_continuousAt.mpr fun s =>
    (continuousAt_const_cpow hn0C).comp (by fun_prop))

/-- The source contour factor before division by `2 * pi * I`. -/
def classicalDetectorMellinContourFactor
    (M : ℕ) (rho : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  (Y : ℂ) ^ w * Complex.Gamma w *
    classicalDetectorMollifier M (rho + w) *
      riemannZeta (rho + w)

/-- The retained residue at the translated zeta pole `w = 1 - rho`. -/
theorem tendsto_classicalDetectorMellinContourFactor_zetaPole
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    {Y : ℝ} (hY : 0 < Y) :
    Tendsto
      (fun w : ℂ =>
        (w - (1 - rho)) *
          classicalDetectorMellinContourFactor M rho Y w)
      (𝓝[≠] (1 - rho))
      (𝓝 ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1)) := by
  let A : ℂ → ℂ := fun w =>
    (Y : ℂ) ^ w * Complex.Gamma w *
      classicalDetectorMollifier M (rho + w)
  have hpoleRe : 0 < (1 - rho).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [nontrivial_zero_re_lt_one hrho]
  have hgammaArg : ∀ n : ℕ, 1 - rho ≠ -(n : ℂ) := by
    intro n hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.sub_re] at hre
    linarith [nontrivial_zero_re_lt_one hrho]
  have hA : ContinuousAt A (1 - rho) := by
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact continuousAt_const_cpow
          (Complex.ofReal_ne_zero.mpr hY.ne')
      · exact (Complex.differentiableAt_Gamma (1 - rho) hgammaArg).continuousAt
    · exact (continuous_classicalDetectorMollifier M).continuousAt.comp (by fun_prop)
  have hsource :=
    tendsto_classicalDetector_translatedZetaResidue_mul_continuous rho hA
  have hcenter : rho + (1 - rho) = 1 := by ring
  simpa only [A, classicalDetectorMellinContourFactor, hcenter,
    mul_assoc] using hsource

/-- The exact finite mass inequality behind the Type-I/Type-II detector. -/
theorem one_le_error_add_remainder_add_blockMass
    {ι : Type*} [Fintype ι] (block : ι → ℂ) (error remainder : ℂ)
    (hidentity : (1 : ℂ) + error + ∑ i, block i = remainder) :
    (1 : ℝ) ≤ ‖error‖ + ‖remainder‖ + ∑ i, ‖block i‖ := by
  have hrewrite : (1 : ℂ) = remainder - error - ∑ i, block i := by
    rw [← hidentity]
    ring
  calc
    (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
    _ = ‖remainder - error - ∑ i, block i‖ := by rw [hrewrite]
    _ ≤ ‖remainder‖ + ‖error‖ + ‖∑ i, block i‖ := by
      calc
        _ ≤ ‖remainder - error‖ + ‖∑ i, block i‖ := norm_sub_le _ _
        _ ≤ (‖remainder‖ + ‖error‖) + ‖∑ i, block i‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ ‖error‖ + ‖remainder‖ + ∑ i, ‖block i‖ := by
      rw [add_comm ‖remainder‖ ‖error‖]
      gcongr
      exact norm_sum_le _ _

/-- A source-independent cardinality-audited block detector. -/
theorem exists_large_block_or_remainder
    {ι : Type*} [Fintype ι] (block : ι → ℂ) (error remainder : ℂ)
    (hidentity : (1 : ℂ) + error + ∑ i, block i = remainder)
    (herror : ‖error‖ ≤ 1 / 3) :
    1 / (3 * (Fintype.card ι + 1) : ℝ) ≤ ‖remainder‖ ∨
      ∃ i, 1 / (3 * (Fintype.card ι + 1) : ℝ) ≤ ‖block i‖ := by
  by_contra h
  push Not at h
  rcases h with ⟨hremainder, hblock⟩
  have hmass := one_le_error_add_remainder_add_blockMass block error remainder hidentity
  have hsum :
      (∑ i, ‖block i‖) ≤
        (Fintype.card ι : ℝ) * (1 / (3 * (Fintype.card ι + 1) : ℝ)) := by
    simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => ‖block i‖)
      (1 / (3 * (Fintype.card ι + 1) : ℝ))
      (fun i _ => (hblock i).le)
  have hcard : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hden : (0 : ℝ) < 3 * (Fintype.card ι + 1) := by positivity
  have hupper :
      ‖error‖ + ‖remainder‖ + ∑ i, ‖block i‖ < 1 := by
    calc
      _ < 1 / 3 +
          1 / (3 * (Fintype.card ι + 1) : ℝ) +
          (Fintype.card ι : ℝ) *
            (1 / (3 * (Fintype.card ι + 1) : ℝ)) :=
        add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt herror hremainder) hsum
      _ = 2 / 3 := by field_simp; ring
      _ < 1 := by norm_num
  linarith

/-- With `k` blocks, unit mass can be spread uniformly at scale `1/k`. -/
theorem uniform_blocks_sum_one (k : ℕ) (hk : 0 < k) :
    ∃ block : Fin k → ℂ,
      (∑ i, block i) = 1 ∧
      ∀ i, ‖block i‖ = 1 / k := by
  refine ⟨fun _ => ((1 / k : ℝ) : ℂ), ?_, ?_⟩
  · simp [hk.ne']
  · intro i
    simp

/-- The normalized vertical integral occurring in the inverse Mellin formula. -/
def classicalDetectorMellinLineIntegral
    (M : ℕ) (z : ℂ) (Y c : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) *
    ∫ t : ℝ,
      classicalDetectorMellinContourFactor M z Y
        (c + t * Complex.I)

/-- The first open analytic edge after the compiled forward Mellin transform. -/
def ClassicalDetectorInverseMellinLine : Prop :=
  ∀ (M : ℕ) (z : ℂ) (Y c : ℝ),
    0 < Y →
    0 < c →
    1 - z.re < c →
    classicalDetectorSmoothedSeries M Y z =
      classicalDetectorMellinLineIntegral M z Y c

/-- Aggregate certificate for the compiled arithmetic, forward Mellin, local residue, and finite
detector layers. It intentionally has no inverse-Mellin or global contour-shift field. -/
structure ClassicalDetectorMellinPartialCertificate : Prop where
  coefficientFormula :
    ∀ M n : ℕ,
      classicalDetectorCoefficient M n =
        ∑ d ∈ n.divisors,
          if d ≤ M then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0
  coefficientOne :
    ∀ {M : ℕ}, 1 ≤ M → classicalDetectorCoefficient M 1 = 1
  coefficientGap :
    ∀ {M n : ℕ}, 2 ≤ n → n ≤ M →
      classicalDetectorCoefficient M n = 0
  sourceProduct :
    ∀ {s : ℂ}, 1 < s.re → ∀ M : ℕ,
      LSeries (classicalDetectorCoefficient M) s =
        classicalDetectorMollifier M s * riemannZeta s
  forwardMellin :
    ∀ (M : ℕ) {z w : ℂ}, 1 < z.re → 0 < w.re →
      mellin (classicalDetectorExponentialSeries M z) w =
        Complex.Gamma w *
          (classicalDetectorMollifier M (z + w) * riemannZeta (z + w))
  cancelledGammaSource :
    ∀ {rho : ℂ}, IsNontrivialZero rho → ∀ {w : ℂ}, w ≠ 0 →
      classicalDetectorCancelledGammaZeta rho w =
        Complex.Gamma w * riemannZeta (rho + w)
  cancelledGammaHolomorphic :
    ∀ {rho : ℂ}, IsNontrivialZero rho →
      DifferentiableOn ℂ (classicalDetectorCancelledGammaZeta rho)
        (classicalDetectorCancelledGammaZetaDomain rho)
  zetaPoleResidue :
    ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
      ∀ {Y : ℝ}, 0 < Y →
        Tendsto
          (fun w : ℂ =>
            (w - (1 - rho)) *
              classicalDetectorMellinContourFactor M rho Y w)
          (𝓝[≠] (1 - rho))
          (𝓝 ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1))
  finiteDetector :
    ∀ {ι : Type} [Fintype ι] (block : ι → ℂ) (error remainder : ℂ),
      (1 : ℂ) + error + ∑ i, block i = remainder →
      ‖error‖ ≤ 1 / 3 →
      1 / (3 * (Fintype.card ι + 1) : ℝ) ≤ ‖remainder‖ ∨
        ∃ i, 1 / (3 * (Fintype.card ι + 1) : ℝ) ≤ ‖block i‖
  cardinalityControl :
    ∀ (k : ℕ), 0 < k →
      ∃ block : Fin k → ℂ,
        (∑ i, block i) = 1 ∧
          ∀ i, ‖block i‖ = 1 / k

theorem classicalDetectorMellinPartialCertificate_endpoint :
    ClassicalDetectorMellinPartialCertificate where
  coefficientFormula := classicalDetectorCoefficient_eq_divisorSum
  coefficientOne := classicalDetectorCoefficient_one
  coefficientGap := classicalDetectorCoefficient_eq_zero
  sourceProduct := fun hs M => LSeries_classicalDetectorCoefficient_eq hs M
  forwardMellin :=
    mellin_classicalDetectorExponentialSeries_eq_gamma_mul_mollifier_mul_zeta
  cancelledGammaSource := classicalDetectorCancelledGammaZeta_eq_source
  cancelledGammaHolomorphic :=
    differentiableOn_classicalDetectorCancelledGammaZeta
  zetaPoleResidue := tendsto_classicalDetectorMellinContourFactor_zetaPole
  finiteDetector := fun block error remainder hidentity herror =>
    exists_large_block_or_remainder block error remainder hidentity herror
  cardinalityControl := uniform_blocks_sum_one

end

end LeanLab.Riemann
