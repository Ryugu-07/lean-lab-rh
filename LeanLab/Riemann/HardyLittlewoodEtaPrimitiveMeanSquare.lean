import LeanLab.Riemann.HardyLittlewoodEtaRemainder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

open Complex Filter Finset Real Set Topology
open scoped BigOperators Interval

namespace LeanLab.Riemann

noncomputable section

theorem hardyLittlewoodThetaLogWeight_smul_etaSourceTerm_eq_thetaTerm (shift t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaLogWeight n •
        hardyLittlewoodEtaSourceTerm
          (hardyCriticalLinePoint (t + shift)) n =
      hardyLittlewoodThetaTerm shift n t := by
  have hsource :
      hardyLittlewoodEtaSourceTerm
          (hardyCriticalLinePoint (t + shift)) n =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) •
          hardyLittlewoodEtaUnitPhase (t + shift) n := by
    convert hardyLittlewoodEtaSourceTerm_eq_rpow_smul_unitPhase
      (1 / 2) (t + shift)
        (by exact_mod_cast (show 1 ≤ n by omega)) using 1
    apply congrArg (fun s => hardyLittlewoodEtaSourceTerm s n)
    apply Complex.ext <;> simp [hardyCriticalLinePoint]
  rw [hsource]
  rw [hardyLittlewoodThetaLogWeight_eq hn]
  unfold hardyLittlewoodThetaTerm hardyLittlewoodThetaCoeff
    hardyLittlewoodThetaPhase hardyLittlewoodEtaUnitPhase
  rw [if_pos hn, if_neg (by omega)]
  have hnpos : (0 : ℝ) < n := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  have hrpow :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hnpos.le]
  rw [hrpow]
  change
    ((Real.log (n : ℝ))⁻¹ : ℝ) •
        ((Real.sqrt (n : ℝ))⁻¹ : ℝ) •
          (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
            Complex.exp ((-((t + shift) * Real.log n) : ℝ) * Complex.I))) =
      ((((-1 : ℝ) ^ (n - 1) /
        (Real.sqrt n * Real.log n) : ℝ) : ℂ) *
          Complex.exp ((-((t + shift) * Real.log n) : ℝ) * Complex.I))
  rw [smul_smul]
  change
    (((Real.log (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) *
          (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
            Complex.exp ((-((t + shift) * Real.log n) : ℝ) * Complex.I))) =
      ((((-1 : ℝ) ^ (n - 1) /
        (Real.sqrt n * Real.log n) : ℝ) : ℂ) *
          Complex.exp ((-((t + shift) * Real.log n) : ℝ) * Complex.I))
  have hsign : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
    have he : n + 1 = (n - 1) + 2 := by omega
    rw [he, pow_add]
    norm_num
  rw [hsign]
  push_cast
  field_simp

theorem hardyLittlewoodThetaPartialSum_critical_eq_polynomial
    (N : ℕ) (shift t : ℝ) :
    hardyLittlewoodThetaPartialSum
        (hardyCriticalLinePoint (t + shift)) N =
      hardyLittlewoodThetaPolynomial N shift t := by
  rw [hardyLittlewoodThetaPartialSum, hardyLittlewoodThetaPolynomial]
  have hsubset : Finset.Icc 2 N ⊆ Finset.range (N + 1) := by
    intro n hn
    have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
    rw [Finset.mem_range]
    omega
  have hextra :
      ∀ n ∈ Finset.range (N + 1), n ∉ Finset.Icc 2 N →
        hardyLittlewoodThetaLogWeight n •
          hardyLittlewoodEtaSourceTerm
            (hardyCriticalLinePoint (t + shift)) n = 0 := by
    intro n hnRange hnIcc
    have hnlt : n < 2 := by
      rw [Finset.mem_range] at hnRange
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnIcc
      omega
    simp [hardyLittlewoodThetaLogWeight, not_le.mpr hnlt]
  rw [← Finset.sum_subset hsubset hextra]
  apply sum_congr rfl
  intro n hn
  exact hardyLittlewoodThetaLogWeight_smul_etaSourceTerm_eq_thetaTerm shift t (Finset.mem_Icc.mp hn).1

theorem hasDerivAt_hardyLittlewoodThetaTerm
    (shift t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    HasDerivAt (hardyLittlewoodThetaTerm shift n)
      (-Complex.I *
        hardyLittlewoodEtaSourceTerm
          (hardyCriticalLinePoint (t + shift)) n) t := by
  let s : ℂ := -((Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I
  have hexp :
      HasDerivAt
        (fun y : ℝ =>
          Complex.exp (s * (((y + shift : ℝ) : ℝ) : ℂ)))
        (s * Complex.exp (s * (((t + shift : ℝ) : ℝ) : ℂ))) t := by
    simpa [mul_comm] using
      (((Complex.ofRealCLM.hasDerivAt (x := t)).add_const
        (shift : ℂ)).const_mul s).cexp
  have hterm :
      HasDerivAt
        (fun y : ℝ =>
          (hardyLittlewoodThetaCoeff n : ℂ) *
            Complex.exp (s * (((y + shift : ℝ) : ℝ) : ℂ)))
        ((hardyLittlewoodThetaCoeff n : ℂ) *
          (s * Complex.exp (s * (((t + shift : ℝ) : ℝ) : ℂ)))) t :=
    hexp.const_mul _
  convert hterm using 1
  · funext y
    unfold hardyLittlewoodThetaTerm hardyLittlewoodThetaPhase
    dsimp only [s]
    congr 2
    apply Complex.ext <;> simp <;> ring
  · symm
    calc
      (hardyLittlewoodThetaCoeff n : ℂ) *
            (s * Complex.exp (s * (((t + shift : ℝ) : ℝ) : ℂ))) =
          s * hardyLittlewoodThetaTerm shift n t := by
        have harg :
            s * (((t + shift : ℝ) : ℝ) : ℂ) =
              ((-((t + shift) * Real.log n) : ℝ) : ℂ) *
                Complex.I := by
          dsimp only [s]
          push_cast
          ring
        rw [harg]
        unfold hardyLittlewoodThetaTerm hardyLittlewoodThetaPhase
        ring
      _ = -Complex.I *
          hardyLittlewoodEtaSourceTerm
            (hardyCriticalLinePoint (t + shift)) n := by
        rw [← hardyLittlewoodThetaLogWeight_smul_etaSourceTerm_eq_thetaTerm shift t hn,
          hardyLittlewoodThetaLogWeight_eq hn]
        dsimp only [s]
        change
          (-((Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) *
              ((((Real.log (n : ℝ))⁻¹ : ℝ) : ℂ) *
                hardyLittlewoodEtaSourceTerm
                  (hardyCriticalLinePoint (t + shift)) n) =
            -Complex.I *
              hardyLittlewoodEtaSourceTerm
                (hardyCriticalLinePoint (t + shift)) n
        have hlog : Real.log (n : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
        let L : ℂ := ((Real.log (n : ℝ) : ℝ) : ℂ)
        have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
        rw [Complex.ofReal_inv]
        change (-L * Complex.I) *
              (L⁻¹ * hardyLittlewoodEtaSourceTerm
                (hardyCriticalLinePoint (t + shift)) n) =
            -Complex.I * hardyLittlewoodEtaSourceTerm
              (hardyCriticalLinePoint (t + shift)) n
        field_simp [hL]

theorem hasDerivAt_neg_im_hardyLittlewoodThetaTerm
    (shift t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    HasDerivAt
      (fun y : ℝ => -(hardyLittlewoodThetaTerm shift n y).im)
      (hardyLittlewoodEtaSourceTerm
        (hardyCriticalLinePoint (t + shift)) n).re t := by
  have hcomplex := hasDerivAt_hardyLittlewoodThetaTerm shift t hn
  have him :
      HasDerivAt
        (fun y : ℝ => (hardyLittlewoodThetaTerm shift n y).im)
        (-Complex.I *
          hardyLittlewoodEtaSourceTerm
            (hardyCriticalLinePoint (t + shift)) n).im t := by
    simpa only [Complex.imCLM_apply, zero_apply,
      zero_add] using
      (hasDerivAt_const t Complex.imCLM).clm_apply hcomplex
  have hscaled :
      HasDerivAt
        (fun y : ℝ => (-1 : ℝ) *
          (hardyLittlewoodThetaTerm shift n y).im)
        ((-1 : ℝ) *
          (-Complex.I *
            hardyLittlewoodEtaSourceTerm
              (hardyCriticalLinePoint (t + shift)) n).im) t :=
    him.const_mul (-1)
  have hderiv :
      -(-(Complex.I *
        hardyLittlewoodEtaSourceTerm
          (hardyCriticalLinePoint (t + shift)) n)).im =
        (hardyLittlewoodEtaSourceTerm
          (hardyCriticalLinePoint (t + shift)) n).re := by
    generalize hardyLittlewoodEtaSourceTerm
      (hardyCriticalLinePoint (t + shift)) n = z
    rcases z with ⟨x, y⟩
    norm_num [Complex.mul_im]
  simpa only [neg_mul, one_mul, hderiv] using hscaled

theorem hardyLittlewoodEtaPartialSum_critical_sub_one_eq_sum
    (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    hardyLittlewoodEtaPartialSum (hardyCriticalLinePoint t) N - 1 =
      ∑ n ∈ Finset.Icc 2 N,
        hardyLittlewoodEtaSourceTerm (hardyCriticalLinePoint t) n := by
  rw [hardyLittlewoodEtaPartialSum]
  let source : ℕ → ℂ :=
    hardyLittlewoodEtaSourceTerm (hardyCriticalLinePoint t)
  have hsubset :
      insert 1 (Finset.Icc 2 N) ⊆ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_insert] at hn
    rw [Finset.mem_range]
    rcases hn with rfl | hn
    · omega
    · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2
  have hextra :
      ∀ n ∈ Finset.range (N + 1),
        n ∉ insert 1 (Finset.Icc 2 N) → source n = 0 := by
    intro n hnRange hnInsert
    have hnlt : n < N + 1 := Finset.mem_range.mp hnRange
    have hnNeOne : n ≠ 1 := by
      intro hn
      exact hnInsert (Finset.mem_insert.mpr (Or.inl hn))
    have hnNotIcc : n ∉ Finset.Icc 2 N := by
      intro hn
      exact hnInsert (Finset.mem_insert.mpr (Or.inr hn))
    have hnZero : n = 0 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnNotIcc
      omega
    subst n
    simp [source, hardyLittlewoodEtaSourceTerm]
  have hsum := Finset.sum_subset hsubset hextra
  have honeNotMem : 1 ∉ Finset.Icc 2 N := by simp
  rw [Finset.sum_insert honeNotMem] at hsum
  have hsourceOne : source 1 = 1 := by
    simp [source, hardyLittlewoodEtaSourceTerm]
  rw [hsourceOne] at hsum
  change (∑ n ∈ Finset.range (N + 1), source n) - 1 =
    ∑ n ∈ Finset.Icc 2 N, source n
  rw [← hsum]
  ring

theorem hasDerivAt_neg_im_hardyLittlewoodThetaPolynomial
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) :
    HasDerivAt
      (fun y : ℝ => -(hardyLittlewoodThetaPolynomial N 0 y).im)
      ((hardyLittlewoodEtaPartialSum (hardyCriticalLinePoint t) N).re - 1) t := by
  have hsum :
      HasDerivAt
        (fun y : ℝ =>
          ∑ n ∈ Finset.Icc 2 N,
            -(hardyLittlewoodThetaTerm 0 n y).im)
        (∑ n ∈ Finset.Icc 2 N,
          (hardyLittlewoodEtaSourceTerm
            (hardyCriticalLinePoint t) n).re) t := by
    apply HasDerivAt.fun_sum
    intro n hn
    simpa using
      hasDerivAt_neg_im_hardyLittlewoodThetaTerm 0 t (Finset.mem_Icc.mp hn).1
  convert hsum using 1
  · funext y
    rw [hardyLittlewoodThetaPolynomial]
    change
      -(Complex.imCLM
          (∑ n ∈ Finset.Icc 2 N,
            hardyLittlewoodThetaTerm 0 n y)) =
        ∑ n ∈ Finset.Icc 2 N,
          -(Complex.imCLM (hardyLittlewoodThetaTerm 0 n y))
    rw [map_sum Complex.imCLM]
    symm
    exact Finset.sum_neg_distrib
      (fun n => Complex.imCLM (hardyLittlewoodThetaTerm 0 n y))
  · have hre := congrArg Complex.re
        (hardyLittlewoodEtaPartialSum_critical_sub_one_eq_sum t hN)
    have hreSum :
        (∑ n ∈ Finset.Icc 2 N,
          hardyLittlewoodEtaSourceTerm
            (hardyCriticalLinePoint t) n).re =
          ∑ n ∈ Finset.Icc 2 N,
            (hardyLittlewoodEtaSourceTerm
              (hardyCriticalLinePoint t) n).re := by
      change
        Complex.reCLM
            (∑ n ∈ Finset.Icc 2 N,
              hardyLittlewoodEtaSourceTerm
                (hardyCriticalLinePoint t) n) =
          ∑ n ∈ Finset.Icc 2 N,
            Complex.reCLM
              (hardyLittlewoodEtaSourceTerm
                (hardyCriticalLinePoint t) n)
      exact map_sum Complex.reCLM _ _
    rw [← hreSum]
    simpa only [sub_re, one_re] using hre

theorem integral_hardyLittlewoodEtaPartialSum_real_sub_one_eq_thetaPolynomial
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) :
    (∫ u in (0 : ℝ)..t,
        ((hardyLittlewoodEtaPartialSum
          (hardyCriticalLinePoint u) N).re - 1)) =
      -(hardyLittlewoodThetaPolynomial N 0 t -
          hardyLittlewoodThetaPolynomial N 0 0).im := by
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt
          (fun y : ℝ =>
            -(hardyLittlewoodThetaPolynomial N 0 y).im)
          ((hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N).re - 1) x := by
    intro x _hx
    exact hasDerivAt_neg_im_hardyLittlewoodThetaPolynomial N x hN
  have hcontinuous :
      Continuous
        (fun x : ℝ =>
          (hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N).re - 1) := by
    have hcritical : Continuous hardyCriticalLinePoint := by
      unfold hardyCriticalLinePoint
      fun_prop
    have heta :
        Continuous
          (fun x : ℝ =>
            hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N) := by
      change Continuous
        ((fun s : ℂ => hardyLittlewoodEtaPartialSum s N) ∘
          hardyCriticalLinePoint)
      exact
        (differentiable_hardyLittlewoodEtaPartialSum N).continuous.comp
          hcritical
    exact (Complex.continuous_re.comp heta).sub continuous_const
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcontinuous.intervalIntegrable (0 : ℝ) t)
  convert hFTC using 1
  rw [Complex.sub_im]
  ring

def hardyLittlewoodThetaSeriesValue (s : ℂ) : ℂ :=
  Filter.limUnder Filter.atTop
    (fun N => hardyLittlewoodThetaPartialSum s N)

theorem tendsto_hardyLittlewoodThetaSeriesValue
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) :
    Tendsto (hardyLittlewoodThetaPartialSum s) atTop
      (𝓝 (hardyLittlewoodThetaSeriesValue s)) := by
  obtain ⟨thetaValue, htheta, _hbound⟩ :=
    exists_hardyLittlewoodThetaValue_of_re_pos s hs_ne hs_re
  exact htheta.cauchySeq.tendsto_limUnder

theorem norm_hardyLittlewoodThetaSeriesValue_sub_partialSum_le
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) {N : ℕ}
    (hN : max 2 ⌈|s.im|⌉₊ ≤ N) :
    ‖hardyLittlewoodThetaSeriesValue s -
        hardyLittlewoodThetaPartialSum s N‖ ≤
      8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-s.re) := by
  obtain ⟨thetaValue, htheta, hbound⟩ :=
    exists_hardyLittlewoodThetaValue_of_re_pos s hs_ne hs_re
  have hcanonical :=
    tendsto_hardyLittlewoodThetaSeriesValue s hs_ne hs_re
  have heq :
      thetaValue = hardyLittlewoodThetaSeriesValue s :=
    tendsto_nhds_unique htheta hcanonical
  rw [← heq]
  exact hbound N hN

theorem norm_hardyLittlewoodThetaSeriesValue_critical_sub_polynomial_le
    (t : ℝ) {N : ℕ} (hN : max 2 ⌈|t|⌉₊ ≤ N) :
    ‖hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
        hardyLittlewoodThetaPolynomial N 0 t‖ ≤
      8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hne : hardyCriticalLinePoint t ≠ (1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hardyCriticalLinePoint] at hre
  have him :
      |(hardyCriticalLinePoint t).im| = |t| := by
    simp [hardyCriticalLinePoint]
  have hbound :=
    norm_hardyLittlewoodThetaSeriesValue_sub_partialSum_le
      (hardyCriticalLinePoint t) hne (by norm_num [hardyCriticalLinePoint])
      (N := N)
  rw [him] at hbound
  have hbound' := hbound hN
  have halign := hardyLittlewoodThetaPartialSum_critical_eq_polynomial N 0 t
  simp only [add_zero] at halign
  rw [halign] at hbound'
  simpa only [hardyCriticalLinePoint_re] using hbound'

def hardyLittlewoodEtaPartialPrimitive (N : ℕ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t,
    (hardyLittlewoodEtaPartialSum
      (hardyCriticalLinePoint u) N).re - 1

theorem abs_hardyLittlewoodEtaPrimitive_sub_partialPrimitive_le
    (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (ht : ⌈|t|⌉₊ ≤ N) :
    |hardyLittlewoodEtaPrimitive t -
        hardyLittlewoodEtaPartialPrimitive N t| ≤
      (4 * (N : ℝ) ^ (-(1 / 2 : ℝ))) * |t| := by
  have hpartialContinuous :
      Continuous
        (fun x : ℝ =>
          (hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N).re - 1) := by
    have hcritical : Continuous hardyCriticalLinePoint := by
      unfold hardyCriticalLinePoint
      fun_prop
    have heta :
        Continuous
          (fun x : ℝ =>
            hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N) := by
      change Continuous
        ((fun s : ℂ => hardyLittlewoodEtaPartialSum s N) ∘
          hardyCriticalLinePoint)
      exact
        (differentiable_hardyLittlewoodEtaPartialSum N).continuous.comp
          hcritical
    exact (Complex.continuous_re.comp heta).sub continuous_const
  have hactualInt :
      IntervalIntegrable
        (fun x : ℝ => hardyLittlewoodEtaReal x - 1)
        MeasureTheory.volume 0 t :=
    (continuous_hardyLittlewoodEtaReal.sub continuous_const).intervalIntegrable
      0 t
  have hpartialInt :
      IntervalIntegrable
        (fun x : ℝ =>
          (hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N).re - 1)
        MeasureTheory.volume 0 t :=
    hpartialContinuous.intervalIntegrable 0 t
  have hpoint :
      ∀ x ∈ Set.uIoc (0 : ℝ) t,
        ‖(hardyLittlewoodEtaReal x - 1) -
            ((hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N).re - 1)‖ ≤
          4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hxt : |x| ≤ |t| := by
      rw [Set.mem_uIoc] at hx
      rcases hx with hx | hx
      · rw [abs_of_nonneg hx.1.le,
          abs_of_nonneg (hx.1.le.trans hx.2)]
        exact hx.2
      · rw [abs_of_nonpos hx.2,
          abs_of_nonpos (hx.1.le.trans hx.2)]
        linarith
    have htN : |t| ≤ (N : ℝ) :=
      (Nat.le_ceil |t|).trans (by exact_mod_cast ht)
    have hrem :=
      norm_hardyLittlewoodEtaCritical_sub_partialSum_le
        x hN (hxt.trans htN)
    calc
      ‖(hardyLittlewoodEtaReal x - 1) -
          ((hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N).re - 1)‖ =
          |(hardyLittlewoodEtaCritical x -
              hardyLittlewoodEtaPartialSum
                (hardyCriticalLinePoint x) N).re| := by
        rw [Real.norm_eq_abs]
        unfold hardyLittlewoodEtaReal
        simp only [Complex.sub_re]
        congr 1
        ring
      _ ≤ ‖hardyLittlewoodEtaCritical x -
          hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N‖ :=
        Complex.abs_re_le_norm _
      _ ≤ 4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := hrem
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub hactualInt hpartialInt] at hnorm
  simpa only [hardyLittlewoodEtaPrimitive,
    hardyLittlewoodEtaPartialPrimitive, Real.norm_eq_abs, sub_zero]
    using hnorm

theorem tendsto_hardyLittlewoodEtaPartialPrimitive
    (t : ℝ) :
    Tendsto (fun N => hardyLittlewoodEtaPartialPrimitive N t) atTop
      (𝓝 (hardyLittlewoodEtaPrimitive t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · refine eventually_atTop.2
      ⟨max 1 ⌈|t|⌉₊, ?_⟩
    intro N hN
    have hNOne : 1 ≤ N := (le_max_left 1 ⌈|t|⌉₊).trans hN
    have hNCeil : ⌈|t|⌉₊ ≤ N :=
      (le_max_right 1 ⌈|t|⌉₊).trans hN
    have hbound :=
      abs_hardyLittlewoodEtaPrimitive_sub_partialPrimitive_le
        t hNOne hNCeil
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hbound
  · have hpow :
        Tendsto
          (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    simpa only [mul_zero, zero_mul] using
      (hpow.const_mul 4).mul_const |t|

theorem hardyLittlewoodEtaPartialPrimitive_eq_thetaPolynomial
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) :
    hardyLittlewoodEtaPartialPrimitive N t =
      -(hardyLittlewoodThetaPolynomial N 0 t -
          hardyLittlewoodThetaPolynomial N 0 0).im := by
  exact integral_hardyLittlewoodEtaPartialSum_real_sub_one_eq_thetaPolynomial N t hN

theorem tendsto_hardyLittlewoodThetaPolynomial
    (t : ℝ) :
    Tendsto (fun N => hardyLittlewoodThetaPolynomial N 0 t) atTop
      (𝓝 (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint t))) := by
  have hne : hardyCriticalLinePoint t ≠ (1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hardyCriticalLinePoint] at hre
  have htheta :=
    tendsto_hardyLittlewoodThetaSeriesValue
      (hardyCriticalLinePoint t) hne
      (by norm_num [hardyCriticalLinePoint])
  apply htheta.congr'
  exact Filter.Eventually.of_forall (fun N => by
    have halign := hardyLittlewoodThetaPartialSum_critical_eq_polynomial N 0 t
    simpa only [add_zero] using halign)

theorem hardyLittlewoodEtaPrimitive_eq_thetaSeriesValue
    (t : ℝ) :
    hardyLittlewoodEtaPrimitive t =
      -(hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
          hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint 0)).im := by
  have ht := tendsto_hardyLittlewoodThetaPolynomial t
  have hzero := tendsto_hardyLittlewoodThetaPolynomial 0
  have hsub := ht.sub hzero
  have him :
      Tendsto
        (fun N =>
          (hardyLittlewoodThetaPolynomial N 0 t -
            hardyLittlewoodThetaPolynomial N 0 0).im)
        atTop
        (𝓝 ((hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint t) -
          hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint 0)).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp hsub
  have hsource := him.neg
  have hfinite :
      (fun N => hardyLittlewoodEtaPartialPrimitive N t) =ᶠ[atTop]
        (fun N =>
          -(hardyLittlewoodThetaPolynomial N 0 t -
              hardyLittlewoodThetaPolynomial N 0 0).im) := by
    exact eventually_atTop.2
      ⟨1, fun N hN =>
        hardyLittlewoodEtaPartialPrimitive_eq_thetaPolynomial N t hN⟩
  have hsource' :
      Tendsto (fun N => hardyLittlewoodEtaPartialPrimitive N t) atTop
        (𝓝
          (-(hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint t) -
            hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint 0)).im)) :=
    hsource.congr' hfinite.symm
  exact tendsto_nhds_unique
    (tendsto_hardyLittlewoodEtaPartialPrimitive t) hsource'

def hardyLittlewoodEtaComplexPrimitive (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t,
    hardyLittlewoodEtaCritical u - 1

def hardyLittlewoodEtaPartialComplexPrimitive
    (N : ℕ) (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t,
    hardyLittlewoodEtaPartialSum
      (hardyCriticalLinePoint u) N - 1

theorem hasDerivAt_hardyLittlewoodThetaPolynomial
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) :
    HasDerivAt
      (hardyLittlewoodThetaPolynomial N 0)
      (-Complex.I *
        (hardyLittlewoodEtaPartialSum
          (hardyCriticalLinePoint t) N - 1)) t := by
  have hsum :
      HasDerivAt
        (fun y : ℝ =>
          ∑ n ∈ Finset.Icc 2 N,
            hardyLittlewoodThetaTerm 0 n y)
        (∑ n ∈ Finset.Icc 2 N,
          -Complex.I *
            hardyLittlewoodEtaSourceTerm
              (hardyCriticalLinePoint t) n) t := by
    apply HasDerivAt.fun_sum
    intro n hn
    simpa using
      hasDerivAt_hardyLittlewoodThetaTerm 0 t (Finset.mem_Icc.mp hn).1
  convert hsum using 1
  · funext y
    rfl
  · rw [hardyLittlewoodEtaPartialSum_critical_sub_one_eq_sum t hN,
      Finset.mul_sum]

theorem hardyLittlewoodEtaPartialComplexPrimitive_eq_thetaPolynomial
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) :
    hardyLittlewoodEtaPartialComplexPrimitive N t =
      Complex.I *
        (hardyLittlewoodThetaPolynomial N 0 t -
          hardyLittlewoodThetaPolynomial N 0 0) := by
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt
          (hardyLittlewoodThetaPolynomial N 0)
          (-Complex.I *
            (hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N - 1)) x := by
    intro x _hx
    exact hasDerivAt_hardyLittlewoodThetaPolynomial N x hN
  have hcritical : Continuous hardyCriticalLinePoint := by
    unfold hardyCriticalLinePoint
    fun_prop
  have heta :
      Continuous
        (fun x : ℝ =>
          hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N) := by
    change Continuous
      ((fun s : ℂ => hardyLittlewoodEtaPartialSum s N) ∘
        hardyCriticalLinePoint)
    exact
      (differentiable_hardyLittlewoodEtaPartialSum N).continuous.comp
        hcritical
  have hint :
      IntervalIntegrable
        (fun x : ℝ =>
          -Complex.I *
            (hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N - 1))
        MeasureTheory.volume 0 t :=
    (continuous_const.mul (heta.sub continuous_const)).intervalIntegrable
      0 t
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  unfold hardyLittlewoodEtaPartialComplexPrimitive
  calc
    (∫ u in (0 : ℝ)..t,
        hardyLittlewoodEtaPartialSum
          (hardyCriticalLinePoint u) N - 1) =
        Complex.I *
          (-Complex.I *
            ∫ u in (0 : ℝ)..t,
              hardyLittlewoodEtaPartialSum
                (hardyCriticalLinePoint u) N - 1) := by
      rw [← mul_assoc, mul_neg, Complex.I_mul_I]
      ring
    _ = Complex.I *
        (hardyLittlewoodThetaPolynomial N 0 t -
          hardyLittlewoodThetaPolynomial N 0 0) := by
      rw [hFTC]

theorem norm_hardyLittlewoodEtaComplexPrimitive_sub_partial_le
    (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (ht : ⌈|t|⌉₊ ≤ N) :
    ‖hardyLittlewoodEtaComplexPrimitive t -
        hardyLittlewoodEtaPartialComplexPrimitive N t‖ ≤
      (4 * (N : ℝ) ^ (-(1 / 2 : ℝ))) * |t| := by
  have hactual :
      Continuous
        (fun x : ℝ => hardyLittlewoodEtaCritical x - 1) :=
    continuous_hardyLittlewoodEtaCritical.sub continuous_const
  have hcritical : Continuous hardyCriticalLinePoint := by
    unfold hardyCriticalLinePoint
    fun_prop
  have hpartial :
      Continuous
        (fun x : ℝ =>
          hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint x) N - 1) := by
    have heta :
        Continuous
          (fun x : ℝ =>
            hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N) := by
      change Continuous
        ((fun s : ℂ => hardyLittlewoodEtaPartialSum s N) ∘
          hardyCriticalLinePoint)
      exact
        (differentiable_hardyLittlewoodEtaPartialSum N).continuous.comp
          hcritical
    exact heta.sub continuous_const
  have hpoint :
      ∀ x ∈ Set.uIoc (0 : ℝ) t,
        ‖(hardyLittlewoodEtaCritical x - 1) -
            (hardyLittlewoodEtaPartialSum
              (hardyCriticalLinePoint x) N - 1)‖ ≤
          4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hxt : |x| ≤ |t| := by
      rw [Set.mem_uIoc] at hx
      rcases hx with hx | hx
      · rw [abs_of_nonneg hx.1.le,
          abs_of_nonneg (hx.1.le.trans hx.2)]
        exact hx.2
      · rw [abs_of_nonpos hx.2,
          abs_of_nonpos (hx.1.le.trans hx.2)]
        linarith
    have htN : |t| ≤ (N : ℝ) :=
      (Nat.le_ceil |t|).trans (by exact_mod_cast ht)
    simpa only [sub_sub_sub_cancel_right] using
      norm_hardyLittlewoodEtaCritical_sub_partialSum_le
        x hN (hxt.trans htN)
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub
    (hactual.intervalIntegrable 0 t)
    (hpartial.intervalIntegrable 0 t)] at hnorm
  simpa only [hardyLittlewoodEtaComplexPrimitive,
    hardyLittlewoodEtaPartialComplexPrimitive, sub_zero] using hnorm

theorem tendsto_hardyLittlewoodEtaPartialComplexPrimitive
    (t : ℝ) :
    Tendsto
      (fun N => hardyLittlewoodEtaPartialComplexPrimitive N t)
      atTop (𝓝 (hardyLittlewoodEtaComplexPrimitive t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · refine eventually_atTop.2
      ⟨max 1 ⌈|t|⌉₊, ?_⟩
    intro N hN
    have hbound :=
      norm_hardyLittlewoodEtaComplexPrimitive_sub_partial_le t
        ((le_max_left 1 ⌈|t|⌉₊).trans hN)
        ((le_max_right 1 ⌈|t|⌉₊).trans hN)
    simpa only [norm_sub_rev] using hbound
  · have hpow :
        Tendsto
          (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ)))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    simpa only [mul_zero, zero_mul] using
      (hpow.const_mul 4).mul_const |t|

theorem hardyLittlewoodEtaComplexPrimitive_eq_thetaSeriesValue
    (t : ℝ) :
    hardyLittlewoodEtaComplexPrimitive t =
      Complex.I *
        (hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
          hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint 0)) := by
  have hsource :=
    (tendsto_hardyLittlewoodThetaPolynomial t).sub
      (tendsto_hardyLittlewoodThetaPolynomial 0)
  have hsourceI := hsource.const_mul Complex.I
  have hfinite :
      (fun N => hardyLittlewoodEtaPartialComplexPrimitive N t) =ᶠ[atTop]
        (fun N =>
          Complex.I *
            (hardyLittlewoodThetaPolynomial N 0 t -
              hardyLittlewoodThetaPolynomial N 0 0)) := by
    exact eventually_atTop.2
      ⟨1, fun N hN =>
        hardyLittlewoodEtaPartialComplexPrimitive_eq_thetaPolynomial N t hN⟩
  have hsource' :
      Tendsto
        (fun N => hardyLittlewoodEtaPartialComplexPrimitive N t)
        atTop
        (𝓝
          (Complex.I *
            (hardyLittlewoodThetaSeriesValue
                (hardyCriticalLinePoint t) -
              hardyLittlewoodThetaSeriesValue
                (hardyCriticalLinePoint 0)))) :=
    hsourceI.congr' hfinite.symm
  exact tendsto_nhds_unique
    (tendsto_hardyLittlewoodEtaPartialComplexPrimitive t) hsource'

theorem continuous_hardyLittlewoodEtaComplexPrimitive :
    Continuous hardyLittlewoodEtaComplexPrimitive := by
  apply intervalIntegral.continuous_primitive
    (a := 0)
  intro a b
  have hcontinuous :
      Continuous
        (fun x : ℝ => hardyLittlewoodEtaCritical x - (1 : ℂ)) :=
    continuous_hardyLittlewoodEtaCritical.sub continuous_const
  exact hcontinuous.intervalIntegrable a b

theorem hardyLittlewoodThetaSeriesValue_critical_eq
    (t : ℝ) :
    hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) =
      hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint 0) -
        Complex.I * hardyLittlewoodEtaComplexPrimitive t := by
  have hprimitive :=
    hardyLittlewoodEtaComplexPrimitive_eq_thetaSeriesValue t
  calc
    hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) =
        hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint 0) +
          (hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
            hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint 0)) := by ring
    _ = hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint 0) -
        Complex.I * hardyLittlewoodEtaComplexPrimitive t := by
      rw [hprimitive]
      rw [← mul_assoc, Complex.I_mul_I]
      ring

theorem continuous_hardyLittlewoodThetaSeriesValue_critical :
    Continuous
      (fun t : ℝ =>
        hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint t)) := by
  have heq :
      (fun t : ℝ =>
        hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint t)) =
        (fun t : ℝ =>
          hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint 0) -
            Complex.I * hardyLittlewoodEtaComplexPrimitive t) := by
    funext t
    exact hardyLittlewoodThetaSeriesValue_critical_eq t
  rw [heq]
  exact continuous_const.sub
    (continuous_const.mul
      continuous_hardyLittlewoodEtaComplexPrimitive)

theorem normSq_le_two_mul_add_tail
    (z w : ℂ) :
    Complex.normSq z ≤
      2 * Complex.normSq w + 2 * ‖z - w‖ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hnorm :
      ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
    calc
      ‖z‖ = ‖w + (z - w)‖ := by ring_nf
      _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
  have hsquare :
      ‖z‖ ^ 2 ≤ (‖w‖ + ‖z - w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z)
      (add_nonneg (norm_nonneg w) (norm_nonneg (z - w)))).2 hnorm
  nlinarith [sq_nonneg (‖w‖ - ‖z - w‖)]

def hardyLittlewoodThetaTailConstant : ℝ :=
  8 * (Real.log 2)⁻¹

def hardyLittlewoodThetaMeanSquareConstant : ℝ :=
  2 * (6 / Real.log 2 +
    16 * (hardyLittlewoodNearPairConstant +
      hardyLittlewoodFarPairConstant)) +
    2 * hardyLittlewoodThetaTailConstant ^ 2

theorem hardyLittlewoodThetaTailConstant_pos :
    0 < hardyLittlewoodThetaTailConstant := by
  unfold hardyLittlewoodThetaTailConstant
  positivity

theorem hardyLittlewoodThetaMeanSquareConstant_nonneg :
    0 ≤ hardyLittlewoodThetaMeanSquareConstant := by
  unfold hardyLittlewoodThetaMeanSquareConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpairs :
      0 ≤ hardyLittlewoodNearPairConstant +
        hardyLittlewoodFarPairConstant :=
    add_nonneg hardyLittlewoodNearPairConstant_pos.le
      hardyLittlewoodFarPairConstant_pos.le
  positivity

def hardyLittlewoodThetaCutoff (T : ℝ) : ℕ :=
  ⌈3 * T⌉₊

theorem three_mul_le_thetaCutoff
    (T : ℝ) :
    3 * T ≤ (hardyLittlewoodThetaCutoff T : ℝ) := by
  exact Nat.le_ceil (3 * T)

theorem thetaCutoff_two_le
    {T : ℝ} (hT : 1 ≤ T) :
    2 ≤ hardyLittlewoodThetaCutoff T := by
  have hreal :
      (2 : ℝ) ≤ (hardyLittlewoodThetaCutoff T : ℝ) := by
    linarith [three_mul_le_thetaCutoff T]
  exact_mod_cast hreal

theorem thetaCutoff_cast_le_four_mul
    {T : ℝ} (hT : 1 ≤ T) :
    (hardyLittlewoodThetaCutoff T : ℝ) ≤ 4 * T := by
  have hnonneg : 0 ≤ 3 * T := by positivity
  have hceil :
      (hardyLittlewoodThetaCutoff T : ℝ) < 3 * T + 1 := by
    exact Nat.ceil_lt_add_one hnonneg
  linarith

theorem norm_hardyLittlewoodThetaSeriesValue_sub_cutoff_le
    {T u t : ℝ} (hT : 1 ≤ T) (hu0 : 0 ≤ u) (huT : u ≤ T)
    (ht : t ∈ Set.Icc T (2 * T)) :
    ‖hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u)) -
        hardyLittlewoodThetaPolynomial
          (hardyLittlewoodThetaCutoff T) 0 (t + u)‖ ≤
      hardyLittlewoodThetaTailConstant := by
  have htu0 : 0 ≤ t + u := by linarith [ht.1]
  have htuN :
      |t + u| ≤ (hardyLittlewoodThetaCutoff T : ℝ) := by
    rw [abs_of_nonneg htu0]
    linarith [ht.2, huT, three_mul_le_thetaCutoff T]
  have hceil :
      ⌈|t + u|⌉₊ ≤ hardyLittlewoodThetaCutoff T :=
    Nat.ceil_le.mpr htuN
  have hmax :
      max 2 ⌈|t + u|⌉₊ ≤ hardyLittlewoodThetaCutoff T :=
    max_le (thetaCutoff_two_le hT) hceil
  have hrem :=
    norm_hardyLittlewoodThetaSeriesValue_critical_sub_polynomial_le
      (t + u) hmax
  have hcutoffOne :
      (1 : ℝ) ≤ (hardyLittlewoodThetaCutoff T : ℝ) := by
    exact_mod_cast (show 1 ≤ hardyLittlewoodThetaCutoff T by
      omega)
  have hpow :
      (hardyLittlewoodThetaCutoff T : ℝ) ^
          (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hcutoffOne (by norm_num)
  calc
    ‖hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u)) -
        hardyLittlewoodThetaPolynomial
          (hardyLittlewoodThetaCutoff T) 0 (t + u)‖ ≤
        hardyLittlewoodThetaTailConstant *
          (hardyLittlewoodThetaCutoff T : ℝ) ^
            (-(1 / 2 : ℝ)) := by
      simpa only [hardyLittlewoodThetaTailConstant] using hrem
    _ ≤ hardyLittlewoodThetaTailConstant * 1 :=
      mul_le_mul_of_nonneg_left hpow
        hardyLittlewoodThetaTailConstant_pos.le
    _ = hardyLittlewoodThetaTailConstant := mul_one _

theorem hardyLittlewoodThetaPolynomial_zero_add_eq_shift
    (N : ℕ) (u t : ℝ) :
    hardyLittlewoodThetaPolynomial N 0 (t + u) =
      hardyLittlewoodThetaPolynomial N u t := by
  unfold hardyLittlewoodThetaPolynomial
  apply Finset.sum_congr rfl
  intro n _hn
  unfold hardyLittlewoodThetaTerm hardyLittlewoodThetaPhase
  congr 2
  push_cast
  ring

theorem normSq_hardyLittlewoodThetaSeriesValue_le_cutoff
    {T u t : ℝ} (hT : 1 ≤ T) (hu0 : 0 ≤ u) (huT : u ≤ T)
    (ht : t ∈ Set.Icc T (2 * T)) :
    Complex.normSq
        (hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u))) ≤
      2 * Complex.normSq
        (hardyLittlewoodThetaPolynomial
          (hardyLittlewoodThetaCutoff T) u t) +
        2 * hardyLittlewoodThetaTailConstant ^ 2 := by
  have hbase :=
    normSq_le_two_mul_add_tail
      (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint (t + u)))
      (hardyLittlewoodThetaPolynomial
        (hardyLittlewoodThetaCutoff T) 0 (t + u))
  have htail :=
    norm_hardyLittlewoodThetaSeriesValue_sub_cutoff_le
      hT hu0 huT ht
  rw [hardyLittlewoodThetaPolynomial_zero_add_eq_shift] at hbase htail
  calc
    Complex.normSq
        (hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u))) ≤
      2 * Complex.normSq
        (hardyLittlewoodThetaPolynomial
          (hardyLittlewoodThetaCutoff T) u t) +
        2 * ‖hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint (t + u)) -
          hardyLittlewoodThetaPolynomial
            (hardyLittlewoodThetaCutoff T) u t‖ ^ 2 := hbase
    _ ≤ 2 * Complex.normSq
        (hardyLittlewoodThetaPolynomial
          (hardyLittlewoodThetaCutoff T) u t) +
        2 * hardyLittlewoodThetaTailConstant ^ 2 := by
      gcongr

theorem integral_normSq_hardyLittlewoodThetaSeriesValue_shift_le
    {T u : ℝ} (hT : 1 ≤ T) (hu0 : 0 ≤ u) (huT : u ≤ T) :
    (∫ t in T..2 * T,
      Complex.normSq
        (hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u)))) ≤
      hardyLittlewoodThetaMeanSquareConstant * T := by
  let N : ℕ := hardyLittlewoodThetaCutoff T
  have hTtwo : T ≤ 2 * T := by linarith
  have hpsiContinuous :
      Continuous
        (fun t : ℝ =>
          Complex.normSq
            (hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint (t + u)))) := by
    have hshift : Continuous (fun t : ℝ => t + u) :=
      continuous_id.add continuous_const
    exact Complex.continuous_normSq.comp
      (continuous_hardyLittlewoodThetaSeriesValue_critical.comp hshift)
  have hpolyContinuous :
      Continuous
        (fun t : ℝ =>
          Complex.normSq
            (hardyLittlewoodThetaPolynomial N u t)) :=
    Complex.continuous_normSq.comp
      (continuous_hardyLittlewoodThetaPolynomial N u)
  have hrhsContinuous :
      Continuous
        (fun t : ℝ =>
          2 * Complex.normSq
              (hardyLittlewoodThetaPolynomial N u t) +
            2 * hardyLittlewoodThetaTailConstant ^ 2) :=
    (continuous_const.mul hpolyContinuous).add continuous_const
  have hmono :
      (∫ t in T..2 * T,
        Complex.normSq
          (hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint (t + u)))) ≤
        ∫ t in T..2 * T,
          (2 * Complex.normSq
              (hardyLittlewoodThetaPolynomial N u t) +
            2 * hardyLittlewoodThetaTailConstant ^ 2) := by
    apply intervalIntegral.integral_mono_on hTtwo
      (hpsiContinuous.intervalIntegrable T (2 * T))
      (hrhsContinuous.intervalIntegrable T (2 * T))
    intro t ht
    exact normSq_hardyLittlewoodThetaSeriesValue_le_cutoff
      hT hu0 huT ht
  have hpairs :
      0 ≤ hardyLittlewoodNearPairConstant +
        hardyLittlewoodFarPairConstant :=
    add_nonneg hardyLittlewoodNearPairConstant_pos.le
      hardyLittlewoodFarPairConstant_pos.le
  have hfinite :
      hardyLittlewoodFiniteMeanSquare N u T T ≤
        T * (6 / Real.log 2 +
          16 * (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant)) := by
    calc
      hardyLittlewoodFiniteMeanSquare N u T T ≤
          T * (6 / Real.log 2) +
            4 * (N : ℝ) *
              (hardyLittlewoodNearPairConstant +
                hardyLittlewoodFarPairConstant) :=
        hardyLittlewoodFiniteMeanSquare_le_length_add_truncation
          N u T T (by linarith)
      _ ≤ T * (6 / Real.log 2) +
            4 * (4 * T) *
              (hardyLittlewoodNearPairConstant +
                hardyLittlewoodFarPairConstant) := by
        gcongr
        exact thetaCutoff_cast_le_four_mul hT
      _ = T * (6 / Real.log 2 +
          16 * (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant)) := by ring
  have hconstInt :
      IntervalIntegrable
        (fun _ : ℝ =>
          2 * hardyLittlewoodThetaTailConstant ^ 2)
        MeasureTheory.volume T (2 * T) :=
    continuous_const.intervalIntegrable T (2 * T)
  have hscaledInt :
      IntervalIntegrable
        (fun t : ℝ =>
          2 * Complex.normSq
            (hardyLittlewoodThetaPolynomial N u t))
        MeasureTheory.volume T (2 * T) :=
    (continuous_const.mul hpolyContinuous).intervalIntegrable T (2 * T)
  have hrhsEq :
      (∫ t in T..2 * T,
          (2 * Complex.normSq
              (hardyLittlewoodThetaPolynomial N u t) +
            2 * hardyLittlewoodThetaTailConstant ^ 2)) =
        2 * hardyLittlewoodFiniteMeanSquare N u T T +
          2 * hardyLittlewoodThetaTailConstant ^ 2 * T := by
    rw [intervalIntegral.integral_add
      hscaledInt hconstInt]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    unfold hardyLittlewoodFiniteMeanSquare
    have hend : T + T = 2 * T := by ring
    rw [hend]
    ring
  calc
    (∫ t in T..2 * T,
      Complex.normSq
        (hardyLittlewoodThetaSeriesValue
          (hardyCriticalLinePoint (t + u)))) ≤
        ∫ t in T..2 * T,
          (2 * Complex.normSq
              (hardyLittlewoodThetaPolynomial N u t) +
            2 * hardyLittlewoodThetaTailConstant ^ 2) := hmono
    _ = 2 * hardyLittlewoodFiniteMeanSquare N u T T +
          2 * hardyLittlewoodThetaTailConstant ^ 2 * T := hrhsEq
    _ ≤ 2 *
          (T * (6 / Real.log 2 +
            16 * (hardyLittlewoodNearPairConstant +
              hardyLittlewoodFarPairConstant))) +
          2 * hardyLittlewoodThetaTailConstant ^ 2 * T := by
      gcongr
    _ = hardyLittlewoodThetaMeanSquareConstant * T := by
      unfold hardyLittlewoodThetaMeanSquareConstant
      ring

theorem hardyLittlewoodEtaWindowError_eq_thetaSeriesValue
    (H t : ℝ) :
    hardyLittlewoodEtaWindowError H t =
      -hardyLittlewoodEtaLowerConstant *
        (hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint (t + H)) -
          hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint t)).im := by
  unfold hardyLittlewoodEtaWindowError
  rw [hardyLittlewoodEtaPrimitive_eq_thetaSeriesValue,
    hardyLittlewoodEtaPrimitive_eq_thetaSeriesValue]
  simp only [Complex.sub_im]
  ring

theorem im_sub_sq_le_two_normSq
    (z w : ℂ) :
    (z - w).im ^ 2 ≤
      2 * (Complex.normSq z + Complex.normSq w) := by
  have hnorm : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
  have hsquare :
      ‖z - w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (z - w))
      (add_nonneg (norm_nonneg z) (norm_nonneg w))).2 hnorm
  have him :
      (z - w).im ^ 2 ≤ Complex.normSq (z - w) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (z - w).re]
  simp only [Complex.normSq_eq_norm_sq] at him ⊢
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

def hardyLittlewoodEtaWindowMomentConstant : ℝ :=
  4 * hardyLittlewoodEtaLowerConstant ^ 2 *
    hardyLittlewoodThetaMeanSquareConstant

theorem hardyLittlewoodEtaWindowMomentConstant_nonneg :
    0 ≤ hardyLittlewoodEtaWindowMomentConstant := by
  unfold hardyLittlewoodEtaWindowMomentConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (sq_nonneg hardyLittlewoodEtaLowerConstant))
    hardyLittlewoodThetaMeanSquareConstant_nonneg

theorem hardyLittlewoodEtaWindowError_sq_le_thetaSeriesValue
    (H t : ℝ) :
    |hardyLittlewoodEtaWindowError H t| ^ 2 ≤
      2 * hardyLittlewoodEtaLowerConstant ^ 2 *
        (Complex.normSq
            (hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint (t + H))) +
          Complex.normSq
            (hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint t))) := by
  rw [hardyLittlewoodEtaWindowError_eq_thetaSeriesValue,
    sq_abs]
  have him :=
    im_sub_sq_le_two_normSq
      (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint (t + H)))
      (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint t))
  have hscaled :=
    mul_le_mul_of_nonneg_left him
      (sq_nonneg hardyLittlewoodEtaLowerConstant)
  nlinarith

theorem integral_hardyLittlewoodEtaWindowError_sq_le
    {T H : ℝ} (hT : 1 ≤ T) (hH0 : 0 ≤ H) (hHT : H ≤ T) :
    (∫ t in T..2 * T,
      |hardyLittlewoodEtaWindowError H t| ^ 2) ≤
        hardyLittlewoodEtaWindowMomentConstant * T := by
  let psiH : ℝ → ℝ := fun t =>
    Complex.normSq
      (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint (t + H)))
  let psiZero : ℝ → ℝ := fun t =>
    Complex.normSq
      (hardyLittlewoodThetaSeriesValue
        (hardyCriticalLinePoint t))
  let scale : ℝ := 2 * hardyLittlewoodEtaLowerConstant ^ 2
  have hTtwo : T ≤ 2 * T := by linarith
  have hleftContinuous :
      Continuous
        (fun t : ℝ =>
          |hardyLittlewoodEtaWindowError H t| ^ 2) :=
    (continuous_hardyLittlewoodEtaWindowError H).abs.pow 2
  have hpsiHContinuous : Continuous psiH := by
    unfold psiH
    exact Complex.continuous_normSq.comp
      (continuous_hardyLittlewoodThetaSeriesValue_critical.comp
        (continuous_id.add continuous_const))
  have hpsiZeroContinuous : Continuous psiZero := by
    unfold psiZero
    exact Complex.continuous_normSq.comp
      continuous_hardyLittlewoodThetaSeriesValue_critical
  have hrightContinuous :
      Continuous
        (fun t : ℝ => scale * (psiH t + psiZero t)) :=
    continuous_const.mul
      (hpsiHContinuous.add hpsiZeroContinuous)
  have hmono :
      (∫ t in T..2 * T,
        |hardyLittlewoodEtaWindowError H t| ^ 2) ≤
        ∫ t in T..2 * T,
          scale * (psiH t + psiZero t) := by
    apply intervalIntegral.integral_mono_on hTtwo
      (hleftContinuous.intervalIntegrable T (2 * T))
      (hrightContinuous.intervalIntegrable T (2 * T))
    intro t _ht
    exact hardyLittlewoodEtaWindowError_sq_le_thetaSeriesValue H t
  have hpsiHInt :
      IntervalIntegrable psiH MeasureTheory.volume T (2 * T) :=
    hpsiHContinuous.intervalIntegrable T (2 * T)
  have hpsiZeroInt :
      IntervalIntegrable psiZero MeasureTheory.volume T (2 * T) :=
    hpsiZeroContinuous.intervalIntegrable T (2 * T)
  have hrightEq :
      (∫ t in T..2 * T,
        scale * (psiH t + psiZero t)) =
        scale *
          ((∫ t in T..2 * T, psiH t) +
            ∫ t in T..2 * T, psiZero t) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hpsiHInt hpsiZeroInt]
  have hHMean :
      (∫ t in T..2 * T, psiH t) ≤
        hardyLittlewoodThetaMeanSquareConstant * T := by
    exact integral_normSq_hardyLittlewoodThetaSeriesValue_shift_le
      hT hH0 hHT
  have hzeroMean :
      (∫ t in T..2 * T, psiZero t) ≤
        hardyLittlewoodThetaMeanSquareConstant * T := by
    simpa only [add_zero] using
      (integral_normSq_hardyLittlewoodThetaSeriesValue_shift_le
        hT (show (0 : ℝ) ≤ 0 by norm_num) (by linarith))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  calc
    (∫ t in T..2 * T,
      |hardyLittlewoodEtaWindowError H t| ^ 2) ≤
        ∫ t in T..2 * T,
          scale * (psiH t + psiZero t) := hmono
    _ = scale *
          ((∫ t in T..2 * T, psiH t) +
            ∫ t in T..2 * T, psiZero t) := hrightEq
    _ ≤ scale *
          (hardyLittlewoodThetaMeanSquareConstant * T +
            hardyLittlewoodThetaMeanSquareConstant * T) := by
      gcongr
    _ = hardyLittlewoodEtaWindowMomentConstant * T := by
      unfold scale hardyLittlewoodEtaWindowMomentConstant
      ring

theorem lintegral_hardyLittlewoodEtaWindowError_sq_le
    {T H : ℝ} (hT : 1 ≤ T) (hH0 : 0 ≤ H) (hHT : H ≤ T) :
    (∫⁻ t, ENNReal.ofReal
        (|hardyLittlewoodEtaWindowError H t| ^ 2)
      ∂(MeasureTheory.volume.restrict
        (Set.Icc T (2 * T)))) ≤
      ENNReal.ofReal
        (hardyLittlewoodEtaWindowMomentConstant * T) := by
  let f : ℝ → ℝ := fun t =>
    |hardyLittlewoodEtaWindowError H t| ^ 2
  have hTtwo : T ≤ 2 * T := by linarith
  have hfContinuous : Continuous f := by
    unfold f
    exact (continuous_hardyLittlewoodEtaWindowError H).abs.pow 2
  have hfIntegrable :
      MeasureTheory.Integrable f
        (MeasureTheory.volume.restrict
          (Set.Icc T (2 * T))) := by
    exact hfContinuous.integrableOn_Icc
  have hfNonneg :
      0 ≤ᵐ[
        MeasureTheory.volume.restrict (Set.Icc T (2 * T))] f :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hlintegral :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hfIntegrable hfNonneg
  have hintegralEq :
      (∫ t, f t
        ∂(MeasureTheory.volume.restrict
          (Set.Icc T (2 * T)))) =
        ∫ t in T..2 * T, f t := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    exact (intervalIntegral.integral_of_le hTtwo).symm
  have hordinary :
      (∫ t in T..2 * T, f t) ≤
        hardyLittlewoodEtaWindowMomentConstant * T := by
    exact integral_hardyLittlewoodEtaWindowError_sq_le
      hT hH0 hHT
  rw [← hlintegral, hintegralEq]
  exact ENNReal.ofReal_le_ofReal hordinary

/-- Aggregate certificate for the formalized Hardy--Littlewood Lemma 7 chain. -/
structure HardyLittlewoodEtaPrimitiveMeanSquareCertificate : Prop where
  thetaRemainder :
    ∀ (t : ℝ) (N : ℕ), max 2 ⌈|t|⌉₊ ≤ N →
      ‖hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
          hardyLittlewoodThetaPolynomial N 0 t‖ ≤
        8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-(1 / 2 : ℝ))
  primitiveIdentity :
    ∀ t : ℝ,
      hardyLittlewoodEtaPrimitive t =
        -(hardyLittlewoodThetaSeriesValue (hardyCriticalLinePoint t) -
            hardyLittlewoodThetaSeriesValue
              (hardyCriticalLinePoint 0)).im
  shiftedMeanSquare :
    ∀ {T u : ℝ}, 1 ≤ T → 0 ≤ u → u ≤ T →
      (∫ t in T..2 * T,
        Complex.normSq
          (hardyLittlewoodThetaSeriesValue
            (hardyCriticalLinePoint (t + u)))) ≤
        hardyLittlewoodThetaMeanSquareConstant * T
  windowMoment :
    ∀ {T H : ℝ}, 1 ≤ T → 0 ≤ H → H ≤ T →
      (∫⁻ t, ENNReal.ofReal
          (|hardyLittlewoodEtaWindowError H t| ^ 2)
        ∂(MeasureTheory.volume.restrict
          (Set.Icc T (2 * T)))) ≤
        ENNReal.ofReal
          (hardyLittlewoodEtaWindowMomentConstant * T)

theorem hardyLittlewoodEtaPrimitiveMeanSquare_endpoint :
    HardyLittlewoodEtaPrimitiveMeanSquareCertificate where
  thetaRemainder :=
    norm_hardyLittlewoodThetaSeriesValue_critical_sub_polynomial_le
  primitiveIdentity := hardyLittlewoodEtaPrimitive_eq_thetaSeriesValue
  shiftedMeanSquare :=
    integral_normSq_hardyLittlewoodThetaSeriesValue_shift_le
  windowMoment := lintegral_hardyLittlewoodEtaWindowError_sq_le

end

end LeanLab.Riemann
