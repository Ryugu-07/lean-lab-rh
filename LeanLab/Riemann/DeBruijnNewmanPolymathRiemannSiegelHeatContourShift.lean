import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelHeatExpansion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Complex Gaussian contour shifts for the Riemann--Siegel heat terms

This module proves the source identities `(rtn-def)` and `(RTN-def)` in the variance-two
Gaussian normalization used by the project.
-/

open Complex Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- Two parameters satisfy the source contour-shift domain condition when their imaginary parts
have the same strict sign. -/
def deBruijnNewmanRiemannSiegelSameOpenHalfPlane (s q : ℂ) : Prop :=
  (0 < s.im ∧ 0 < q.im) ∨ (s.im < 0 ∧ q.im < 0)

theorem deBruijnNewmanRiemannSiegelSameOpenHalfPlane.left_im_ne_zero
    {s q : ℂ} (h : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s q) : s.im ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt h.1
  · exact ne_of_lt h.1

theorem deBruijnNewmanRiemannSiegelSameOpenHalfPlane.right_im_ne_zero
    {s q : ℂ} (h : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s q) : q.im ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt h.2
  · exact ne_of_lt h.2

theorem deBruijnNewmanRiemannSiegel_min_abs_im_pos_of_sameOpenHalfPlane
    {s q : ℂ} (h : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s q) :
    0 < min |s.im| |q.im| := by
  rcases h with h | h
  · rw [abs_of_pos h.1, abs_of_pos h.2]
    exact lt_min h.1 h.2
  · rw [abs_of_neg h.1, abs_of_neg h.2]
    exact lt_min (neg_pos.mpr h.1) (neg_pos.mpr h.2)

theorem min_abs_le_abs_of_mem_uIcc_of_same_sign
    {a b x : ℝ} (h : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0))
    (hx : x ∈ Set.uIcc a b) :
    min |a| |b| ≤ |x| := by
  rcases h with hpos | hneg
  · have hminPos : 0 < min a b := lt_min hpos.1 hpos.2
    have hxLower : min a b ≤ x := hx.1
    have hxPos : 0 < x := hminPos.trans_le hxLower
    rw [abs_of_pos hpos.1, abs_of_pos hpos.2, abs_of_pos hxPos]
    exact hxLower
  · have hmaxNeg : max a b < 0 := max_lt hneg.1 hneg.2
    have hxUpper : x ≤ max a b := hx.2
    have hxNeg : x < 0 := hxUpper.trans_lt hmaxNeg
    rw [abs_of_neg hneg.1, abs_of_neg hneg.2, abs_of_neg hxNeg]
    rw [min_neg_neg]
    exact neg_le_neg hxUpper

theorem add_mul_mem_uIcc_add_mul
    {a b u c d : ℝ} (hc : 0 ≤ c) (hu : u ∈ Set.uIcc a b) :
    d + c * u ∈ Set.uIcc (d + c * a) (d + c * b) := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hu
    have hmap : d + c * a ≤ d + c * b := by
      simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hab hc) d
    rw [uIcc_of_le hmap]
    constructor
    · simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hu.1 hc) d
    · simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hu.2 hc) d
  · rw [uIcc_comm, uIcc_of_le hba] at hu
    have hmap : d + c * b ≤ d + c * a := by
      simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hba hc) d
    rw [uIcc_comm, uIcc_of_le hmap]
    constructor
    · simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hu.1 hc) d
    · simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hu.2 hc) d

theorem deBruijnNewmanRiemannSiegel_strip_min_abs_im_le
    {s q : ℂ} {a b u : ℝ} (ha : 0 ≤ a)
    (hu : u ∈ Set.uIcc 0 b)
    (him : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s q)
    (hqim : q.im = s.im + a * b) :
    min |s.im| |q.im| ≤ |s.im + a * u| := by
  apply min_abs_le_abs_of_mem_uIcc_of_same_sign
  · simpa [deBruijnNewmanRiemannSiegelSameOpenHalfPlane] using him
  · rw [hqim]
    simpa only [mul_zero, add_zero] using
      (add_mul_mem_uIcc_add_mul (d := s.im) ha hu)

/-- The raw Riemann--Siegel contour has one subgaussian bound that is uniform over a finite
horizontal strip. -/
theorem deBruijnNewmanRiemannSiegel_norm_rawIntegral_strip_le
    (N : ℕ) (a b : ℝ) (s : ℂ) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
        ‖deBruijnNewmanRiemannSiegelRawIntegral N
            (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
          C * Real.exp ((1 / 64 : ℝ) * x ^ 2 + d * |x|) := by
  let delta := deBruijnNewmanRiemannSiegelRawDelta a
  let A := |a|
  let S := |s.re|
  let M := |s.im| + A * |b|
  let L := deBruijnNewmanRiemannSiegelLineLogConstant N delta
  let B := Real.sqrt 2 * Real.pi * (N + 1 / 2)
  let D := delta * S + B
  let C0 := S * L + M * Real.pi + D ^ 2 / Real.pi
  let C := (1 / 2) * deBruijnNewmanRiemannSiegelContourGaussianMass * Real.exp C0
  let d := A * L
  refine ⟨C, d, ?_, ?_, ?_⟩
  · dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) deBruijnNewmanRiemannSiegelContourGaussianMass_nonneg)
      (Real.exp_nonneg _)
  · have hdeltaPos : 0 < delta := deBruijnNewmanRiemannSiegelRawDelta_pos a
    dsimp [d, A, L, deBruijnNewmanRiemannSiegelLineLogConstant]
    positivity
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hdelta : 0 < delta := deBruijnNewmanRiemannSiegelRawDelta_pos a
  have hA : 0 ≤ A := abs_nonneg a
  have hS : 0 ≤ S := abs_nonneg s.re
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := by
    dsimp [L, deBruijnNewmanRiemannSiegelLineLogConstant]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have huAbs : |u| ≤ |b| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hu
  have hre : |z.re| ≤ S + A * |x| := by
    dsimp [z]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    calc
      |s.re + a * x| ≤ |s.re| + |a * x| := abs_add_le _ _
      _ = S + A * |x| := by simp [S, A, abs_mul]
  have him : |z.im| ≤ M := by
    dsimp [z]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, add_zero, mul_one, mul_zero, sub_zero]
    calc
      |s.im + a * u| ≤ |s.im| + |a * u| := abs_add_le _ _
      _ = |s.im| + A * |u| := by simp [A, abs_mul]
      _ ≤ |s.im| + A * |b| := by
        have hmul := mul_le_mul_of_nonneg_left huAbs hA
        linarith
      _ = M := rfl
  have hrate :
      deBruijnNewmanRiemannSiegelLineRate N delta z ≤
        D + delta * A * |x| := by
    have hmul := mul_le_mul_of_nonneg_left hre hdelta.le
    calc
      deBruijnNewmanRiemannSiegelLineRate N delta z =
          delta * |z.re| + B := by rfl
      _ ≤ delta * (S + A * |x|) + B := by
        simpa [add_comm] using add_le_add_right hmul B
      _ = D + delta * A * |x| := by dsimp [D]; ring
  have hrateNonneg : 0 ≤ deBruijnNewmanRiemannSiegelLineRate N delta z :=
    deBruijnNewmanRiemannSiegel_nonneg_lineRate N hdelta z
  have hrightNonneg : 0 ≤ D + delta * A * |x| := by positivity
  have hrateSq :
      deBruijnNewmanRiemannSiegelLineRate N delta z ^ 2 ≤
        (D + delta * A * |x|) ^ 2 :=
    (sq_le_sq₀ hrateNonneg hrightNonneg).mpr hrate
  have hsplitSq :
      (D + delta * A * |x|) ^ 2 ≤
        2 * D ^ 2 + 2 * (delta * A) ^ 2 * x ^ 2 := by
    nlinarith [sq_nonneg (D - delta * A * |x|), sq_abs x]
  have hrateDiv :
      deBruijnNewmanRiemannSiegelLineRate N delta z ^ 2 /
          (2 * Real.pi) ≤
        D ^ 2 / Real.pi + (delta ^ 2 * A ^ 2 / Real.pi) * x ^ 2 := by
    have hpi : 0 < 2 * Real.pi := by positivity
    rw [div_le_iff₀ hpi]
    field_simp
    nlinarith [hrateSq, hsplitSq]
  have hdeltaSq : delta ^ 2 * A ^ 2 / Real.pi ≤ 1 / 64 := by
    simpa [delta, A] using
      deBruijnNewmanRiemannSiegelRawDelta_sq_mul_abs_sq_div_pi_le a
  have hquad :
      (delta ^ 2 * A ^ 2 / Real.pi) * x ^ 2 ≤
        (1 / 64 : ℝ) * x ^ 2 :=
    mul_le_mul_of_nonneg_right hdeltaSq (sq_nonneg x)
  have hconstant :
      deBruijnNewmanRiemannSiegelLineMajorantConstant N delta z ≤
        C0 + (1 / 64 : ℝ) * x ^ 2 + d * |x| := by
    unfold deBruijnNewmanRiemannSiegelLineMajorantConstant
    have hlinear := mul_le_mul_of_nonneg_right hre hL
    have himul := mul_le_mul_of_nonneg_right him Real.pi_pos.le
    dsimp [C0, d, S, A, M, L] at hlinear himul ⊢
    nlinarith
  calc
    ‖deBruijnNewmanRiemannSiegelRawIntegral N z‖ ≤
        ∫ v : ℝ, deBruijnNewmanRiemannSiegelLineMajorant N delta z v :=
      deBruijnNewmanRiemannSiegel_norm_rawIntegral_le N hdelta z
    _ = ((1 / 2) *
          Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta z)) *
        deBruijnNewmanRiemannSiegelContourGaussianMass :=
      deBruijnNewmanRiemannSiegel_integral_lineMajorant N delta z
    _ ≤ ((1 / 2) *
          Real.exp (C0 + (1 / 64 : ℝ) * x ^ 2 + d * |x|)) *
        deBruijnNewmanRiemannSiegelContourGaussianMass := by
      apply mul_le_mul_of_nonneg_right _
        deBruijnNewmanRiemannSiegelContourGaussianMass_nonneg
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hconstant) (by norm_num)
    _ = C * Real.exp ((1 / 64 : ℝ) * x ^ 2 + d * |x|) := by
      dsimp [C]
      rw [show C0 + (1 / 64 : ℝ) * x ^ 2 + d * |x| =
          C0 + ((1 / 64 : ℝ) * x ^ 2 + d * |x|) by ring,
        Real.exp_add]
      ring

/-- Gamma has one subgaussian horizontal bound over a finite strip whose imaginary part stays a
fixed positive distance from zero. -/
theorem deBruijnNewmanRiemannSiegel_norm_Gamma_strip_le
    (a b m : ℝ) {s : ℂ} (hm : 0 < m)
    (hstrip : ∀ u ∈ Set.uIcc 0 b,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im|) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
        ‖Complex.Gamma (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
          C * Real.exp ((1 / 128 : ℝ) * x ^ 2 + d * |x|) := by
  let delta := deBruijnNewmanRiemannSiegelGammaDelta a
  let A := |a|
  let S := |s.re + 1|
  let K := deBruijnNewmanRiemannSiegelGammaLogConstant delta
  let q := max 1 m⁻¹
  let Cpos := 2 * delta * S ^ 2 + K * S
  let dpos := K * A
  let Cneg := q * (2 + |s.re|)
  let dneg := q * A
  let C0 := max Cpos Cneg
  let d := max dpos dneg
  let C := Real.exp C0
  refine ⟨C, d, Real.exp_nonneg _, ?_, ?_⟩
  · dsimp [d, dpos, dneg, K, q, A]
    positivity
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hdelta : 0 < delta := deBruijnNewmanRiemannSiegelGammaDelta_pos a
  have hA : 0 ≤ A := abs_nonneg a
  have hS : 0 ≤ S := abs_nonneg (s.re + 1)
  have hK : 0 ≤ K := by
    dsimp [K, deBruijnNewmanRiemannSiegelGammaLogConstant]
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hCpos : 0 ≤ Cpos := by dsimp [Cpos]; positivity
  have hCneg : 0 ≤ Cneg := by dsimp [Cneg]; positivity
  have hCposMax : Cpos ≤ C0 := by dsimp [C0]; exact le_max_left _ _
  have hCnegMax : Cneg ≤ C0 := by dsimp [C0]; exact le_max_right _ _
  have hdpos : dpos ≤ d := by dsimp [d]; exact le_max_left _ _
  have hdneg : dneg ≤ d := by dsimp [d]; exact le_max_right _ _
  have himLower : m ≤ |z.im| := by
    have hbase := hstrip u hu
    dsimp [z]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, add_zero, mul_zero, mul_one, sub_zero] at hbase ⊢
    exact hbase
  have himz : z.im ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at himLower
    linarith
  have hqz : max 1 |z.im|⁻¹ ≤ q := by
    dsimp [q]
    apply max_le
    · exact le_max_left _ _
    · exact (inv_anti₀ hm himLower).trans (le_max_right _ _)
  by_cases hzre : 1 ≤ z.re
  · have hGamma :=
      (deBruijnNewmanRiemannSiegel_norm_Gamma_le_realGamma
        (lt_of_lt_of_le (by norm_num) hzre)).trans
        (deBruijnNewmanRiemannSiegel_realGamma_le_subquadratic hdelta hzre)
    have hzreFormula : z.re + 1 = (s.re + 1) + a * x := by
      dsimp [z]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      ring
    have hsquare : (z.re + 1) ^ 2 ≤ 2 * S ^ 2 + 2 * A ^ 2 * x ^ 2 := by
      rw [hzreFormula]
      have hab : (a * x) ^ 2 = A ^ 2 * x ^ 2 := by
        dsimp [A]
        rw [mul_pow, sq_abs]
      have hSsq : S ^ 2 = (s.re + 1) ^ 2 := by
        dsimp [S]
        rw [sq_abs]
      nlinarith [sq_nonneg ((s.re + 1) - a * x)]
    have hlinear : K * (z.re + 1) ≤ K * (S + A * |x|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [hzreFormula]
      calc
        (s.re + 1) + a * x ≤ |(s.re + 1) + a * x| := le_abs_self _
        _ ≤ |s.re + 1| + |a * x| := abs_add_le _ _
        _ = S + A * |x| := by simp [S, A, abs_mul]
    have hquad : 2 * delta * A ^ 2 * x ^ 2 ≤ (1 / 128 : ℝ) * x ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [delta, A] using deBruijnNewmanRiemannSiegelGammaDelta_quad a)
        (sq_nonneg x)
    have hexponent :
        delta * (z.re + 1) ^ 2 + K * (z.re + 1) ≤
          C0 + (1 / 128 : ℝ) * x ^ 2 + d * |x| := by
      have hsquareMul := mul_le_mul_of_nonneg_left hsquare hdelta.le
      have hdMul := mul_le_mul_of_nonneg_right hdpos (abs_nonneg x)
      dsimp [Cpos, dpos] at hCposMax hdpos ⊢
      nlinarith
    calc
      ‖Complex.Gamma z‖ ≤
          Real.exp (delta * (z.re + 1) ^ 2 + K * (z.re + 1)) := hGamma
      _ ≤ Real.exp (C0 + ((1 / 128 : ℝ) * x ^ 2 + d * |x|)) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ = C * Real.exp ((1 / 128 : ℝ) * x ^ 2 + d * |x|) := by
        dsimp [C]
        rw [Real.exp_add]
  · have hzre' : z.re < 1 := lt_of_not_ge hzre
    have hGamma :=
      deBruijnNewmanRiemannSiegel_norm_Gamma_le_exp_linear_of_re_lt_one himz hzre'
    have habs : |z.re| ≤ |s.re| + A * |x| := by
      dsimp [z]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      calc
        |s.re + a * x| ≤ |s.re| + |a * x| := abs_add_le _ _
        _ = |s.re| + A * |x| := by simp [A, abs_mul]
    have hqMul :
        max 1 |z.im|⁻¹ * (2 + |z.re|) ≤ q * (2 + |z.re|) :=
      mul_le_mul_of_nonneg_right hqz (by positivity)
    have hlinear : q * (2 + |z.re|) ≤ Cneg + dneg * |x| := by
      have hmul := mul_le_mul_of_nonneg_left habs hq
      dsimp [Cneg, dneg]
      dsimp [q, A] at hmul ⊢
      nlinarith
    have htarget :
        max 1 |z.im|⁻¹ * (2 + |z.re|) ≤
          C0 + (1 / 128 : ℝ) * x ^ 2 + d * |x| := by
      have hdMul := mul_le_mul_of_nonneg_right hdneg (abs_nonneg x)
      nlinarith [sq_nonneg x]
    calc
      ‖Complex.Gamma z‖ ≤
          Real.exp (max 1 |z.im|⁻¹ * (2 + |z.re|)) := hGamma
      _ ≤ Real.exp (C0 + ((1 / 128 : ℝ) * x ^ 2 + d * |x|)) := by
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ = C * Real.exp ((1 / 128 : ℝ) * x ^ 2 + d * |x|) := by
        dsimp [C]
        rw [Real.exp_add]

/-- The completed-zeta prefactor has one subgaussian bound over any finite strip that remains a
fixed positive distance from the real axis. -/
theorem deBruijnNewmanRiemannSiegel_norm_prefactor_strip_le
    (a b m : ℝ) {s : ℂ} (hm : 0 < m)
    (hstrip : ∀ u ∈ Set.uIcc 0 b,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im|) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
        ‖deBruijnNewmanRiemannSiegelPrefactor
            (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
          C * Real.exp ((1 / 128 : ℝ) * x ^ 2 + d * |x|) := by
  have hmHalf : 0 < m / 2 := by positivity
  have hstripHalf : ∀ u ∈ Set.uIcc 0 b,
      m / 2 ≤ |(s / 2 + (a / 2 * u : ℝ) * Complex.I).im| := by
    intro u hu
    have hbase := hstrip u hu
    have heq :
        (s / 2 + (a / 2 * u : ℝ) * Complex.I).im =
          (s + (a * u : ℝ) * Complex.I).im / 2 := by
      norm_num [Complex.div_im, Complex.add_im, Complex.mul_im]
      ring
    rw [heq, abs_div]
    norm_num
    have hbase' : m ≤ |s.im + a * u| := by
      simpa [Complex.add_im, Complex.mul_im] using hbase
    exact div_le_div_of_nonneg_right hbase' (by norm_num)
  obtain ⟨Cg, dg, hCg, hdg, hGamma⟩ :=
    deBruijnNewmanRiemannSiegel_norm_Gamma_strip_le
      (a / 2) b (m / 2) (s := s / 2) hmHalf hstripHalf
  let A := |a|
  let B := ‖s‖ + A + A * |b| + 1
  let P := |Real.log Real.pi| / 2
  let C := (1 / 8) * B ^ 2 * Real.exp (P * |s.re|) * Cg
  let d := 2 + P * A + dg
  refine ⟨C, d, ?_, ?_, ?_⟩
  · dsimp [C, B, P, A]
    positivity
  · dsimp [d, P, A]
    positivity
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, A]; positivity
  have hBone : 1 ≤ B := by
    dsimp [B]
    nlinarith [norm_nonneg s, abs_nonneg a, abs_nonneg b]
  have huAbs : |u| ≤ |b| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hu
  have hzNorm : ‖z‖ ≤ B * (1 + |x|) := by
    calc
      ‖z‖ ≤ ‖s‖ + ‖((a * x : ℝ) : ℂ)‖ +
          ‖((a * u : ℝ) : ℂ) * Complex.I‖ := by
        dsimp [z]
        exact norm_add₃_le
      _ = ‖s‖ + A * |x| + A * |u| := by simp [A, abs_mul]
      _ ≤ ‖s‖ + A * |x| + A * |b| := by
        have hmul := mul_le_mul_of_nonneg_left huAbs hA
        linarith
      _ ≤ B * (1 + |x|) := by
        have hAB : A ≤ B := by
          dsimp [B]
          nlinarith [norm_nonneg s, mul_nonneg hA (abs_nonneg b)]
        have hconst : ‖s‖ + A * |b| ≤ B := by
          dsimp [B]
          nlinarith [hA]
        have hlinear := mul_le_mul_of_nonneg_right hAB (abs_nonneg x)
        nlinarith
  have hzSubNorm : ‖z - 1‖ ≤ 2 * B * (1 + |x|) := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ B * (1 + |x|) + 1 := by
        norm_num only [norm_one]
        exact add_le_add hzNorm le_rfl
      _ ≤ 2 * B * (1 + |x|) := by
        nlinarith [abs_nonneg x]
  have honeExp : 1 + |x| ≤ Real.exp |x| := by
    simpa [add_comm] using Real.add_one_le_exp |x|
  have hpoly : ‖z * (z - 1) / 2‖ ≤ B ^ 2 * Real.exp (2 * |x|) := by
    rw [norm_div, norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      ‖z‖ * ‖z - 1‖ / 2 ≤
          (B * (1 + |x|)) * (2 * B * (1 + |x|)) / 2 := by
        gcongr
      _ = B ^ 2 * (1 + |x|) ^ 2 := by ring
      _ ≤ B ^ 2 * (Real.exp |x|) ^ 2 := by gcongr
      _ = B ^ 2 * Real.exp (2 * |x|) := by
        rw [show (2 : ℝ) * |x| = (2 : ℕ) * |x| by norm_num,
          Real.exp_nat_mul]
  have hzReAbs : |z.re| ≤ |s.re| + A * |x| := by
    dsimp [z]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    calc
      |s.re + a * x| ≤ |s.re| + |a * x| := abs_add_le _ _
      _ = |s.re| + A * |x| := by simp [A, abs_mul]
  have hpi :
      ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤
        Real.exp (P * |s.re| + P * A * |x|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Real.rpow_def_of_pos Real.pi_pos]
    apply Real.exp_le_exp.mpr
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hbase : Real.log Real.pi * (-z.re / 2) ≤ P * |z.re| := by
      have habsMul :
          Real.log Real.pi * (-z.re) ≤ |Real.log Real.pi| * |z.re| := by
        calc
          Real.log Real.pi * (-z.re) ≤ |Real.log Real.pi * (-z.re)| :=
            le_abs_self _
          _ = |Real.log Real.pi| * |z.re| := by rw [abs_mul, abs_neg]
      dsimp [P]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hzReAbs hP
    have hre : (-z / 2).re = -z.re / 2 := by
      norm_num [Complex.div_re]
    rw [hre]
    exact hbase.trans (by
      calc
        P * |z.re| ≤ P * (|s.re| + A * |x|) := hmul
        _ = P * |s.re| + P * A * |x| := by ring)
  have hGamma' := hGamma x u hu
  have hGammaAt :
      ‖Complex.Gamma (z / 2)‖ ≤
        Cg * Real.exp ((1 / 128 : ℝ) * x ^ 2 + dg * |x|) := by
    convert hGamma' using 1
    dsimp [z]
    congr 2
    push_cast
    ring
  unfold deBruijnNewmanRiemannSiegelPrefactor
  change ‖(1 / 8 : ℂ) * (z * (z - 1) / 2) *
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul]
  have hconst : ‖(1 / 8 : ℂ)‖ = (1 / 8 : ℝ) := by norm_num
  rw [hconst]
  calc
    (1 / 8 : ℝ) * ‖z * (z - 1) / 2‖ *
          ‖(Real.pi : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ ≤
        (1 / 8) * (B ^ 2 * Real.exp (2 * |x|)) *
          Real.exp (P * |s.re| + P * A * |x|) *
          (Cg * Real.exp ((1 / 128 : ℝ) * x ^ 2 + dg * |x|)) := by
      gcongr
    _ = C * Real.exp ((1 / 128 : ℝ) * x ^ 2 + d * |x|) := by
      dsimp [C, d]
      have hexp :
          Real.exp (2 * |x|) * Real.exp (P * |s.re| + P * A * |x|) *
              Real.exp ((1 / 128 : ℝ) * x ^ 2 + dg * |x|) =
            Real.exp (P * |s.re|) *
              Real.exp ((1 / 128 : ℝ) * x ^ 2 + (2 + P * A + dg) * |x|) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        (1 / 8) * (B ^ 2 * Real.exp (2 * |x|)) *
              Real.exp (P * |s.re| + P * A * |x|) *
              (Cg * Real.exp ((1 / 128 : ℝ) * x ^ 2 + dg * |x|)) =
            ((1 / 8) * B ^ 2 * Cg) *
              (Real.exp (2 * |x|) *
                Real.exp (P * |s.re| + P * A * |x|) *
                Real.exp ((1 / 128 : ℝ) * x ^ 2 + dg * |x|)) := by ring
        _ = ((1 / 8) * B ^ 2 * Cg) *
              (Real.exp (P * |s.re|) *
                Real.exp ((1 / 128 : ℝ) * x ^ 2 +
                  (2 + P * A + dg) * |x|)) := by rw [hexp]
        _ = (1 / 8) * B ^ 2 * Real.exp (P * |s.re|) * Cg *
              Real.exp ((1 / 128 : ℝ) * x ^ 2 +
                (2 + P * A + dg) * |x|) := by ring

/-- The actual source remainder has one uniform subgaussian bound on a pole-free finite strip. -/
theorem deBruijnNewmanRiemannSiegel_norm_R0N_strip_le
    (N : ℕ) (a b m : ℝ) {s : ℂ} (hm : 0 < m)
    (hstrip : ∀ u ∈ Set.uIcc 0 b,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im|) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
        ‖deBruijnNewmanRiemannSiegelR0N N
            (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
          C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by
  obtain ⟨Cp, dp, hCp, hdp, hp⟩ :=
    deBruijnNewmanRiemannSiegel_norm_prefactor_strip_le a b m hm hstrip
  obtain ⟨Cr, dr, hCr, hdr, hr⟩ :=
    deBruijnNewmanRiemannSiegel_norm_rawIntegral_strip_le N a b s
  refine ⟨Cp * Cr, dp + dr, mul_nonneg hCp hCr, add_nonneg hdp hdr, ?_⟩
  intro x u hu
  unfold deBruijnNewmanRiemannSiegelR0N
  rw [norm_mul]
  calc
    ‖deBruijnNewmanRiemannSiegelPrefactor
          (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ *
        ‖deBruijnNewmanRiemannSiegelRawIntegral N
          (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
      (Cp * Real.exp ((1 / 128 : ℝ) * x ^ 2 + dp * |x|)) *
        (Cr * Real.exp ((1 / 64 : ℝ) * x ^ 2 + dr * |x|)) := by
      exact mul_le_mul (hp x u hu) (hr x u hu) (norm_nonneg _) (by positivity)
    _ = (Cp * Cr) *
        Real.exp ((3 / 128 : ℝ) * x ^ 2 + (dp + dr) * |x|) := by
      rw [show Cp * Real.exp ((1 / 128 : ℝ) * x ^ 2 + dp * |x|) *
            (Cr * Real.exp ((1 / 64 : ℝ) * x ^ 2 + dr * |x|)) =
          (Cp * Cr) *
            (Real.exp ((1 / 128 : ℝ) * x ^ 2 + dp * |x|) *
              Real.exp ((1 / 64 : ℝ) * x ^ 2 + dr * |x|)) by ring,
        ← Real.exp_add]
      ring_nf

/-- Every positive-index source residue term inherits a uniform strip bound from two adjacent
source remainders. -/
theorem deBruijnNewmanRiemannSiegel_norm_R0Term_strip_le
    (N : ℕ) (a b m : ℝ) {s : ℂ} (hm : 0 < m)
    (hstrip : ∀ u ∈ Set.uIcc 0 b,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im|) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
        ‖deBruijnNewmanRiemannSiegelR0Term (N + 1)
            (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
          C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by
  obtain ⟨C0, d0, hC0, hd0, h0⟩ :=
    deBruijnNewmanRiemannSiegel_norm_R0N_strip_le N a b m hm hstrip
  obtain ⟨C1, d1, hC1, hd1, h1⟩ :=
    deBruijnNewmanRiemannSiegel_norm_R0N_strip_le (N + 1) a b m hm hstrip
  let d := max d0 d1
  refine ⟨C0 + C1, d, add_nonneg hC0 hC1, ?_, ?_⟩
  · dsimp [d]
    exact hd0.trans (le_max_left _ _)
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hd0d : d0 ≤ d := by dsimp [d]; exact le_max_left _ _
  have hd1d : d1 ≤ d := by dsimp [d]; exact le_max_right _ _
  have hExp0 :
      Real.exp ((3 / 128 : ℝ) * x ^ 2 + d0 * |x|) ≤
        Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hd0d (abs_nonneg x)
    linarith
  have hExp1 :
      Real.exp ((3 / 128 : ℝ) * x ^ 2 + d1 * |x|) ≤
        Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hd1d (abs_nonneg x)
    linarith
  have hterm :
      deBruijnNewmanRiemannSiegelR0Term (N + 1) z =
        deBruijnNewmanRiemannSiegelR0N N z -
          deBruijnNewmanRiemannSiegelR0N (N + 1) z := by
    rw [deBruijnNewmanRiemannSiegel_R0N_adjacent_decomposition N]
    ring
  rw [hterm]
  calc
    ‖deBruijnNewmanRiemannSiegelR0N N z -
        deBruijnNewmanRiemannSiegelR0N (N + 1) z‖ ≤
      ‖deBruijnNewmanRiemannSiegelR0N N z‖ +
        ‖deBruijnNewmanRiemannSiegelR0N (N + 1) z‖ := norm_sub_le _ _
    _ ≤ C0 * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d0 * |x|) +
        C1 * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d1 * |x|) :=
      add_le_add (h0 x u hu) (h1 x u hu)
    _ ≤ C0 * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) +
        C1 * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hExp0 hC0)
        (mul_le_mul_of_nonneg_left hExp1 hC1)
    _ = (C0 + C1) * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|) := by ring

/-- The entire Gaussian factor used to move the heat-evolution contour. -/
def deBruijnNewmanRiemannSiegelHeatContourKernel
    (a : ℝ) (s : ℂ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp (-w ^ 2 / 4) * F (s + (a : ℂ) * w)

/-- A `3/128` strip bound for `F` becomes a decaying `29/128` strip bound after multiplication by
the complex Gaussian. -/
theorem deBruijnNewmanRiemannSiegel_norm_heatContourKernel_le
    {a b C d : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|))
    (x u : ℝ) (hu : u ∈ Set.uIcc 0 b) :
    ‖deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      C * Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4) := by
  have huAbs : |u| ≤ |b| := by
    simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hu
  have huSq : u ^ 2 ≤ b ^ 2 := by
    rw [sq_le_sq]
    exact huAbs
  have harg :
      s + (a : ℂ) * ((x : ℂ) + (u : ℂ) * Complex.I) =
        s + (a * x : ℝ) + (a * u : ℝ) * Complex.I := by
    push_cast
    ring
  have hexpNorm :
      ‖Complex.exp (-((x : ℂ) + (u : ℂ) * Complex.I) ^ 2 / 4)‖ =
        Real.exp (-x ^ 2 / 4 + u ^ 2 / 4) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [Complex.div_re, Complex.mul_re, Complex.add_re, Complex.add_im, pow_two]
    ring
  rw [deBruijnNewmanRiemannSiegelHeatContourKernel, norm_mul, hexpNorm, harg]
  calc
    Real.exp (-x ^ 2 / 4 + u ^ 2 / 4) *
        ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
      Real.exp (-x ^ 2 / 4 + u ^ 2 / 4) *
        (C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) :=
      mul_le_mul_of_nonneg_left (hF x u hu) (Real.exp_nonneg _)
    _ = C * Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + u ^ 2 / 4) := by
      rw [show Real.exp (-x ^ 2 / 4 + u ^ 2 / 4) *
            (C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) =
          C * (Real.exp (-x ^ 2 / 4 + u ^ 2 / 4) *
            Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Each finite vertical side is controlled by the uniform strip bound times its length. -/
theorem deBruijnNewmanRiemannSiegel_norm_heatContourKernel_vertical_integral_le
    {a b C d : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|))
    (x : ℝ) :
    ‖∫ u : ℝ in 0..b,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (u : ℂ) * Complex.I)‖ ≤
      (C * Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4)) * |b| := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := b)
    (f := fun u : ℝ => deBruijnNewmanRiemannSiegelHeatContourKernel a s F
      ((x : ℂ) + (u : ℂ) * Complex.I))
    (C := C * Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4))
    (fun u hu => deBruijnNewmanRiemannSiegel_norm_heatContourKernel_le
      hC hF x u (Set.uIoc_subset_uIcc hu))
  simpa only [sub_zero] using hbound

theorem tendsto_deBruijnNewmanRiemannSiegel_heatContourSideMajorant
    (C d b : ℝ) :
    Tendsto (fun T : ℝ =>
      (C * Real.exp (-(29 / 128 : ℝ) * T ^ 2 + d * |T| + b ^ 2 / 4)) * |b|)
      atTop (𝓝 0) := by
  have hcoef : 0 < (29 / 128 : ℝ) := by norm_num
  have hlinear : Tendsto (fun T : ℝ => (29 / 128 : ℝ) * T - d) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_const_mul_atTop_of_pos hcoef).mpr tendsto_id)
  have hquad : Tendsto
      (fun T : ℝ => ((29 / 128 : ℝ) * T - d) * T) atTop atTop :=
    hlinear.atTop_mul_atTop₀ tendsto_id
  have hexponent : Tendsto
      (fun T : ℝ => -(((29 / 128 : ℝ) * T - d) * T) + b ^ 2 / 4)
      atTop atBot :=
    tendsto_atBot_add_const_right _ _ (tendsto_neg_atTop_atBot.comp hquad)
  have hexp : Tendsto
      (fun T : ℝ => Real.exp
        (-(((29 / 128 : ℝ) * T - d) * T) + b ^ 2 / 4)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hexponent
  have hmain := (hexp.const_mul C).mul_const |b|
  have hmain' : Tendsto
      (fun T : ℝ => C * Real.exp
        (-(((29 / 128 : ℝ) * T - d) * T) + b ^ 2 / 4) * |b|)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using hmain
  apply hmain'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [abs_of_nonneg hT]
  congr 3
  ring

theorem tendsto_deBruijnNewmanRiemannSiegel_heatContourKernel_rightIntegral
    {a b C d : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in 0..b,
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((T : ℂ) + (u : ℂ) * Complex.I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' ?_ ?_ (tendsto_deBruijnNewmanRiemannSiegel_heatContourSideMajorant C d b)
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall fun T =>
      deBruijnNewmanRiemannSiegel_norm_heatContourKernel_vertical_integral_le hC hF T

theorem tendsto_deBruijnNewmanRiemannSiegel_heatContourKernel_leftIntegral
    {a b C d : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in 0..b,
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((-T : ℂ) + (u : ℂ) * Complex.I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' ?_ ?_ (tendsto_deBruijnNewmanRiemannSiegel_heatContourSideMajorant C d b)
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall fun T => by
      simpa only [Complex.ofReal_neg, neg_sq, abs_neg] using
        deBruijnNewmanRiemannSiegel_norm_heatContourKernel_vertical_integral_le hC hF (-T)

/-- Pointwise holomorphy of `F` on a horizontal strip gives pointwise holomorphy of the
Gaussian-weighted contour kernel on that strip. -/
theorem differentiableAt_deBruijnNewmanRiemannSiegelHeatContourKernel
    {a b : ℝ} {s : ℂ} {F : ℂ → ℂ}
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      DifferentiableAt ℂ F
        (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I))
    {w : ℂ} (hw : w.im ∈ Set.uIcc 0 b) :
    DifferentiableAt ℂ
      (deBruijnNewmanRiemannSiegelHeatContourKernel a s F) w := by
  have harg :
      s + (a : ℂ) * w =
        s + (a * w.re : ℝ) + (a * w.im : ℝ) * Complex.I := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one]
  have hFat : DifferentiableAt ℂ F (s + (a : ℂ) * w) := by
    rw [harg]
    exact hF w.re w.im hw
  unfold deBruijnNewmanRiemannSiegelHeatContourKernel
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-z ^ 2 / 4)) w).mul
    (hFat.comp w (by fun_prop))

/-- The finite rectangular contour identity underlying the source heat-shift formulas. -/
theorem deBruijnNewmanRiemannSiegel_heatContourKernel_boundary_rect_eq_zero
    {a b : ℝ} {s : ℂ} {F : ℂ → ℂ}
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      DifferentiableAt ℂ F
        (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I))
    (T : ℝ) :
    (∫ x : ℝ in -T..T,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F x) -
      (∫ x : ℝ in -T..T,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (b : ℂ) * Complex.I)) +
      Complex.I * (∫ u : ℝ in 0..b,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((T : ℂ) + (u : ℂ) * Complex.I)) -
      Complex.I * (∫ u : ℝ in 0..b,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((-T : ℂ) + (u : ℂ) * Complex.I)) = 0 := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (deBruijnNewmanRiemannSiegelHeatContourKernel a s F)
    (-T : ℂ) ((T : ℂ) + (b : ℂ) * Complex.I) (by
      intro w hw
      have hu : w.im ∈ Set.uIcc 0 b := by
        have hu' : w ∈ Complex.im ⁻¹'
            Set.uIcc ((-T : ℂ).im) (((T : ℂ) + (b : ℂ) * Complex.I).im) := hw.2
        change w.im ∈ Set.uIcc ((-T : ℂ).im)
          (((T : ℂ) + (b : ℂ) * Complex.I).im) at hu'
        simpa using hu'
      exact (differentiableAt_deBruijnNewmanRiemannSiegelHeatContourKernel hF hu).differentiableWithinAt)
  simpa only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    Complex.ofReal_zero, neg_zero, Complex.add_re, Complex.mul_re, Complex.I_re,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, zero_add, Complex.ofReal_neg,
    smul_eq_mul] using hrect

/-- A real Gaussian still dominates the linear exponential loss in the uniform strip estimate. -/
theorem deBruijnNewmanRiemannSiegel_integrable_heatContourMajorant
    (d b : ℝ) :
    Integrable (fun x : ℝ =>
      Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4)) := by
  let k : ℝ := 29 / 128
  have hk : 0 < k := by norm_num [k]
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(k / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  let C : ℝ := Real.exp (d ^ 2 / (2 * k) + b ^ 2 / 4)
  refine Integrable.mono' (hgauss.const_mul C) (by fun_prop) ?_
  apply ae_of_all
  intro x
  have hsq : 0 ≤ (k * |x| - |d|) ^ 2 := sq_nonneg _
  have hlinear : d * |x| ≤ k / 2 * x ^ 2 + d ^ 2 / (2 * k) := by
    have hdenom : 0 < 2 * k := by positivity
    have hrewrite :
        k / 2 * x ^ 2 + d ^ 2 / (2 * k) =
          (k ^ 2 * x ^ 2 + d ^ 2) / (2 * k) := by
      field_simp
    rw [hrewrite, le_div_iff₀ hdenom]
    have hd : d * |x| ≤ |d| * |x| :=
      mul_le_mul_of_nonneg_right (le_abs_self d) (abs_nonneg x)
    nlinarith [hsq, sq_abs x, sq_abs d]
  have hexponent :
      -k * x ^ 2 + d * |x| + b ^ 2 / 4 ≤
        -(k / 2) * x ^ 2 + (d ^ 2 / (2 * k) + b ^ 2 / 4) := by
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-(29 / 128 : ℝ) * x ^ 2 + d * |x| + b ^ 2 / 4) ≤
        Real.exp (-(k / 2) * x ^ 2 +
          (d ^ 2 / (2 * k) + b ^ 2 / 4)) :=
      Real.exp_le_exp.mpr (by simpa [k] using hexponent)
    _ = C * Real.exp (-(k / 2) * x ^ 2) := by
      dsimp [C]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Every horizontal slice of the contour kernel is Bochner integrable. -/
theorem integrable_deBruijnNewmanRiemannSiegelHeatContourKernel_horizontal
    {a b C d u : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hhol : ∀ (x v : ℝ), v ∈ Set.uIcc 0 b →
      DifferentiableAt ℂ F
        (s + (a * x : ℝ) + (a * v : ℝ) * Complex.I))
    (hF : ∀ (x v : ℝ), v ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * v : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|))
    (hu : u ∈ Set.uIcc 0 b) :
    Integrable (fun x : ℝ =>
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  have hcontinuous : Continuous (fun x : ℝ =>
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((x : ℂ) + (u : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hu' : (((x : ℂ) + (u : ℂ) * Complex.I).im) ∈ Set.uIcc 0 b := by
      simpa using hu
    exact
      (differentiableAt_deBruijnNewmanRiemannSiegelHeatContourKernel hhol hu').continuousAt.comp_of_eq
        (by fun_prop) rfl
  refine Integrable.mono'
    ((deBruijnNewmanRiemannSiegel_integrable_heatContourMajorant d b).const_mul C)
    hcontinuous.aestronglyMeasurable ?_
  apply ae_of_all
  intro x
  exact deBruijnNewmanRiemannSiegel_norm_heatContourKernel_le hC hF x u hu

/-- Cauchy's theorem and the decaying side estimates move the full real contour to a parallel
horizontal line. -/
theorem deBruijnNewmanRiemannSiegel_integral_heatContourKernel_eq_im_shift
    {a b C d : ℝ} {s : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hhol : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      DifferentiableAt ℂ F
        (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I))
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 b →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) :
    (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F x) =
      ∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (b : ℂ) * Complex.I) := by
  let I₀ := fun T : ℝ => ∫ x : ℝ in -T..T,
    deBruijnNewmanRiemannSiegelHeatContourKernel a s F x
  let I_b := fun T : ℝ => ∫ x : ℝ in -T..T,
    deBruijnNewmanRiemannSiegelHeatContourKernel a s F
      ((x : ℂ) + (b : ℂ) * Complex.I)
  let I_right := fun T : ℝ => ∫ u : ℝ in 0..b,
    deBruijnNewmanRiemannSiegelHeatContourKernel a s F
      ((T : ℂ) + (u : ℂ) * Complex.I)
  let I_left := fun T : ℝ => ∫ u : ℝ in 0..b,
    deBruijnNewmanRiemannSiegelHeatContourKernel a s F
      ((-T : ℂ) + (u : ℂ) * Complex.I)
  have hfinite : ∀ T : ℝ,
      I₀ T = I_b T - Complex.I * I_right T + Complex.I * I_left T := by
    intro T
    have hboundary :=
      deBruijnNewmanRiemannSiegel_heatContourKernel_boundary_rect_eq_zero hhol T
    dsimp [I₀, I_b, I_right, I_left]
    linear_combination hboundary
  have hInt₀ : Integrable (fun x : ℝ =>
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F x) := by
    simpa using
      (integrable_deBruijnNewmanRiemannSiegelHeatContourKernel_horizontal
        hC hhol hF (u := 0) Set.left_mem_uIcc)
  have hIntb : Integrable (fun x : ℝ =>
      deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((x : ℂ) + (b : ℂ) * Complex.I)) :=
    integrable_deBruijnNewmanRiemannSiegelHeatContourKernel_horizontal
      hC hhol hF Set.right_mem_uIcc
  have hI₀ : Tendsto I₀ atTop
      (𝓝 (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F x)) := by
    simpa [I₀] using intervalIntegral_tendsto_integral hInt₀
      tendsto_neg_atTop_atBot tendsto_id
  have hIb : Tendsto I_b atTop
      (𝓝 (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (b : ℂ) * Complex.I))) := by
    simpa [I_b] using intervalIntegral_tendsto_integral hIntb
      tendsto_neg_atTop_atBot tendsto_id
  have hRight : Tendsto I_right atTop (𝓝 0) := by
    simpa [I_right] using
      tendsto_deBruijnNewmanRiemannSiegel_heatContourKernel_rightIntegral hC hF
  have hLeft : Tendsto I_left atTop (𝓝 0) := by
    simpa [I_left] using
      tendsto_deBruijnNewmanRiemannSiegel_heatContourKernel_leftIntegral hC hF
  have hShifted : Tendsto
      (fun T : ℝ => I_b T - Complex.I * I_right T + Complex.I * I_left T)
      atTop
      (𝓝 (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (b : ℂ) * Complex.I))) := by
    convert (hIb.sub (hRight.const_mul Complex.I)).add
      (hLeft.const_mul Complex.I) using 1 <;> simp
  have hI₀Shifted : Tendsto I₀ atTop
      (𝓝 (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (b : ℂ) * Complex.I))) :=
    hShifted.congr' (Filter.Eventually.of_forall fun T => (hfinite T).symm)
  exact tendsto_nhds_unique hI₀ hI₀Shifted

/-- Adding the real part of a complex displacement merely translates the real parameter. -/
theorem deBruijnNewmanRiemannSiegel_integral_heatContourKernel_im_shift_eq_shift
    (a : ℝ) (s : ℂ) (F : ℂ → ℂ) (q : ℂ) :
    (∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + (q.im : ℂ) * Complex.I)) =
      ∫ x : ℝ,
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F ((x : ℂ) + q) := by
  have htranslate := integral_add_right_eq_self
    (fun x : ℝ => deBruijnNewmanRiemannSiegelHeatContourKernel a s F
      ((x : ℂ) + (q.im : ℂ) * Complex.I)) q.re (μ := (volume : Measure ℝ))
  calc
    (∫ x : ℝ, deBruijnNewmanRiemannSiegelHeatContourKernel a s F
        ((x : ℂ) + (q.im : ℂ) * Complex.I)) =
        ∫ x : ℝ, deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          (((x + q.re : ℝ) : ℂ) + (q.im : ℂ) * Complex.I) := htranslate.symm
    _ = ∫ x : ℝ, deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          ((x : ℂ) + q) := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      have harg : (((x + q.re : ℝ) : ℂ) + (q.im : ℂ) * Complex.I) =
          (x : ℂ) + q := by
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_re, Complex.I_im, add_zero, zero_mul, mul_one]
      change deBruijnNewmanRiemannSiegelHeatContourKernel a s F
          (((x + q.re : ℝ) : ℂ) + (q.im : ℂ) * Complex.I) =
        deBruijnNewmanRiemannSiegelHeatContourKernel a s F ((x : ℂ) + q)
      rw [harg]

/-- The variance-two Gaussian integral is the normalized complex Gaussian-weighted Lebesgue
integral. -/
theorem integral_gaussianReal_two_eq_complexGaussian_weighted (G : ℝ → ℂ) :
    (∫ x : ℝ, G x ∂gaussianReal 0 2) =
      (((Real.sqrt (2 * Real.pi * 2))⁻¹ : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-((x : ℂ) ^ 2) / 4) * G x := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_ofNat]
  change (((((Real.sqrt (2 * Real.pi * 2))⁻¹ : ℝ) *
      Real.exp (-x ^ 2 / (2 * 2)) : ℝ) : ℂ) * G x) =
    (((Real.sqrt (2 * Real.pi * 2))⁻¹ : ℝ) : ℂ) *
      (Complex.exp (-((x : ℂ) ^ 2) / 4) * G x)
  push_cast
  have hexponent : -((x : ℂ) ^ 2) / (2 * 2) = -((x : ℂ) ^ 2) / 4 := by ring
  rw [hexponent]
  ring

/-- Generic variance-two Gaussian contour shift, with the completed-square factors displayed in
the normalization used by `(rtn-def)` and `(RTN-def)`. -/
theorem deBruijnNewmanRiemannSiegel_gaussian_contour_shift
    {a C d : ℝ} {s q : ℂ} {F : ℂ → ℂ} (hC : 0 ≤ C)
    (hhol : ∀ (x u : ℝ), u ∈ Set.uIcc 0 q.im →
      DifferentiableAt ℂ F
        (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I))
    (hF : ∀ (x u : ℝ), u ∈ Set.uIcc 0 q.im →
      ‖F (s + (a * x : ℝ) + (a * u : ℝ) * Complex.I)‖ ≤
        C * Real.exp ((3 / 128 : ℝ) * x ^ 2 + d * |x|)) :
    (∫ y : ℝ, F (s + (a * y : ℝ)) ∂gaussianReal 0 2) =
      Complex.exp (-q ^ 2 / 4) *
        ∫ y : ℝ,
          Complex.exp (-((y : ℂ) * q) / 2) *
            F (s + (a * y : ℝ) + (a : ℂ) * q)
          ∂gaussianReal 0 2 := by
  let G : ℝ → ℂ := fun y =>
    Complex.exp (-((y : ℂ) * q) / 2) *
      F (s + (a * y : ℝ) + (a : ℂ) * q)
  have hvertical :=
    deBruijnNewmanRiemannSiegel_integral_heatContourKernel_eq_im_shift hC hhol hF
  have htranslate :=
    deBruijnNewmanRiemannSiegel_integral_heatContourKernel_im_shift_eq_shift a s F q
  have hcontour :
      (∫ y : ℝ, deBruijnNewmanRiemannSiegelHeatContourKernel a s F y) =
        ∫ y : ℝ,
          deBruijnNewmanRiemannSiegelHeatContourKernel a s F ((y : ℂ) + q) :=
    hvertical.trans htranslate
  have hcomplete :
      (∫ y : ℝ,
          deBruijnNewmanRiemannSiegelHeatContourKernel a s F ((y : ℂ) + q)) =
        Complex.exp (-q ^ 2 / 4) *
          ∫ y : ℝ, Complex.exp (-((y : ℂ) ^ 2) / 4) * G y := by
    calc
      (∫ y : ℝ,
          deBruijnNewmanRiemannSiegelHeatContourKernel a s F ((y : ℂ) + q)) =
          ∫ y : ℝ, Complex.exp (-q ^ 2 / 4) *
            (Complex.exp (-((y : ℂ) ^ 2) / 4) * G y) := by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        have harg :
            s + (a : ℂ) * ((y : ℂ) + q) =
              s + (a * y : ℝ) + (a : ℂ) * q := by
          push_cast
          ring
        unfold deBruijnNewmanRiemannSiegelHeatContourKernel
        dsimp [G]
        rw [harg]
        rw [show Complex.exp (-q ^ 2 / 4) *
              (Complex.exp (-((y : ℂ) ^ 2) / 4) *
                (Complex.exp (-((y : ℂ) * q) / 2) *
                  F (s + (a * y : ℝ) + (a : ℂ) * q))) =
            (Complex.exp (-q ^ 2 / 4) * Complex.exp (-((y : ℂ) ^ 2) / 4) *
              Complex.exp (-((y : ℂ) * q) / 2)) *
                F (s + (a * y : ℝ) + (a : ℂ) * q) by ring]
        congr 1
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        ring
      _ = Complex.exp (-q ^ 2 / 4) *
          ∫ y : ℝ, Complex.exp (-((y : ℂ) ^ 2) / 4) * G y := by
        rw [MeasureTheory.integral_const_mul]
  have hleft := integral_gaussianReal_two_eq_complexGaussian_weighted
    (fun y : ℝ => F (s + (a * y : ℝ)))
  have hright := integral_gaussianReal_two_eq_complexGaussian_weighted G
  dsimp [G] at hright ⊢
  rw [hleft, hright]
  unfold deBruijnNewmanRiemannSiegelHeatContourKernel at hcontour
  have hweighted :
      (∫ y : ℝ, Complex.exp (-((y : ℂ) ^ 2) / 4) *
          F (s + (a * y : ℝ))) =
        Complex.exp (-q ^ 2 / 4) *
          ∫ y : ℝ, Complex.exp (-((y : ℂ) ^ 2) / 4) * G y :=
    by
      convert hcontour.trans hcomplete using 1 <;> push_cast <;> rfl
  rw [hweighted]
  ring

/-- The source remainder is holomorphic at every point off the real axis. -/
theorem differentiableAt_deBruijnNewmanRiemannSiegelR0N_of_im_ne_zero
    (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (deBruijnNewmanRiemannSiegelR0N N) z := by
  have hzmem : z ∈ deBruijnNewmanRiemannSiegelNonintegerDomain := by
    rw [mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff]
    intro n hn
    have him := congrArg Complex.im hn
    simp only [Complex.intCast_im] at him
    exact hz him
  exact ((differentiableOn_deBruijnNewmanRiemannSiegelR0N_nonintegerDomain N) z hzmem).differentiableAt
    (isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain.mem_nhds hzmem)

/-- Every positive-index source residue term is holomorphic off the real axis. -/
theorem differentiableAt_deBruijnNewmanRiemannSiegelR0Term_of_im_ne_zero
    (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (deBruijnNewmanRiemannSiegelR0Term (N + 1)) z := by
  have hterm : (fun w : ℂ => deBruijnNewmanRiemannSiegelR0Term (N + 1) w) =
      fun w : ℂ => deBruijnNewmanRiemannSiegelR0N N w -
        deBruijnNewmanRiemannSiegelR0N (N + 1) w := by
    funext w
    rw [deBruijnNewmanRiemannSiegel_R0N_adjacent_decomposition N]
    ring
  change DifferentiableAt ℂ
    (fun w : ℂ => deBruijnNewmanRiemannSiegelR0Term (N + 1) w) z
  rw [hterm]
  exact (differentiableAt_deBruijnNewmanRiemannSiegelR0N_of_im_ne_zero N hz).sub
    (differentiableAt_deBruijnNewmanRiemannSiegelR0N_of_im_ne_zero (N + 1) hz)

/-- `(RTN-def)` before substituting `a = sqrt(t)/2` and `q = sqrt(t) beta`. -/
theorem deBruijnNewmanRiemannSiegelR0N_gaussian_contour_shift
    (N : ℕ) {a : ℝ} (ha : 0 < a) {s q : ℂ}
    (hhalf : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (a : ℂ) * q)) :
    (∫ y : ℝ,
        deBruijnNewmanRiemannSiegelR0N N (s + (a * y : ℝ))
        ∂gaussianReal 0 2) =
      Complex.exp (-q ^ 2 / 4) *
        ∫ y : ℝ,
          Complex.exp (-((y : ℂ) * q) / 2) *
            deBruijnNewmanRiemannSiegelR0N N
              (s + (a * y : ℝ) + (a : ℂ) * q)
          ∂gaussianReal 0 2 := by
  let endpoint : ℂ := s + (a : ℂ) * q
  let m : ℝ := min |s.im| |endpoint.im|
  have hm : 0 < m := by
    dsimp [m, endpoint]
    exact deBruijnNewmanRiemannSiegel_min_abs_im_pos_of_sameOpenHalfPlane hhalf
  have hendpointIm : endpoint.im = s.im + a * q.im := by
    dsimp [endpoint]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hstrip : ∀ u ∈ Set.uIcc 0 q.im,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im| := by
    intro u hu
    have hbase := deBruijnNewmanRiemannSiegel_strip_min_abs_im_le
      ha.le hu hhalf hendpointIm
    dsimp [m, endpoint] at hbase ⊢
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, add_zero, mul_zero,
      zero_mul, mul_one, sub_zero] using hbase
  obtain ⟨C, d, hC, _hd, hbound⟩ :=
    deBruijnNewmanRiemannSiegel_norm_R0N_strip_le N a q.im m hm hstrip
  apply deBruijnNewmanRiemannSiegel_gaussian_contour_shift hC _ hbound
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hzLower : m ≤ |z.im| := by
    have hbase := hstrip u hu
    dsimp [z]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, add_zero, mul_zero,
      mul_one, sub_zero] at hbase ⊢
    exact hbase
  have hzim : z.im ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hzLower
    linarith
  exact differentiableAt_deBruijnNewmanRiemannSiegelR0N_of_im_ne_zero N hzim

/-- `(rtn-def)` before substituting `a = sqrt(t)/2` and `q = sqrt(t) alpha_n`. -/
theorem deBruijnNewmanRiemannSiegelR0Term_gaussian_contour_shift
    (N : ℕ) {a : ℝ} (ha : 0 < a) {s q : ℂ}
    (hhalf : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (a : ℂ) * q)) :
    (∫ y : ℝ,
        deBruijnNewmanRiemannSiegelR0Term (N + 1) (s + (a * y : ℝ))
        ∂gaussianReal 0 2) =
      Complex.exp (-q ^ 2 / 4) *
        ∫ y : ℝ,
          Complex.exp (-((y : ℂ) * q) / 2) *
            deBruijnNewmanRiemannSiegelR0Term (N + 1)
              (s + (a * y : ℝ) + (a : ℂ) * q)
          ∂gaussianReal 0 2 := by
  let endpoint : ℂ := s + (a : ℂ) * q
  let m : ℝ := min |s.im| |endpoint.im|
  have hm : 0 < m := by
    dsimp [m, endpoint]
    exact deBruijnNewmanRiemannSiegel_min_abs_im_pos_of_sameOpenHalfPlane hhalf
  have hendpointIm : endpoint.im = s.im + a * q.im := by
    dsimp [endpoint]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hstrip : ∀ u ∈ Set.uIcc 0 q.im,
      m ≤ |(s + (a * u : ℝ) * Complex.I).im| := by
    intro u hu
    have hbase := deBruijnNewmanRiemannSiegel_strip_min_abs_im_le
      ha.le hu hhalf hendpointIm
    dsimp [m, endpoint] at hbase ⊢
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, add_zero, mul_zero,
      zero_mul, mul_one, sub_zero] using hbase
  obtain ⟨C, d, hC, _hd, hbound⟩ :=
    deBruijnNewmanRiemannSiegel_norm_R0Term_strip_le N a q.im m hm hstrip
  apply deBruijnNewmanRiemannSiegel_gaussian_contour_shift hC _ hbound
  intro x u hu
  let z : ℂ := s + (a * x : ℝ) + (a * u : ℝ) * Complex.I
  have hzLower : m ≤ |z.im| := by
    have hbase := hstrip u hu
    dsimp [z]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, add_zero, mul_zero,
      mul_one, sub_zero] at hbase ⊢
    exact hbase
  have hzim : z.im ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hzLower
    linarith
  exact differentiableAt_deBruijnNewmanRiemannSiegelR0Term_of_im_ne_zero N hzim

theorem deBruijnNewmanRiemannSiegel_sqrt_scale_mul_sqrt
    {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t / 2) * Real.sqrt t = t / 2 := by
  calc
    (Real.sqrt t / 2) * Real.sqrt t =
        (Real.sqrt t * Real.sqrt t) / 2 := by ring
    _ = t / 2 := by rw [Real.mul_self_sqrt ht]

theorem deBruijnNewmanRiemannSiegel_sqrt_scale_complex_mul
    {t : ℝ} (ht : 0 ≤ t) (beta : ℂ) :
    (((Real.sqrt t / 2 : ℝ) : ℂ) *
        (((Real.sqrt t : ℝ) : ℂ) * beta)) =
      (((t / 2 : ℝ) : ℂ) * beta) := by
  rw [← mul_assoc, ← Complex.ofReal_mul,
    deBruijnNewmanRiemannSiegel_sqrt_scale_mul_sqrt ht]

theorem deBruijnNewmanRiemannSiegel_sqrt_mul_complex_sq
    {t : ℝ} (ht : 0 ≤ t) (beta : ℂ) :
    ((((Real.sqrt t : ℝ) : ℂ) * beta) ^ 2) =
      (t : ℂ) * beta ^ 2 := by
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt ht]

theorem deBruijnNewmanRiemannSiegel_heatShift_mul_complex
    (t y : ℝ) (beta : ℂ) :
    ((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * beta)) / 2 =
      deBruijnNewmanRiemannSiegelHeatShift t y * beta := by
  unfold deBruijnNewmanRiemannSiegelHeatShift
  push_cast
  ring

/-- Exact source identity `(RTN-def)` in the project's variance-two Gaussian normalization. -/
theorem deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift
    (N : ℕ) {t : ℝ} (ht : 0 < t) (beta s : ℂ)
    (hhalf : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (((t / 2 : ℝ) : ℂ) * beta))) :
    deBruijnNewmanRiemannSiegelHeatRemainder t N s =
      Complex.exp (-((t : ℂ) * beta ^ 2) / 4) *
        ∫ y : ℝ,
          Complex.exp (-(deBruijnNewmanRiemannSiegelHeatShift t y * beta)) *
            deBruijnNewmanRiemannSiegelR0N N
              (s + deBruijnNewmanRiemannSiegelHeatShift t y +
                (((t / 2 : ℝ) : ℂ) * beta))
          ∂gaussianReal 0 2 := by
  let a : ℝ := Real.sqrt t / 2
  let q : ℂ := ((Real.sqrt t : ℝ) : ℂ) * beta
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (Real.sqrt_pos.2 ht) (by norm_num)
  have haq : (a : ℂ) * q = (((t / 2 : ℝ) : ℂ) * beta) := by
    dsimp [a, q]
    exact deBruijnNewmanRiemannSiegel_sqrt_scale_complex_mul ht.le beta
  have hhalf' : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (a : ℂ) * q) := by
    rw [haq]
    exact hhalf
  have hsource :=
    deBruijnNewmanRiemannSiegelR0N_gaussian_contour_shift N ha hhalf'
  unfold deBruijnNewmanRiemannSiegelHeatRemainder
    deBruijnNewmanRiemannSiegelHeatEvolve
  dsimp [a, q] at hsource
  rw [deBruijnNewmanRiemannSiegel_sqrt_mul_complex_sq ht.le beta] at hsource
  rw [deBruijnNewmanRiemannSiegel_sqrt_scale_complex_mul ht.le beta] at hsource
  have hlinear (y : ℝ) :
      ((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * beta)) / 2 =
        (((Real.sqrt t / 2 * y : ℝ) : ℂ) * beta) := by
    simpa only [deBruijnNewmanRiemannSiegelHeatShift] using
      deBruijnNewmanRiemannSiegel_heatShift_mul_complex t y beta
  have hlinearNeg (y : ℝ) :
      -((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * beta)) / 2 =
        -(((Real.sqrt t / 2 * y : ℝ) : ℂ) * beta) := by
    calc
      -((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * beta)) / 2 =
          -(((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * beta)) / 2) := by ring
      _ = -(((Real.sqrt t / 2 * y : ℝ) : ℂ) * beta) :=
        congrArg Neg.neg (hlinear y)
  simp_rw [hlinearNeg] at hsource
  simpa only [deBruijnNewmanRiemannSiegelHeatShift] using hsource

/-- Exact source identity `(rtn-def)` for a positive index, written as `N + 1`. -/
theorem deBruijnNewmanRiemannSiegelHeatTerm_succ_contour_shift
    (N : ℕ) {t : ℝ} (ht : 0 < t) (alpha s : ℂ)
    (hhalf : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (((t / 2 : ℝ) : ℂ) * alpha))) :
    deBruijnNewmanRiemannSiegelHeatTerm t (N + 1) s =
      Complex.exp (-((t : ℂ) * alpha ^ 2) / 4) *
        ∫ y : ℝ,
          Complex.exp (-(deBruijnNewmanRiemannSiegelHeatShift t y * alpha)) *
            deBruijnNewmanRiemannSiegelR0Term (N + 1)
              (s + deBruijnNewmanRiemannSiegelHeatShift t y +
                (((t / 2 : ℝ) : ℂ) * alpha))
          ∂gaussianReal 0 2 := by
  let a : ℝ := Real.sqrt t / 2
  let q : ℂ := ((Real.sqrt t : ℝ) : ℂ) * alpha
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (Real.sqrt_pos.2 ht) (by norm_num)
  have haq : (a : ℂ) * q = (((t / 2 : ℝ) : ℂ) * alpha) := by
    dsimp [a, q]
    exact deBruijnNewmanRiemannSiegel_sqrt_scale_complex_mul ht.le alpha
  have hhalf' : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (a : ℂ) * q) := by
    rw [haq]
    exact hhalf
  have hsource :=
    deBruijnNewmanRiemannSiegelR0Term_gaussian_contour_shift N ha hhalf'
  unfold deBruijnNewmanRiemannSiegelHeatTerm
    deBruijnNewmanRiemannSiegelHeatEvolve
  dsimp [a, q] at hsource
  rw [deBruijnNewmanRiemannSiegel_sqrt_mul_complex_sq ht.le alpha] at hsource
  rw [deBruijnNewmanRiemannSiegel_sqrt_scale_complex_mul ht.le alpha] at hsource
  have hlinear (y : ℝ) :
      ((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * alpha)) / 2 =
        (((Real.sqrt t / 2 * y : ℝ) : ℂ) * alpha) := by
    simpa only [deBruijnNewmanRiemannSiegelHeatShift] using
      deBruijnNewmanRiemannSiegel_heatShift_mul_complex t y alpha
  have hlinearNeg (y : ℝ) :
      -((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * alpha)) / 2 =
        -(((Real.sqrt t / 2 * y : ℝ) : ℂ) * alpha) := by
    calc
      -((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * alpha)) / 2 =
          -(((y : ℂ) * (((Real.sqrt t : ℝ) : ℂ) * alpha)) / 2) := by ring
      _ = -(((Real.sqrt t / 2 * y : ℝ) : ℂ) * alpha) :=
        congrArg Neg.neg (hlinear y)
  simp_rw [hlinearNeg] at hsource
  simpa only [deBruijnNewmanRiemannSiegelHeatShift] using hsource

/-- Exact source identity `(rtn-def)` for an arbitrary index certified positive. -/
theorem deBruijnNewmanRiemannSiegelHeatTerm_contour_shift
    (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 < t) (alpha s : ℂ)
    (hhalf : deBruijnNewmanRiemannSiegelSameOpenHalfPlane s
      (s + (((t / 2 : ℝ) : ℂ) * alpha))) :
    deBruijnNewmanRiemannSiegelHeatTerm t n s =
      Complex.exp (-((t : ℂ) * alpha ^ 2) / 4) *
        ∫ y : ℝ,
          Complex.exp (-(deBruijnNewmanRiemannSiegelHeatShift t y * alpha)) *
            deBruijnNewmanRiemannSiegelR0Term n
              (s + deBruijnNewmanRiemannSiegelHeatShift t y +
                (((t / 2 : ℝ) : ℂ) * alpha))
          ∂gaussianReal 0 2 := by
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa only [hnEq] using
    deBruijnNewmanRiemannSiegelHeatTerm_succ_contour_shift (n - 1) ht alpha s hhalf
end

end LeanLab.Riemann
