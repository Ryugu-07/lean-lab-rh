import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelPhaseMargin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option linter.style.header false

/-!
# Fixed endpoint masses in the height-ten Riemann--Siegel contour

This module attacks the remaining endpoint-mass producer.  It keeps the principal-argument
decay, extracts quartic growth from the exact sine denominator, and uses separate compact and
tail envelopes at the two fixed endpoint heights.
-/

open Complex Filter Finset MeasureTheory Real Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

private theorem antitone_heightTenArctanTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1)) := by
  intro a b hab
  have hpow : x ^ (2 * b + 1) ≤ x ^ (2 * a + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden : (2 : ℝ) * a + 1 ≤ (2 : ℝ) * b + 1 := by
    exact_mod_cast (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  exact div_le_div₀ (pow_nonneg hx0 _) hpow (by positivity) hden

theorem heightTen_firstTwoTerms_le_arctan
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_heightTenArctanTerm x hx0 hx1.le
  have hlower := hanti.alternating_series_le_tendsto hsum 1
  norm_num [Finset.sum_range_succ] at hlower
  simpa [pow_three] using hlower

theorem arg_deBruijnNewmanRiemannSiegelLine_one_eq_neg_arctan
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 3 / 2) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) =
      -Real.arctan
        ((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
  let z := deBruijnNewmanRiemannSiegelLine 1 v
  have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hzRe : z.re = 3 / 2 - Real.sqrt 2 / 2 * v := by
    simp [z]
    norm_num
  have hzRePos : 0 < z.re := by
    rw [hzRe]
    nlinarith
  have htan :
      Real.tan (Complex.arg z) =
        -((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) := by
    rw [Complex.tan_arg]
    rw [hzRe]
    simp only [z, deBruijnNewmanRiemannSiegelLine_im]
    ring
  have hprincipal := Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩
  simpa only [Real.arctan_neg] using hprincipal.symm

theorem arg_deBruijnNewmanRiemannSiegelLine_one_neg_eq_arctan
    {x : ℝ} (hx : 0 ≤ x) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) =
      Real.arctan
        ((Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x)) := by
  let z := deBruijnNewmanRiemannSiegelLine 1 (-x)
  have hzRe : z.re = 3 / 2 + Real.sqrt 2 / 2 * x := by
    simp [z]
    norm_num
  have hzRePos : 0 < z.re := by
    rw [hzRe]
    positivity
  have htan :
      Real.tan (Complex.arg z) =
        (Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x) := by
    rw [Complex.tan_arg]
    rw [hzRe]
    simp only [z, deBruijnNewmanRiemannSiegelLine_im]
    ring
  exact (Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩).symm

theorem arg_deBruijnNewmanRiemannSiegelLine_one_neg_le_ratio
    {x : ℝ} (hx : 0 ≤ x) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) ≤
      (Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x) := by
  rw [arg_deBruijnNewmanRiemannSiegelLine_one_neg_eq_arctan hx]
  apply arctan_le_self_of_nonneg
  positivity

theorem arg_deBruijnNewmanRiemannSiegelLine_one_compact_le
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) ≤
      -(((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) -
        ((Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)) ^ 3 / 3) := by
  let r := (Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v)
  have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hden : 0 < 3 / 2 - Real.sqrt 2 / 2 * v := by nlinarith
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [div_lt_one hden]
    nlinarith
  rw [arg_deBruijnNewmanRiemannSiegelLine_one_eq_neg_arctan hv0 (by linarith)]
  change -Real.arctan r ≤ -(r - r ^ 3 / 3)
  exact neg_le_neg (heightTen_firstTwoTerms_le_arctan hr0 hr1)

theorem oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf :
    (111 / 50 : ℝ) ≤ Real.pi * (Real.sqrt 2 / 2) := by
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrt : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hq : (7071 / 10000 : ℝ) ≤ Real.sqrt 2 / 2 := by nlinarith
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  calc
    (111 / 50 : ℝ) ≤ (31415 / 10000) * (7071 / 10000) := by norm_num
    _ ≤ Real.pi * (Real.sqrt 2 / 2) :=
      mul_le_mul hpi hq (by norm_num) Real.pi_pos.le

theorem pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred :
    Real.pi * (Real.sqrt 2 / 2) ≤ (1111 / 500 : ℝ) := by
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrt : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hq : Real.sqrt 2 / 2 ≤ (14143 / 20000 : ℝ) := by nlinarith
  have hpi : Real.pi ≤ (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h.le
  calc
    Real.pi * (Real.sqrt 2 / 2) ≤
        (31416 / 10000) * (14143 / 20000) :=
      mul_le_mul hpi hq (by positivity) (by norm_num)
    _ ≤ (1111 / 500 : ℝ) := by norm_num

theorem one_div_sqrt_one_add_le_linear
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 51 / 50) :
    1 / Real.sqrt (1 + x) ≤ 1 - (29 / 100) * x := by
  have hbase : 0 < 1 + x := by linarith
  have hsqrt : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hbase
  have hrhs : 0 ≤ 1 - (29 / 100 : ℝ) * x := by nlinarith
  have hfactor :
      0 ≤ (42 / 100 : ℝ) - (4959 / 10000) * x + (841 / 10000) * x ^ 2 := by
    have hmonoFactor :
        0 ≤ (4959 / 10000 : ℝ) -
          (841 / 10000) * ((51 / 50 : ℝ) + x) := by
      nlinarith
    have hdiff :
        0 ≤ ((51 / 50 : ℝ) - x) *
          ((4959 / 10000 : ℝ) -
            (841 / 10000) * ((51 / 50 : ℝ) + x)) :=
      mul_nonneg (by linarith) hmonoFactor
    nlinarith
  have hpoly :
      1 ≤ (1 - (29 / 100 : ℝ) * x) ^ 2 * (1 + x) := by
    nlinarith [mul_nonneg hx0 hfactor]
  rw [div_le_iff₀ hsqrt]
  have hsqrtSq : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt hbase.le
  have hsq :
      1 ≤ ((1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x)) ^ 2 := by
    rw [mul_pow, hsqrtSq]
    exact hpoly
  have hproductNonneg :
      0 ≤ (((1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x)) - 1) *
        (((1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x)) + 1) := by
    nlinarith
  by_contra h
  have hlt : (1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x) < 1 :=
    lt_of_not_ge h
  have hplus :
      0 < (1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x) + 1 := by
    have := mul_nonneg hrhs hsqrt.le
    linarith
  have hproductNeg :
      (((1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x)) - 1) *
          (((1 - (29 / 100 : ℝ) * x) * Real.sqrt (1 + x)) + 1) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hplus
  exact (not_lt_of_ge hproductNonneg) hproductNeg

theorem two_thirds_mul_pow_four_le_sinh_sq_sub_sin_sq (u : ℝ) :
    (2 / 3 : ℝ) * u ^ 4 ≤ Real.sinh u ^ 2 - Real.sin u ^ 2 := by
  let x := 2 * u
  have hsum : HasSum
      (fun n : ℕ =>
        (1 + (-1 : ℝ) ^ n) * x ^ (2 * n) / (2 * n).factorial)
      (Real.cosh x + Real.cos x) := by
    convert (Real.hasSum_cosh x).add (Real.hasSum_cos x) using 1
    · ext n
      ring
  have hterm : ∀ n : ℕ,
      0 ≤ (1 + (-1 : ℝ) ^ n) * x ^ (2 * n) / (2 * n).factorial := by
    intro n
    have hsign : 0 ≤ 1 + (-1 : ℝ) ^ n := by
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;>
        simp [pow_add, pow_mul]
    have hpow : 0 ≤ x ^ (2 * n) := by
      rw [pow_mul]
      positivity
    exact div_nonneg (mul_nonneg hsign hpow) (by positivity)
  have hpartial := hsum.summable.sum_le_tsum (range 3) (fun n _ => hterm n)
  rw [hsum.tsum_eq] at hpartial
  have hidentity :
      Real.cosh (2 * u) + Real.cos (2 * u) - 2 =
        2 * (Real.sinh u ^ 2 - Real.sin u ^ 2) := by
    rw [Real.cosh_two_mul, Real.cos_two_mul]
    nlinarith [Real.cosh_sq u, Real.sin_sq_add_cos_sq u]
  dsimp [x] at hpartial
  norm_num [Finset.sum_range_succ] at hpartial
  nlinarith [hidentity]

theorem one_add_two_thirds_mul_pow_four_le_denominatorQuarterNormSq
    (N : ℕ) (v : ℝ) :
    1 + (2 / 3 : ℝ) *
        (Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im) ^ 4 ≤
      ‖deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanRiemannSiegelLine N v)‖ ^ 2 / 4 := by
  let u := Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im
  have hnormSq := normSq_sin_pi_mul_deBruijnNewmanRiemannSiegelLine N v
  have hquartic := two_thirds_mul_pow_four_le_sinh_sq_sub_sin_sq u
  have htrig := Real.sin_sq_add_cos_sq u
  rw [deBruijnNewmanRiemannSiegelDenominator_eq, norm_mul, norm_mul,
    Complex.norm_I, mul_one]
  norm_num
  ring_nf
  rw [← Complex.normSq_eq_norm_sq
    (Complex.sin ((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v)), hnormSq]
  dsimp [u] at hquartic htrig ⊢
  ring_nf at hquartic ⊢
  have him4 :
      (deBruijnNewmanRiemannSiegelLine N v).im ^ 4 * (2 / 3 : ℝ) =
        Real.sqrt 2 ^ 4 * v ^ 4 * (1 / 24 : ℝ) := by
    rw [deBruijnNewmanRiemannSiegelLine_im]
    ring
  have him4pi :
      Real.pi ^ 4 * (deBruijnNewmanRiemannSiegelLine N v).im ^ 4 * (2 / 3 : ℝ) =
        Real.pi ^ 4 * Real.sqrt 2 ^ 4 * v ^ 4 * (1 / 24 : ℝ) := by
    calc
      _ = Real.pi ^ 4 *
          ((deBruijnNewmanRiemannSiegelLine N v).im ^ 4 * (2 / 3 : ℝ)) := by ring
      _ = _ := by rw [him4]; ring
  rw [him4pi] at hquartic
  nlinarith

theorem heightTen_compact_quarticParameter_le
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    (2 / 3 : ℝ) *
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4 ≤ 51 / 50 := by
  have hcoeff := pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred
  have habs :
      |Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im| ≤
        (1111 / 1000 : ℝ) := by
    rw [deBruijnNewmanRiemannSiegelLine_im]
    calc
      |Real.pi * (-(Real.sqrt 2 / 2) * v)| =
          (Real.pi * (Real.sqrt 2 / 2)) * |v| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
          abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 / 2)]
        ring
      _ ≤ (1111 / 500 : ℝ) * (1 / 2) :=
        mul_le_mul hcoeff hv (abs_nonneg v) (by norm_num)
      _ = (1111 / 1000 : ℝ) := by norm_num
  have hpow :
      |Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im| ^ 4 ≤
        (1111 / 1000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 4
  have habspow :
      |Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im| ^ 4 =
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4 := by
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  rw [habspow] at hpow
  calc
    (2 / 3 : ℝ) *
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4 ≤
        (2 / 3) * (1111 / 1000 : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (51 / 50 : ℝ) := by norm_num

theorem one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    1 / ‖deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤
      (1 / 2 : ℝ) *
        (1 - (29 / 100) * (2 / 3) *
          (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4) := by
  let x := (2 / 3 : ℝ) *
    (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4
  let d := ‖deBruijnNewmanRiemannSiegelDenominator
    (deBruijnNewmanRiemannSiegelLine 1 v)‖
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 51 / 50 := heightTen_compact_quarticParameter_le hv
  have hquarter :=
    one_add_two_thirds_mul_pow_four_le_denominatorQuarterNormSq 1 v
  have hquarter' : 1 + x ≤ d ^ 2 / 4 := by
    simpa only [x, d] using hquarter
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdPos : 0 < d := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 (by linarith)
  have hsqrtLe : Real.sqrt (1 + x) ≤ d / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hrecip : 1 / (d / 2) ≤ 1 / Real.sqrt (1 + x) :=
    one_div_le_one_div_of_le hsqrtPos hsqrtLe
  have hlinear := one_div_sqrt_one_add_le_linear hx0 hx1
  have hfinal : 1 / d ≤ (1 / 2 : ℝ) * (1 - (29 / 100) * x) := by
    calc
      1 / d = (1 / 2 : ℝ) * (1 / (d / 2)) := by field_simp
      _ ≤ (1 / 2 : ℝ) * (1 / Real.sqrt (1 + x)) := by gcongr
      _ ≤ (1 / 2 : ℝ) * (1 - (29 / 100) * x) := by gcongr
  simpa [x, d, mul_assoc] using hfinal

theorem nine_le_exp_eleven_div_five :
    (9 : ℝ) ≤ Real.exp (11 / 5) := by
  have hseries := Real.sum_le_exp_of_nonneg
    (x := (11 / 5 : ℝ)) (by norm_num) 8
  have hpartial :
      (9 : ℝ) ≤ ∑ i ∈ range 8,
        (11 / 5 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hpartial.trans hseries

theorem one_div_two_mul_sinh_le_exp_tail
    {u : ℝ} (hu : 11 / 10 ≤ u) :
    1 / (2 * Real.sinh u) ≤ (9 / 8 : ℝ) * Real.exp (-u) := by
  have hu0 : 0 < u := by linarith
  have hexp2 : (9 : ℝ) ≤ Real.exp (2 * u) := by
    calc
      (9 : ℝ) ≤ Real.exp (11 / 5) := nine_le_exp_eleven_div_five
      _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have hinv : Real.exp (-2 * u) ≤ (1 / 9 : ℝ) := by
    rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9) hexp2)
  have hmul := mul_le_mul_of_nonneg_left hinv (Real.exp_pos u).le
  have hexpIdentity : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hexpIdentity] at hmul
  have hsinhLower : (8 / 9 : ℝ) * Real.exp u ≤ 2 * Real.sinh u := by
    rw [Real.sinh_eq]
    nlinarith
  have hleftPos : 0 < (8 / 9 : ℝ) * Real.exp u := by positivity
  have hrecip : 1 / (2 * Real.sinh u) ≤
      1 / ((8 / 9 : ℝ) * Real.exp u) :=
    one_div_le_one_div_of_le hleftPos hsinhLower
  calc
    1 / (2 * Real.sinh u) ≤ 1 / ((8 / 9 : ℝ) * Real.exp u) := hrecip
    _ = (9 / 8 : ℝ) * Real.exp (-u) := by
      rw [Real.exp_neg]
      field_simp

theorem one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    {v : ℝ} (hv : 1 / 2 ≤ |v|) :
    1 / ‖deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤
      (9 / 8 : ℝ) *
        Real.exp (-(Real.pi * (Real.sqrt 2 / 2) * |v|)) := by
  let u := Real.pi * (Real.sqrt 2 / 2) * |v|
  let d := ‖deBruijnNewmanRiemannSiegelDenominator
    (deBruijnNewmanRiemannSiegelLine 1 v)‖
  have hu : (11 / 10 : ℝ) ≤ u := by
    have hcoeff := oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf
    calc
      (11 / 10 : ℝ) ≤ (111 / 50 : ℝ) * (1 / 2) := by norm_num
      _ ≤ (Real.pi * (Real.sqrt 2 / 2)) * |v| :=
        mul_le_mul hcoeff hv (by norm_num) (by positivity)
      _ = u := by rfl
  have hu0 : 0 < u := by linarith
  have hsinhEq :
      |Real.sinh
        (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im)| =
        Real.sinh u := by
    rw [Real.abs_sinh]
    congr 1
    simp only [deBruijnNewmanRiemannSiegelLine_im, abs_mul, abs_neg,
      abs_of_pos Real.pi_pos, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 / 2)]
    dsimp [u]
    ring
  have hden := two_mul_abs_sinh_le_norm_deBruijnNewmanRiemannSiegelDenominator 1 v
  rw [hsinhEq] at hden
  have hleftPos : 0 < 2 * Real.sinh u := by
    exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hu0)
  have hrecip : 1 / d ≤ 1 / (2 * Real.sinh u) := by
    apply one_div_le_one_div_of_le hleftPos
    simpa only [d] using hden
  have htail := one_div_two_mul_sinh_le_exp_tail hu
  simpa only [u, d] using hrecip.trans htail

theorem rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_neg_le
    {x : ℝ} (hx : 0 ≤ x) :
    ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖ ^ (-(1 / 2 : ℝ)) ≤
      (1633 / 2000 : ℝ) := by
  let d := ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hdSq := norm_deBruijnNewmanRiemannSiegelLine_one_sq (-x)
  have hd0 : 0 ≤ d := norm_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hdLowerSq : (3 / 2 : ℝ) ^ 2 ≤ d ^ 2 := by
    dsimp [d] at hdSq ⊢
    nlinarith
  have hdLower : (3 / 2 : ℝ) ≤ d := by nlinarith
  have hdPos : 0 < d := by linarith
  have hsqrtLower :
      (2000 / 1633 : ℝ) ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by norm_num) hd0]
    nlinarith
  have hrecip : 1 / Real.sqrt d ≤ 1 / (2000 / 1633 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hsqrtLower
  have hrpow : d ^ (-(1 / 2 : ℝ)) = (Real.sqrt d)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hdPos.le]
  rw [show ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖ = d by rfl, hrpow]
  simpa [one_div] using hrecip

private theorem heightTen_positiveCompactFourthPowerCertificate
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    1 ≤ ((1633 / 2000 : ℝ) + (197 / 1000) * v) ^ 4 *
      (v ^ 2 - (3 * (14143 / 10000 : ℝ) / 2) * v + 9 / 4) := by
  have hx0 : 0 ≤ 2 * v := by positivity
  have hx1 : 0 ≤ 1 - 2 * v := by linarith
  have hbernstein :
      ((1633 / 2000 : ℝ) + (197 / 1000) * v) ^ 4 *
          (v ^ 2 - (3 * (14143 / 10000 : ℝ) / 2) * v + 9 / 4) - 1 =
        (1072004489 / 64000000000000 : ℝ) * (1 - 2 * v) ^ 6 +
        (2392493208516897 / 1280000000000000000 : ℝ) * 6 *
          (2 * v) * (1 - 2 * v) ^ 5 +
        (17128956591132331 / 9600000000000000000 : ℝ) * 15 *
          (2 * v) ^ 2 * (1 - 2 * v) ^ 4 +
        (117734999769953 / 160000000000000000 : ℝ) * 20 *
          (2 * v) ^ 3 * (1 - 2 * v) ^ 3 +
        (2204690264831 / 16000000000000000 : ℝ) * 15 *
          (2 * v) ^ 4 * (1 - 2 * v) ^ 2 +
        (1252911448979 / 640000000000000 : ℝ) * 6 *
          (2 * v) ^ 5 * (1 - 2 * v) +
        (566631889091 / 64000000000000 : ℝ) * (2 * v) ^ 6 := by
    ring
  have hnonneg :
      0 ≤ ((1633 / 2000 : ℝ) + (197 / 1000) * v) ^ 4 *
          (v ^ 2 - (3 * (14143 / 10000 : ℝ) / 2) * v + 9 / 4) - 1 := by
    rw [hbernstein]
    positivity
  linarith

theorem rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_compact_le
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) ≤
      (1633 / 2000 : ℝ) + (197 / 1000) * v := by
  let d := ‖deBruijnNewmanRiemannSiegelLine 1 v‖
  let L := (1633 / 2000 : ℝ) + (197 / 1000) * v
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtUpper : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hdSq := norm_deBruijnNewmanRiemannSiegelLine_one_sq v
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdPos : 0 < d := by
    have hone := one_le_norm_deBruijnNewmanRiemannSiegelLine_one v
    dsimp [d]
    linarith
  have hqLower :
      v ^ 2 - (3 * (14143 / 10000 : ℝ) / 2) * v + 9 / 4 ≤ d ^ 2 := by
    have hproduct :
        0 ≤ v * ((14143 / 10000 : ℝ) - Real.sqrt 2) :=
      mul_nonneg hv0 (sub_nonneg.mpr hsqrtUpper)
    dsimp [d] at hdSq ⊢
    nlinarith
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hcert := heightTen_positiveCompactFourthPowerCertificate hv0 hv1
  have hmain : 1 ≤ L ^ 4 * d ^ 2 := by
    calc
      1 ≤ L ^ 4 *
          (v ^ 2 - (3 * (14143 / 10000 : ℝ) / 2) * v + 9 / 4) := by
        simpa only [L] using hcert
      _ ≤ L ^ 4 * d ^ 2 := mul_le_mul_of_nonneg_left hqLower (by positivity)
  have hsqrtDPos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdPos
  have hsqrtDSq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd0
  have hsqrtDFour : Real.sqrt d ^ 4 = d ^ 2 := by
    calc
      Real.sqrt d ^ 4 = (Real.sqrt d ^ 2) ^ 2 := by ring
      _ = d ^ 2 := by rw [hsqrtDSq]
  have hyFour : 1 ≤ (L * Real.sqrt d) ^ 4 := by
    rw [mul_pow, hsqrtDFour]
    exact hmain
  have hy : 1 ≤ L * Real.sqrt d :=
    (one_le_pow_iff_of_nonneg (mul_nonneg hL0 hsqrtDPos.le)
      (by norm_num : (4 : ℕ) ≠ 0)).mp hyFour
  have hrpow : d ^ (-(1 / 2 : ℝ)) = (Real.sqrt d)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hdPos.le]
  rw [show ‖deBruijnNewmanRiemannSiegelLine 1 v‖ = d by rfl, hrpow]
  have hdiv : 1 / Real.sqrt d ≤ L := (div_le_iff₀ hsqrtDPos).2 hy
  simpa only [one_div, L] using hdiv

private theorem heightTen_positiveCompactClearedBracket_nonneg
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    0 ≤ Real.sqrt 2 *
        (4 + (9 / 2) * v + (4 / 3) * v ^ 2 + (1 / 3) * v ^ 3) -
      ((9 / 2) + 8 * v + 3 * v ^ 2) := by
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hx0 : 0 ≤ 2 * v := by positivity
  have hx1 : 0 ≤ 1 - 2 * v := by linarith
  have hrationalIdentity :
      (7071 / 5000 : ℝ) *
          (4 + (9 / 2) * v + (4 / 3) * v ^ 2 + (1 / 3) * v ^ 3) -
          ((9 / 2) + 8 * v + 3 * v ^ 2) =
        (723 / 625 : ℝ) * (1 - 2 * v) ^ 3 +
        (53047 / 60000 : ℝ) * 3 * (2 * v) * (1 - 2 * v) ^ 2 +
        (15557 / 30000 : ℝ) * 3 * (2 * v) ^ 2 * (1 - 2 * v) +
        (4763 / 40000 : ℝ) * (2 * v) ^ 3 := by
    ring
  have hrational :
      0 ≤ (7071 / 5000 : ℝ) *
          (4 + (9 / 2) * v + (4 / 3) * v ^ 2 + (1 / 3) * v ^ 3) -
          ((9 / 2) + 8 * v + 3 * v ^ 2) := by
    rw [hrationalIdentity]
    positivity
  have hseries :
      0 ≤ 4 + (9 / 2) * v + (4 / 3) * v ^ 2 + (1 / 3) * v ^ 3 := by
    positivity
  have hdelta := mul_nonneg (sub_nonneg.mpr hsqrtLower) hseries
  nlinarith

theorem heightTen_positiveCompactAnglePolynomial_le
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    (Real.sqrt 2 / 3) * v + (2 / 9) * v ^ 2 + (1 / 18) * v ^ 3 ≤
      (Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v) -
        ((Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v)) ^ 3 / 3 := by
  let t := Real.sqrt 2
  let d := 3 - t * v
  let r := (t * v) / d
  let P := (t / 3) * v + (2 / 9) * v ^ 2 + (1 / 18) * v ^ 3
  let B := t *
      (4 + (9 / 2) * v + (4 / 3) * v ^ 2 + (1 / 3) * v ^ 3) -
    ((9 / 2) + 8 * v + 3 * v ^ 2)
  let E := 3 * t * v * d ^ 2 - t ^ 3 * v ^ 3 - 3 * P * d ^ 3
  have htSq : t ^ 2 = (2 : ℝ) := by dsimp [t]; norm_num
  have htUpper : t < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hdPos : 0 < d := by dsimp [d]; nlinarith
  have hB : 0 ≤ B := by
    simpa only [B, t] using
      heightTen_positiveCompactClearedBracket_nonneg hv0 hv1
  have hmod :
      E - v ^ 3 * B =
        (t ^ 2 - 2) *
          (9 * v ^ 2 - 4 * v ^ 4 - (3 / 2) * v ^ 5 -
            7 * t * v ^ 3 + (2 / 3) * t * v ^ 5 +
            (1 / 6) * t * v ^ 6 + t ^ 2 * v ^ 4) := by
    dsimp [E, B, P, d]
    ring
  have hEeq : E = v ^ 3 * B := by
    rw [htSq, sub_self, zero_mul] at hmod
    linarith
  have hE : 0 ≤ E := by
    rw [hEeq]
    positivity
  have hcleared : 3 * d ^ 3 * (r - r ^ 3 / 3 - P) = E := by
    dsimp [E, r]
    field_simp [hdPos.ne']
  have hproduct : 0 ≤ 3 * d ^ 3 * (r - r ^ 3 / 3 - P) := by
    rw [hcleared]
    exact hE
  have hdiff : 0 ≤ r - r ^ 3 / 3 - P :=
    nonneg_of_mul_nonneg_right hproduct (mul_pos (by norm_num) (pow_pos hdPos 3))
  have htarget : P ≤ r - r ^ 3 / 3 := by linarith
  simpa only [t, d, r, P] using htarget

theorem arg_deBruijnNewmanRiemannSiegelLine_one_compact_le_polynomial
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) ≤
      -((Real.sqrt 2 / 3) * v + (2 / 9) * v ^ 2 + (1 / 18) * v ^ 3) := by
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_compact_le hv0 hv1
  have hpoly := heightTen_positiveCompactAnglePolynomial_le hv0 hv1
  have hratio :
      (Real.sqrt 2 / 2 * v) / (3 / 2 - Real.sqrt 2 / 2 * v) =
        (Real.sqrt 2 * v) / (3 - Real.sqrt 2 * v) := by
    have hden : 3 - Real.sqrt 2 * v ≠ 0 := by
      have hsqrt := Real.sqrt_two_lt_three_halves
      nlinarith
    field_simp [hden]
  rw [hratio] at harg
  exact harg.trans (neg_le_neg hpoly)

theorem heightTen_positiveCompactTotalExponent_le
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    (13 / 2 : ℝ) * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
        (-Real.pi * v ^ 2 +
          Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v) ≤
      (361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 - (13 / 36) * v ^ 3 := by
  have harg :=
    arg_deBruijnNewmanRiemannSiegelLine_one_compact_le_polynomial hv0 hv1
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 13 / 2)
  have hpiSqrtUpper :
      Real.pi * Real.sqrt 2 ≤ (1111 / 250 : ℝ) := by
    calc
      Real.pi * Real.sqrt 2 =
          2 * (Real.pi * (Real.sqrt 2 / 2)) := by ring
      _ ≤ 2 * (1111 / 500 : ℝ) := by
        gcongr
        exact pi_mul_sqrtTwoHalf_le_oneThousandOneHundredEleven_div_fiveHundred
      _ = (1111 / 250 : ℝ) := by norm_num
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlinear :
      (3 / 2 : ℝ) * (Real.sqrt 2 * Real.pi) -
          (13 / 6) * Real.sqrt 2 ≤ 361 / 100 := by
    nlinarith
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hquadratic :
      -Real.pi - (13 / 9 : ℝ) ≤ -(2063 / 450 : ℝ) := by
    nlinarith
  have hlinearMul := mul_le_mul_of_nonneg_right hlinear hv0
  have hquadraticMul := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg v)
  nlinarith

theorem heightTen_negativeCompactAnglePolynomial_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) ≤
      (Real.sqrt 2 / 3) * x - (1 / 6) * x ^ 2 := by
  let t := Real.sqrt 2
  let d := 3 + t * x
  let P := (t / 3) * x - (1 / 6) * x ^ 2
  have htSq : t ^ 2 = (2 : ℝ) := by dsimp [t]; norm_num
  have htUpper : t < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hdPos : 0 < d := by dsimp [d]; positivity
  have htx : t * x ≤ 1 := by
    have := mul_le_mul_of_nonneg_right htUpper.le hx0
    nlinarith
  have hfactor : 0 ≤ x ^ 2 * (1 - t * x) :=
    mul_nonneg (sq_nonneg x) (sub_nonneg.mpr htx)
  have hmod :
      P * d - t * x - (1 / 6) * x ^ 2 * (1 - t * x) =
        (t ^ 2 - 2) * x ^ 2 / 3 := by
    dsimp [P, d]
    ring
  have hcleared : t * x ≤ P * d := by
    rw [htSq, sub_self, zero_mul, zero_div] at hmod
    nlinarith
  have hratio : t * x / d ≤ P := by
    rw [div_le_iff₀ hdPos]
    exact hcleared
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_neg_le_ratio hx0
  have hhalfRatio :
      (Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x) =
        Real.sqrt 2 * x / (3 + Real.sqrt 2 * x) := by
    field_simp [hdPos.ne']
  rw [hhalfRatio] at harg
  exact harg.trans (by simpa only [t, d, P] using hratio)

theorem heightTen_negativeCompactTotalExponent_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    10 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * x ^ 2 -
          Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x) ≤
      -(39 / 20 : ℝ) * x - (28849 / 6000) * x ^ 2 := by
  have harg := heightTen_negativeCompactAnglePolynomial_le hx0 hx1
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 10)
  have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  have hsqrtLower : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hgapLower :
      (16547 / 12000 : ℝ) ≤ (3 / 2) * Real.pi - 10 / 3 := by
    nlinarith
  have hlinearProduct :
      (39 / 20 : ℝ) ≤ Real.sqrt 2 * ((3 / 2) * Real.pi - 10 / 3) := by
    calc
      (39 / 20 : ℝ) ≤ (7071 / 5000 : ℝ) * (16547 / 12000) := by norm_num
      _ ≤ Real.sqrt 2 * ((3 / 2) * Real.pi - 10 / 3) :=
        mul_le_mul hsqrtLower hgapLower (by norm_num) (by positivity)
  have hquadratic :
      (28849 / 6000 : ℝ) ≤ Real.pi + 5 / 3 := by
    nlinarith
  have hlinearMul := mul_le_mul_of_nonneg_right hlinearProduct hx0
  have hquadraticMul := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg x)
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization
    (y v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint y) v‖ =
      ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
        Real.exp
          (y * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v) +
            (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v)) *
        (1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 v)‖) := by
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
    deBruijnNewmanRiemannSiegelKernel deBruijnNewmanRiemannSiegelNumerator
  rw [norm_mul, norm_div, norm_mul,
    norm_cpow_neg_heightTenRiemannSiegelCriticalPoint,
    norm_exp_deBruijnNewmanRiemannSiegel_gaussian,
    norm_deBruijnNewmanRiemannSiegelDirection]
  simp only [Nat.cast_one, mul_one, div_eq_mul_inv]
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp (y * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v)) *
          Real.exp
            (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v) *
          ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 v)‖⁻¹ =
        ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) *
          (Real.exp (y * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 v)) *
            Real.exp
              (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * v)) *
          ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 v)‖⁻¹ := by ring
    _ = _ := by
      rw [← Real.exp_add]
      norm_num [one_div]

theorem norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ ≤
      ((1633 / 2000 : ℝ) + (197 / 1000) * v) *
        Real.exp
          ((361 / 100 : ℝ) * v - (2063 / 450) * v ^ 2 -
            (13 / 36) * v ^ 3) *
        ((1 / 2 : ℝ) *
          (1 - (29 / 100) * (2 / 3) *
            (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4)) := by
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hvAbs : |v| ≤ 1 / 2 := by rw [abs_of_nonneg hv0]; exact hv1
  have hrpow :=
    rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_compact_le hv0 hv1
  have hexponent := heightTen_positiveCompactTotalExponent_le hv0 hv1
  have hden :=
    one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le hvAbs
  exact mul_le_mul
    (mul_le_mul hrpow (Real.exp_le_exp.mpr hexponent)
      (Real.exp_pos _).le (by positivity))
    hden (one_div_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (by positivity) (Real.exp_pos _).le)

theorem norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 10) (-x)‖ ≤
      (1633 / 2000 : ℝ) *
        Real.exp (-(39 / 20 : ℝ) * x - (28849 / 6000) * x ^ 2) *
        ((1 / 2 : ℝ) *
          (1 - (29 / 100) * (2 / 3) *
            (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 (-x)).im) ^ 4)) := by
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hxAbs : |-x| ≤ 1 / 2 := by simpa [abs_of_nonneg hx0] using hx1
  have hrpow :=
    rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_neg_le hx0
  have hexponent := heightTen_negativeCompactTotalExponent_le hx0 hx1
  have hexponent' :
      10 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
          (-Real.pi * (-x) ^ 2 +
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x)) ≤
        -(39 / 20 : ℝ) * x - (28849 / 6000) * x ^ 2 := by
    convert hexponent using 1
    all_goals ring
  have hden :=
    one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le hxAbs
  exact mul_le_mul
    (mul_le_mul hrpow (Real.exp_le_exp.mpr hexponent')
      (Real.exp_pos _).le (by norm_num))
    hden (one_div_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (by norm_num) (Real.exp_pos _).le)

end

end LeanLab.Riemann
