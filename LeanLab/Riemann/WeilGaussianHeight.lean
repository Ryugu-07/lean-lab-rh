import LeanLab.Riemann.WeilZeroCutoff
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A symmetric Gaussian height limit for Riemann's xi function

This module starts the passage from the finite-height xi zero cutoff to a global formula for the
fixed entire weight `exp (a * (s - 1 / 2)^2)`. No generic test-class limit, positivity statement,
or Riemann hypothesis is asserted.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators Interval Topology

namespace LeanLab.Riemann

noncomputable section

/-- The critical-line-centered entire Gaussian used for the fixed-test height limit. -/
def riemannXiGaussianWeight (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * (z - 1 / 2) ^ 2)

theorem differentiable_riemannXiGaussianWeight (a : ℝ) :
    Differentiable ℂ (riemannXiGaussianWeight a) := by
  unfold riemannXiGaussianWeight
  fun_prop

/-- The Gaussian is invariant under the reflection in xi's functional equation. -/
theorem riemannXiGaussianWeight_one_sub (a : ℝ) (z : ℂ) :
    riemannXiGaussianWeight a (1 - z) = riemannXiGaussianWeight a z := by
  unfold riemannXiGaussianWeight
  congr 1
  ring

/-- Exact Gaussian decay: the imaginary direction contributes `exp (-a * Im(z)^2)`. -/
theorem norm_riemannXiGaussianWeight (a : ℝ) (z : ℂ) :
    ‖riemannXiGaussianWeight a z‖ =
      Real.exp (a * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) := by
  have hsquare : ((z - 1 / 2) ^ 2).re =
      (z.re - 1 / 2) ^ 2 - z.im ^ 2 := by
    rw [pow_two, mul_re]
    simp
    ring
  rw [riemannXiGaussianWeight, Complex.norm_exp]
  congr 1
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hsquare]

/-- Differentiating the xi functional equation makes its logarithmic derivative odd under
`s |-> 1-s`. The identity remains valid at zeros under Lean's totalized division convention. -/
theorem logDeriv_riemannXi_one_sub (z : ℂ) :
    logDeriv riemannXi (1 - z) = -logDeriv riemannXi z := by
  have hfun : (fun s : ℂ => riemannXi (1 - s)) =ᶠ[𝓝 z] riemannXi :=
    Filter.Eventually.of_forall riemannXi_one_sub
  have hderiv := Filter.EventuallyEq.deriv_eq hfun
  rw [deriv_comp_const_sub] at hderiv
  have hderiv' : deriv riemannXi (1 - z) = -deriv riemannXi z := by
    calc
      deriv riemannXi (1 - z) = -(-deriv riemannXi (1 - z)) := by ring
      _ = -deriv riemannXi z := congrArg Neg.neg hderiv
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub, hderiv']
  ring

/-- The Gaussian at a xi zero, multiplied by the squared zero norm, has a uniform bound depending
only on the positive Gaussian parameter. This deliberately uses only the critical-strip bounds. -/
theorem norm_riemannXiGaussianWeight_mul_zero_norm_sq_le
    {a : ℝ} (ha : 0 < a) (p : RiemannXiDivisorZeroIndex) :
    ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ *
        ‖riemannXiDivisorZeroValue p‖ ^ 2 ≤
      Real.exp (a / 4) * (1 + 1 / a) := by
  let rho : ℂ := riemannXiDivisorZeroValue p
  have hrho : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hreflect : IsNontrivialZero (1 - rho) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
  have hre0 : 0 < rho.re := by
    have hreflectRe := nontrivial_zero_re_lt_one hreflect
    simp only [sub_re, one_re] at hreflectRe
    linarith
  have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
  have hcenter : (rho.re - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (rho.re - 1 / 2)]
  have himNonneg : 0 ≤ a * rho.im ^ 2 :=
    mul_nonneg ha.le (sq_nonneg rho.im)
  have himExp : rho.im ^ 2 * Real.exp (-a * rho.im ^ 2) ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    calc
      rho.im ^ 2 * Real.exp (-a * rho.im ^ 2) * a =
          (a * rho.im ^ 2) * Real.exp (-(a * rho.im ^ 2)) := by
        rw [show -a * rho.im ^ 2 = -(a * rho.im ^ 2) by ring]
        ring
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hreSq : rho.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg rho.re]
  have himExpOne : Real.exp (-a * rho.im ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hinside :
      Real.exp (-a * rho.im ^ 2) * (rho.re ^ 2 + rho.im ^ 2) ≤ 1 + 1 / a := by
    calc
      Real.exp (-a * rho.im ^ 2) * (rho.re ^ 2 + rho.im ^ 2) =
          Real.exp (-a * rho.im ^ 2) * rho.re ^ 2 +
            rho.im ^ 2 * Real.exp (-a * rho.im ^ 2) := by ring
      _ ≤ 1 * 1 + 1 / a := by
        gcongr
      _ = 1 + 1 / a := by ring
  have hcenterExp :
      Real.exp (a * (rho.re - 1 / 2) ^ 2) ≤ Real.exp (a / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [norm_riemannXiGaussianWeight, Complex.sq_norm, Complex.normSq_apply]
  have hsplit :
      Real.exp (a * ((rho.re - 1 / 2) ^ 2 - rho.im ^ 2)) =
        Real.exp (a * (rho.re - 1 / 2) ^ 2) * Real.exp (-a * rho.im ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc
    (Real.exp (a * (rho.re - 1 / 2) ^ 2) * Real.exp (-a * rho.im ^ 2)) *
        (rho.re * rho.re + rho.im * rho.im) =
      Real.exp (a * (rho.re - 1 / 2) ^ 2) *
        (Real.exp (-a * rho.im ^ 2) * (rho.re ^ 2 + rho.im ^ 2)) := by ring
    _ ≤ Real.exp (a / 4) * (1 + 1 / a) := by
      exact mul_le_mul hcenterExp hinside
        (by positivity) (Real.exp_pos _).le

/-- The Gaussian zero weight is dominated by the compiled reciprocal-square Hadamard majorant. -/
theorem norm_riemannXiGaussianWeight_zero_le_inv_sq
    {a : ℝ} (ha : 0 < a) (p : RiemannXiDivisorZeroIndex) :
    ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ ≤
      (Real.exp (a / 4) * (1 + 1 / a)) *
        (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hnormPos : 0 < ‖riemannXiDivisorZeroValue p‖ := norm_pos_iff.mpr hp0
  have hbound := norm_riemannXiGaussianWeight_mul_zero_norm_sq_le ha p
  calc
    ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ =
        (‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ *
          ‖riemannXiDivisorZeroValue p‖ ^ 2) *
            (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
      field_simp [hnormPos.ne']
    _ ≤ (Real.exp (a / 4) * (1 + 1 / a)) *
        (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
      gcongr

/-- The critical-line-centered Gaussian is absolutely summable over all xi zeros with analytic
multiplicity. No ordering convention, RH, zero-count asymptotic, or simplicity premise is used. -/
theorem summable_riemannXiGaussianWeight {a : ℝ} (ha : 0 < a) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)) := by
  apply Summable.of_norm_bounded
    (summable_riemannXiDivisorZeroIndex_norm_inv_sq.mul_left
      (Real.exp (a / 4) * (1 + 1 / a)))
  exact norm_riemannXiGaussianWeight_zero_le_inv_sq ha

/-- A unit interval contains a point quantitatively separated from every point of a prescribed
finite set. The deliberately non-sharp constant makes the finite-union measure proof robust. -/
theorem exists_mem_Ioo_forall_finset_abs_sub_ge
    (s : Finset ℝ) (R : ℝ) :
    ∃ T ∈ Ioo R (R + 1),
      ∀ y ∈ s, 1 / (4 * ((s.card : ℝ) + 1)) ≤ |T - y| := by
  classical
  let delta : ℝ := 1 / (4 * ((s.card : ℝ) + 1))
  let bad : Set ℝ := ⋃ y ∈ s, Ioo (y - delta) (y + delta)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hbadMeasure : volume.real bad ≤ (s.card : ℝ) * (2 * delta) := by
    calc
      volume.real bad ≤ ∑ y ∈ s, volume.real (Ioo (y - delta) (y + delta)) := by
        dsimp only [bad]
        exact measureReal_biUnion_finset_le s _
      _ = ∑ _y ∈ s, 2 * delta := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Real.volume_real_Ioo_of_le (by linarith [hdelta.le])]
        ring
      _ = (s.card : ℝ) * (2 * delta) := by simp
  have hbadLt : volume.real bad < 1 := by
    apply lt_of_le_of_lt hbadMeasure
    dsimp only [delta]
    have hcard : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    rw [div_eq_mul_inv]
    have hden : 0 < 4 * ((s.card : ℝ) + 1) := by positivity
    calc
      (s.card : ℝ) * (2 * (1 * (4 * ((s.card : ℝ) + 1))⁻¹)) =
          (2 * (s.card : ℝ)) / (4 * ((s.card : ℝ) + 1)) := by
            rw [div_eq_mul_inv]
            ring
      _ < 1 := by
        rw [div_lt_one hden]
        nlinarith
  by_contra hnone
  push Not at hnone
  have hsubset : Ioo R (R + 1) ⊆ bad := by
    intro T hT
    obtain ⟨y, hy, hdist⟩ := hnone T hT
    have hdist' : |T - y| < delta := by
      simpa only [delta] using hdist
    rw [abs_lt] at hdist'
    dsimp only [bad]
    simp only [Set.mem_iUnion]
    refine ⟨y, ?_⟩
    refine ⟨hy, ?_⟩
    constructor <;> linarith
  have hbadFinite : volume bad < (⊤ : ENNReal) := by
    dsimp only [bad]
    apply measure_biUnion_lt_top s.finite_toSet
    intro y _hy
    simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]
  have hmono : volume.real (Ioo R (R + 1)) ≤ volume.real bad :=
    measureReal_mono hsubset hbadFinite.ne
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hmono
  linarith

/-- The multiplicity-bearing xi zeros of norm at most `R`, packaged as a finite set. -/
noncomputable def riemannXiZeroNormFinset (R : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := riemannXi) (U := (Set.univ : Set ℂ)) R (by simp)).toFinset

@[simp] theorem mem_riemannXiZeroNormFinset_iff
    (R : ℝ) (p : RiemannXiDivisorZeroIndex) :
    p ∈ riemannXiZeroNormFinset R ↔ ‖riemannXiDivisorZeroValue p‖ ≤ R := by
  classical
  simp only [riemannXiZeroNormFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- Squared-reciprocal summability alone gives the coarse polynomial zero-count estimate needed
by the Gaussian argument. No Riemann--von Mangoldt asymptotic is imported. -/
theorem riemannXiZeroNormFinset_card_le
    {R : ℝ} (hR : 0 < R) :
    (riemannXiZeroNormFinset R).card ≤
      R ^ 2 * ∑' p : RiemannXiDivisorZeroIndex,
        ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ) := by
  let u : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)
  have hu : Summable u := summable_riemannXiDivisorZeroIndex_norm_inv_sq
  have hterm : ∀ p ∈ riemannXiZeroNormFinset R, R⁻¹ ^ (2 : ℕ) ≤ u p := by
    intro p hp
    have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
      Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    have hpNorm : 0 < ‖riemannXiDivisorZeroValue p‖ := norm_pos_iff.mpr hp0
    have hpLe : ‖riemannXiDivisorZeroValue p‖ ≤ R :=
      (mem_riemannXiZeroNormFinset_iff R p).mp hp
    have hinv : R⁻¹ ≤ ‖riemannXiDivisorZeroValue p‖⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hpNorm hpLe
    dsimp only [u]
    gcongr
  have hmass :
      ((riemannXiZeroNormFinset R).card : ℝ) * R⁻¹ ^ (2 : ℕ) ≤ ∑' p, u p := by
    calc
      ((riemannXiZeroNormFinset R).card : ℝ) * R⁻¹ ^ (2 : ℕ) =
          ∑ _p ∈ riemannXiZeroNormFinset R, R⁻¹ ^ (2 : ℕ) := by simp
      _ ≤ ∑ p ∈ riemannXiZeroNormFinset R, u p := by
        exact Finset.sum_le_sum hterm
      _ ≤ ∑' p, u p := hu.sum_le_tsum _ (fun _p _hp => by positivity)
  have hcancel : R⁻¹ ^ (2 : ℕ) * R ^ 2 = 1 := by
    field_simp [hR.ne']
  calc
    ((riemannXiZeroNormFinset R).card : ℝ) =
        (((riemannXiZeroNormFinset R).card : ℝ) * R⁻¹ ^ (2 : ℕ)) * R ^ 2 := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ (∑' p, u p) * R ^ 2 := by
      exact mul_le_mul_of_nonneg_right hmass (sq_nonneg R)
    _ = R ^ 2 * ∑' p : RiemannXiDivisorZeroIndex,
        ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ) := by
      dsimp only [u]
      ring

/-- The polynomial scale used for the `n`-th Gaussian contour. -/
def gaussianXiHeightScale (c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) + c + 3

theorem tendsto_gaussianXiHeightScale (c : ℝ) :
    Tendsto (gaussianXiHeightScale c) atTop atTop := by
  have heq : gaussianXiHeightScale c = fun n : ℕ => (n : ℝ) + (c + 3) := by
    funext n
    unfold gaussianXiHeightScale
    ring
  rw [heq]
  exact tendsto_atTop_add_const_right atTop (c + 3) tendsto_natCast_atTop_atTop

/-- Nearby xi zeros whose ordinates must be quantitatively avoided at the `n`-th contour. -/
noncomputable def gaussianXiNearZeroFinset (c : ℝ) (n : ℕ) :
    Finset RiemannXiDivisorZeroIndex :=
  riemannXiZeroNormFinset (4 * gaussianXiHeightScale c n)

/-- Absolute ordinates of the nearby multiplicity-bearing zeros. Duplicates are harmless here. -/
noncomputable def gaussianXiNearAbsImFinset (c : ℝ) (n : ℕ) : Finset ℝ :=
  (gaussianXiNearZeroFinset c n).image
    (fun p => |(riemannXiDivisorZeroValue p).im|)

/-- A canonical choice of a height in the next unit interval that is separated from all nearby
absolute zero ordinates. -/
noncomputable def gaussianXiSelectedHeight (c : ℝ) (n : ℕ) : ℝ :=
  Classical.choose
    (exists_mem_Ioo_forall_finset_abs_sub_ge
      (gaussianXiNearAbsImFinset c n) (gaussianXiHeightScale c n))

theorem gaussianXiSelectedHeight_spec (c : ℝ) (n : ℕ) :
    gaussianXiSelectedHeight c n ∈
        Ioo (gaussianXiHeightScale c n) (gaussianXiHeightScale c n + 1) ∧
      ∀ y ∈ gaussianXiNearAbsImFinset c n,
        1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)) ≤
          |gaussianXiSelectedHeight c n - y| := by
  exact Classical.choose_spec
    (exists_mem_Ioo_forall_finset_abs_sub_ge
      (gaussianXiNearAbsImFinset c n) (gaussianXiHeightScale c n))

theorem tendsto_gaussianXiSelectedHeight (c : ℝ) :
    Tendsto (gaussianXiSelectedHeight c) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n => (gaussianXiSelectedHeight_spec c n).1.1.le)
    (tendsto_gaussianXiHeightScale c)

theorem gaussianXiHeightScale_pos {c : ℝ} (hc : 1 < c) (n : ℕ) :
    0 < gaussianXiHeightScale c n := by
  unfold gaussianXiHeightScale
  positivity

/-- A fixed power of the campaign scale is absorbed by its Gaussian decay. -/
theorem tendsto_gaussianXiHeightScale_pow_four_mul_exp_neg_sq
    {a c : ℝ} (ha : 0 < a) :
    Tendsto
      (fun n : ℕ => gaussianXiHeightScale c n ^ 4 *
        Real.exp (-a * gaussianXiHeightScale c n ^ 2))
      atTop (𝓝 0) := by
  have hdecay :
      Tendsto (fun R : ℝ => R ^ (4 : ℝ) * Real.exp (-a * R ^ 2)) atTop (𝓝 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha 4).tendsto_zero_of_tendsto
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr one_half_pos)))
  have hdecay' :
      Tendsto (fun R : ℝ => R ^ (4 : ℕ) * Real.exp (-a * R ^ 2)) atTop (𝓝 0) := by
    apply hdecay.congr'
    exact Filter.Eventually.of_forall fun R => by
      exact congrArg (fun q : ℝ => q * Real.exp (-a * R ^ 2))
        (Real.rpow_natCast R 4)
  change Tendsto
    ((fun R : ℝ => R ^ (4 : ℕ) * Real.exp (-a * R ^ 2)) ∘
      gaussianXiHeightScale c) atTop (𝓝 0)
  exact hdecay'.comp (tendsto_gaussianXiHeightScale c)

/-- Every selected symmetric rectangle has a genuinely zero-free boundary. -/
theorem gaussianXiSelectedHeight_zeroFreeBoundary
    {c : ℝ} (hc : 1 < c) (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    ¬riemannXiZeroOnRectangleBoundary
      (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p := by
  let rho : ℂ := riemannXiDivisorZeroValue p
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  have hrho : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hreflect : IsNontrivialZero (1 - rho) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
  have hre0 : 0 < rho.re := by
    have hreflectRe := nontrivial_zero_re_lt_one hreflect
    simp only [sub_re, one_re] at hreflectRe
    linarith
  have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
  have hRpos : 0 < R := gaussianXiHeightScale_pos hc n
  have hRtwo : 2 < R := by
    dsimp only [R, gaussianXiHeightScale]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hTmem : T ∈ Ioo R (R + 1) := (gaussianXiSelectedHeight_spec c n).1
  have hTpos : 0 < T := lt_trans hRpos hTmem.1
  have hnear_of_abs_im_eq (him : |rho.im| = T) : p ∈ gaussianXiNearZeroFinset c n := by
    rw [gaussianXiNearZeroFinset, mem_riemannXiZeroNormFinset_iff]
    apply le_of_lt
    calc
      ‖rho‖ ≤ |rho.re| + |rho.im| := Complex.norm_le_abs_re_add_abs_im rho
      _ = rho.re + T := by rw [abs_of_pos hre0, him]
      _ < R + 2 := by linarith [hTmem.2]
      _ < 4 * R := by linarith
  have hsep_of_abs_im_eq (him : |rho.im| = T) : False := by
    have hpNear := hnear_of_abs_im_eq him
    have himMem : |rho.im| ∈ gaussianXiNearAbsImFinset c n := by
      rw [gaussianXiNearAbsImFinset]
      exact Finset.mem_image.mpr ⟨p, hpNear, rfl⟩
    have hsep := (gaussianXiSelectedHeight_spec c n).2 |rho.im| himMem
    have hdeltaPos :
        0 < 1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)) := by
      positivity
    rw [him, sub_self, abs_zero] at hsep
    linarith
  intro hboundary
  rcases hboundary with hbottom | htop | hleft | hright
  · apply hsep_of_abs_im_eq
    rw [hbottom.1, abs_neg, abs_of_pos hTpos]
  · apply hsep_of_abs_im_eq
    rw [htop.1, abs_of_pos hTpos]
  · linarith [hleft.1]
  · linarith [hright.1]

/-- The compensated genus-one zero term has reciprocal-square decay once the zero is farther than
twice the evaluation point. -/
theorem norm_riemannXiLogDerivZeroTerm_le_of_two_norm_lt
    {z : ℂ} (p : RiemannXiDivisorZeroIndex)
    (hfar : 2 * ‖z‖ < ‖riemannXiDivisorZeroValue p‖) :
    ‖riemannXiLogDerivZeroTerm p z‖ ≤
      (2 * ‖z‖) * (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  let rho : ℂ := riemannXiDivisorZeroValue p
  have hrho0 : rho ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hzrho : z - rho ≠ 0 := by
    intro hzero
    have heq : z = rho := sub_eq_zero.mp hzero
    rw [heq] at hfar
    nlinarith [norm_nonneg rho]
  have hterm : riemannXiLogDerivZeroTerm p z = z / (rho * (z - rho)) := by
    rw [riemannXiLogDerivZeroTerm]
    change 1 / (z - rho) + 1 / rho = z / (rho * (z - rho))
    field_simp [hrho0, hzrho]
    ring
  have htri : ‖rho‖ ≤ ‖z‖ + ‖z - rho‖ := by
    have hraw : ‖rho‖ ≤ ‖z‖ + ‖rho - z‖ := by
      have h := norm_add_le z (rho - z)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hhalf : ‖rho‖ / 2 ≤ ‖z - rho‖ := by nlinarith
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho0
  have hzrhoNorm : 0 < ‖z - rho‖ := norm_pos_iff.mpr hzrho
  rw [hterm, norm_div, norm_mul, div_eq_mul_inv]
  calc
    ‖z‖ * (‖rho‖ * ‖z - rho‖)⁻¹ =
        ‖z‖ * ‖rho‖⁻¹ * ‖z - rho‖⁻¹ := by
      field_simp [hrhoNorm.ne', hzrhoNorm.ne']
    _ ≤ ‖z‖ * ‖rho‖⁻¹ * (2 * ‖rho‖⁻¹) := by
      gcongr
      have hhalfPos : 0 < ‖rho‖ / 2 := by positivity
      have hinv : ‖z - rho‖⁻¹ ≤ (‖rho‖ / 2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hhalfPos hhalf
      have hhalfInv : (‖rho‖ / 2)⁻¹ = 2 * ‖rho‖⁻¹ := by
        field_simp [hrhoNorm.ne']
      simpa only [hhalfInv] using hinv
    _ = (2 * ‖z‖) * (‖rho‖⁻¹ ^ (2 : ℕ)) := by ring

/-- On a horizontal line separated by `delta` from a zero ordinate, the uncompensated reciprocal
part costs at most `delta^(-1)`; the genus-one correction contributes `norm(rho)^(-1)`. -/
theorem norm_riemannXiLogDerivZeroTerm_le_of_im_separated
    {z : ℂ} (p : RiemannXiDivisorZeroIndex) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : delta ≤ |z.im - (riemannXiDivisorZeroValue p).im|) :
    ‖riemannXiLogDerivZeroTerm p z‖ ≤
      delta⁻¹ + ‖riemannXiDivisorZeroValue p‖⁻¹ := by
  let rho : ℂ := riemannXiDivisorZeroValue p
  have himNorm : |z.im - rho.im| ≤ ‖z - rho‖ := by
    simpa only [sub_im] using Complex.abs_im_le_norm (z - rho)
  have hdist : delta ≤ ‖z - rho‖ := le_trans hsep himNorm
  rw [riemannXiLogDerivZeroTerm]
  calc
    ‖1 / (z - rho) + 1 / rho‖ ≤ ‖1 / (z - rho)‖ + ‖1 / rho‖ := norm_add_le _ _
    _ = ‖z - rho‖⁻¹ + ‖rho‖⁻¹ := by simp
    _ ≤ delta⁻¹ + ‖rho‖⁻¹ := by
      gcongr

/-- The derivative of the degree-at-most-one Hadamard polynomial is constant. -/
theorem eval_derivative_eq_coeff_zero_of_degree_le_one
    {P : Polynomial ℂ} (hP : P.degree ≤ 1) (z : ℂ) :
    Polynomial.eval z P.derivative = P.derivative.coeff 0 := by
  have hdegree : P.derivative.degree ≤ 0 := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have hlt : P.derivative.degree < (1 : WithBot ℕ) :=
        lt_of_lt_of_le (Polynomial.degree_derivative_lt hP0) hP
      rw [Polynomial.degree_le_iff_coeff_zero]
      intro m hm
      apply (Polynomial.degree_lt_iff_coeff_zero P.derivative 1).mp hlt
      exact_mod_cast hm
  rw [Polynomial.eq_C_of_degree_le_zero hdegree, Polynomial.eval_C]
  simp

/-- Total squared-reciprocal xi-zero mass, with analytic multiplicity. -/
def riemannXiReciprocalSquareMass : ℝ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)

theorem riemannXiReciprocalSquareMass_nonneg :
    0 ≤ riemannXiReciprocalSquareMass := by
  exact tsum_nonneg fun _ => by positivity

theorem riemannXiDivisorZeroValue_norm_inv_le_mass_add_one
    (p : RiemannXiDivisorZeroIndex) :
    ‖riemannXiDivisorZeroValue p‖⁻¹ ≤ riemannXiReciprocalSquareMass + 1 := by
  let u : RiemannXiDivisorZeroIndex → ℝ := fun q =>
    ‖riemannXiDivisorZeroValue q‖⁻¹ ^ (2 : ℕ)
  have hu : Summable u := summable_riemannXiDivisorZeroIndex_norm_inv_sq
  have hpLe : u p ≤ ∑' q, u q := hu.le_tsum p (fun _q _hq => by positivity)
  have hpNonneg : 0 ≤ ‖riemannXiDivisorZeroValue p‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hmassNonneg : 0 ≤ riemannXiReciprocalSquareMass :=
    riemannXiReciprocalSquareMass_nonneg
  dsimp only [u] at hpLe
  dsimp only [riemannXiReciprocalSquareMass]
  nlinarith [sq_nonneg (‖riemannXiDivisorZeroValue p‖⁻¹ - 1)]

/-- The selected top edge is separated from the ordinate of every nearby zero. -/
theorem gaussianXiSelectedHeight_sep_im_of_mem_near
    {c : ℝ} (hc : 1 < c) (n : ℕ) (p : RiemannXiDivisorZeroIndex)
    (hp : p ∈ gaussianXiNearZeroFinset c n) :
    1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)) ≤
      |gaussianXiSelectedHeight c n - (riemannXiDivisorZeroValue p).im| := by
  have himMem : |(riemannXiDivisorZeroValue p).im| ∈
      gaussianXiNearAbsImFinset c n := by
    rw [gaussianXiNearAbsImFinset]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hsep := (gaussianXiSelectedHeight_spec c n).2
    |(riemannXiDivisorZeroValue p).im| himMem
  have hTpos : 0 < gaussianXiSelectedHeight c n :=
    lt_trans (gaussianXiHeightScale_pos hc n) (gaussianXiSelectedHeight_spec c n).1.1
  exact hsep.trans (by
    simpa only [abs_of_pos hTpos] using
      abs_abs_sub_abs_le_abs_sub
        (gaussianXiSelectedHeight c n) (riemannXiDivisorZeroValue p).im)

/-- Points of the selected top edge have norm below twice the campaign scale. -/
theorem norm_selectedGaussianTopEdge_lt
    {c : ℝ} (hc : 1 < c) (n : ℕ) {x : ℝ} (hx : x ∈ [[1 - c, c]]) :
    ‖(x : ℂ) + gaussianXiSelectedHeight c n * I‖ <
      2 * gaussianXiHeightScale c n := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  have habsx : |x| ≤ c := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hT := (gaussianXiSelectedHeight_spec c n).1.2
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    ((x : ℂ) + gaussianXiSelectedHeight c n * I)
  have hre : (((x : ℂ) + gaussianXiSelectedHeight c n * I).re) = x := by simp
  have him : (((x : ℂ) + gaussianXiSelectedHeight c n * I).im) =
      gaussianXiSelectedHeight c n := by simp
  rw [hre, him, abs_of_pos (lt_trans (gaussianXiHeightScale_pos hc n)
    (gaussianXiSelectedHeight_spec c n).1.1)] at hnorm
  calc
    ‖(x : ℂ) + gaussianXiSelectedHeight c n * I‖ ≤
        |x| + gaussianXiSelectedHeight c n := hnorm
    _ ≤ c + gaussianXiSelectedHeight c n := by gcongr
    _ < c + (gaussianXiHeightScale c n + 1) := by gcongr
    _ < 2 * gaussianXiHeightScale c n := by
      unfold gaussianXiHeightScale
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

/-- The Gaussian has uniform quadratic decay along each selected top edge. -/
theorem norm_riemannXiGaussianWeight_selectedTopEdge_le
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (n : ℕ) {x : ℝ}
    (hx : x ∈ [[1 - c, c]]) :
    ‖riemannXiGaussianWeight a
        ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
      Real.exp (a * (c - 1 / 2) ^ 2) *
        Real.exp (-a * gaussianXiHeightScale c n ^ 2) := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  have hRpos : 0 < R := gaussianXiHeightScale_pos hc n
  have hTgt : R < T := (gaussianXiSelectedHeight_spec c n).1.1
  have hcenterLower : -(c - 1 / 2) ≤ x - 1 / 2 := by linarith [hx.1]
  have hcenterUpper : x - 1 / 2 ≤ c - 1 / 2 := by linarith [hx.2]
  have hcenterProd :
      0 ≤ ((c - 1 / 2) + (x - 1 / 2)) *
        ((c - 1 / 2) - (x - 1 / 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have hcenterSq : (x - 1 / 2) ^ 2 ≤ (c - 1 / 2) ^ 2 := by
    nlinarith
  have hheightSq : R ^ 2 < T ^ 2 := by nlinarith
  rw [norm_riemannXiGaussianWeight]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, sub_zero, add_zero,
    add_im, mul_im, I_im, mul_one, zero_add]
  change Real.exp (a * ((x - 1 / 2) ^ 2 - T ^ 2)) ≤
    Real.exp (a * (c - 1 / 2) ^ 2) *
      Real.exp (-a * gaussianXiHeightScale c n ^ 2)
  calc
    Real.exp (a * ((x - 1 / 2) ^ 2 - T ^ 2)) ≤
        Real.exp (a * (c - 1 / 2) ^ 2 - a * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * R ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (a * (c - 1 / 2) ^ 2) *
        Real.exp (-a * gaussianXiHeightScale c n ^ 2) := by
      rfl

/-- On every selected top edge, xi's logarithmic derivative is bounded by one fixed Hadamard
constant, a finite near-zero contribution, and a reciprocal-square far-zero contribution. -/
theorem exists_norm_logDeriv_selectedGaussianTopEdge_le
    {c : ℝ} (hc : 1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x ∈ [[1 - c, c]],
      ‖logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        C + ((gaussianXiNearZeroFinset c n).card : ℝ) *
            ((1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)))⁻¹ +
              (riemannXiReciprocalSquareMass + 1)) +
          4 * gaussianXiHeightScale c n * riemannXiReciprocalSquareMass := by
  obtain ⟨P, hPdegree, hPfac⟩ := exists_riemannXi_hadamard_factorization
  refine ⟨‖P.derivative.coeff 0‖, norm_nonneg _, ?_⟩
  intro n x hx
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  let z : ℂ := (x : ℂ) + T * I
  let near : Finset RiemannXiDivisorZeroIndex := gaussianXiNearZeroFinset c n
  let delta : ℝ := 1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1))
  let u : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)
  have hRpos : 0 < R := gaussianXiHeightScale_pos hc n
  have hTpos : 0 < T :=
    lt_trans hRpos (gaussianXiSelectedHeight_spec c n).1.1
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hlr : 1 - c < c := by linarith
  have hbt : -T < T := by linarith
  obtain ⟨_hbottomMap, htopMap, _hrightMap, _hleftMap⟩ :=
    mapsTo_riemannXiNonzeroSet_rectangle_edges hlr hbt
      (gaussianXiSelectedHeight_zeroFreeBoundary hc n)
  have hznonzero : z ∈ riemannXiNonzeroSet := by
    apply htopMap
    simpa only [z, T] using hx
  have hsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiLogDerivZeroTerm p z) :=
    summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet hznonzero
  have hu : Summable u := summable_riemannXiDivisorZeroIndex_norm_inv_sq
  have hnearTerm : ∀ p ∈ near,
      ‖riemannXiLogDerivZeroTerm p z‖ ≤
        delta⁻¹ + (riemannXiReciprocalSquareMass + 1) := by
    intro p hp
    have hsepRaw := gaussianXiSelectedHeight_sep_im_of_mem_near hc n p (by
      simpa only [near] using hp)
    have hzim : z.im = T := by simp [z]
    have hsep : delta ≤ |z.im - (riemannXiDivisorZeroValue p).im| := by
      simpa only [delta, hzim, T] using hsepRaw
    exact (norm_riemannXiLogDerivZeroTerm_le_of_im_separated p hdelta hsep).trans
      (by
        gcongr
        exact riemannXiDivisorZeroValue_norm_inv_le_mass_add_one p)
  have hnearSum :
      ∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖ ≤
        (near.card : ℝ) * (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
    calc
      ∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖ ≤
          ∑ _p ∈ near, (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
            exact Finset.sum_le_sum hnearTerm
      _ = (near.card : ℝ) *
          (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
        simp
        ring
  have hfarTerm : ∀ q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
      ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤ (4 * R) * u q.1 := by
    intro q
    have hqNot : q.1 ∉ near := by
      intro hq
      exact q.2 hq
    have hqNorm : 4 * R < ‖riemannXiDivisorZeroValue q.1‖ := by
      apply lt_of_not_ge
      intro hle
      apply hqNot
      simpa only [near, gaussianXiNearZeroFinset,
        mem_riemannXiZeroNormFinset_iff, R] using hle
    have hzNorm : ‖z‖ < 2 * R := by
      simpa only [z, T, R] using norm_selectedGaussianTopEdge_lt hc n hx
    have hfar : 2 * ‖z‖ < ‖riemannXiDivisorZeroValue q.1‖ := by
      nlinarith
    calc
      ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
          (2 * ‖z‖) * u q.1 :=
        norm_riemannXiLogDerivZeroTerm_le_of_two_norm_lt q.1 hfar
      _ ≤ (4 * R) * u q.1 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
  have hfarMajorant : Summable (fun q : (nearᶜ : Set RiemannXiDivisorZeroIndex) =>
      (4 * R) * u q.1) := (hu.subtype _).mul_left (4 * R)
  have hfarSum :
      ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
          ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
        4 * R * riemannXiReciprocalSquareMass := by
    calc
      ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
          ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
          ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex), (4 * R) * u q.1 :=
        (hsum.norm.subtype _).tsum_le_tsum hfarTerm hfarMajorant
      _ = (4 * R) * ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex), u q.1 := by
        rw [tsum_mul_left]
      _ ≤ (4 * R) * ∑' p : RiemannXiDivisorZeroIndex, u p := by
        gcongr
        exact Summable.tsum_subtype_le u _ (fun _p => by positivity) hu
      _ = 4 * R * riemannXiReciprocalSquareMass := by
        dsimp only [u, riemannXiReciprocalSquareMass]
  have hzeroSum :
      ‖∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z‖ ≤
        (near.card : ℝ) * (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          4 * R * riemannXiReciprocalSquareMass := by
    calc
      ‖∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z‖ ≤
          ∑' p : RiemannXiDivisorZeroIndex, ‖riemannXiLogDerivZeroTerm p z‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ = (∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖) +
          ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
            ‖riemannXiLogDerivZeroTerm q.1 z‖ :=
        hsum.norm.sum_add_tsum_compl.symm
      _ ≤ (near.card : ℝ) * (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          4 * R * riemannXiReciprocalSquareMass := add_le_add hnearSum hfarSum
  have hlog := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hPfac hznonzero
  rw [hlog, eval_derivative_eq_coeff_zero_of_degree_le_one hPdegree]
  calc
    ‖↑(P.derivative.coeff 0) +
        ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z‖ ≤
      ‖P.derivative.coeff 0‖ +
        ‖∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z‖ := norm_add_le _ _
    _ ≤ ‖P.derivative.coeff 0‖ +
        ((near.card : ℝ) * (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          4 * R * riemannXiReciprocalSquareMass) := by gcongr
    _ = ‖P.derivative.coeff 0‖ + ((gaussianXiNearZeroFinset c n).card : ℝ) *
            ((1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)))⁻¹ +
              (riemannXiReciprocalSquareMass + 1)) +
          4 * gaussianXiHeightScale c n * riemannXiReciprocalSquareMass := by
      dsimp only [near, delta, R]
      ring

/-- The selected-height logarithmic derivative has a single coarse fourth-power bound. The power
is intentionally non-sharp; Gaussian decay, rather than zero-count sharpness, is the mechanism. -/
theorem exists_norm_logDeriv_selectedGaussianTopEdge_le_scale_pow_four
    {c : ℝ} (hc : 1 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∀ x ∈ [[1 - c, c]],
      ‖logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        K * gaussianXiHeightScale c n ^ 4 := by
  obtain ⟨C, hC, hraw⟩ := exists_norm_logDeriv_selectedGaussianTopEdge_le hc
  let M : ℝ := riemannXiReciprocalSquareMass
  let K : ℝ := C + 1108 * (M + 1) ^ 2
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro n x hx
  let R : ℝ := gaussianXiHeightScale c n
  let N : ℝ := ((gaussianXiNearZeroFinset c n).card : ℝ)
  let A : ℝ := ((gaussianXiNearAbsImFinset c n).card : ℝ)
  have hR : 2 < R := by
    dsimp only [R, gaussianXiHeightScale]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hRone : 1 ≤ R := hR.le.trans' (by norm_num)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact riemannXiReciprocalSquareMass_nonneg
  have hNnonneg : 0 ≤ N := by dsimp only [N]; positivity
  have hAnonneg : 0 ≤ A := by dsimp only [A]; positivity
  have hcardRaw := riemannXiZeroNormFinset_card_le (R := 4 * R) (by positivity)
  have hNraw : N ≤ (4 * R) ^ 2 * M := by
    dsimp only [N, M]
    simpa only [gaussianXiNearZeroFinset, R, riemannXiReciprocalSquareMass] using hcardRaw
  have hN : N ≤ 16 * R ^ 2 * M := by
    calc
      N ≤ (4 * R) ^ 2 * M := hNraw
      _ = 16 * R ^ 2 * M := by ring
  have hA : A ≤ N := by
    have himage := Finset.card_image_le
      (s := gaussianXiNearZeroFinset c n)
      (f := fun p => |(riemannXiDivisorZeroValue p).im|)
    dsimp only [A, N, gaussianXiNearAbsImFinset]
    exact_mod_cast himage
  have hdeltaInv :
      (1 / (4 * (A + 1)))⁻¹ = 4 * (A + 1) := by
    have hden : 4 * (A + 1) ≠ 0 := by positivity
    field_simp
  have hNcoarse : N ≤ 16 * R ^ 2 * (M + 1) := by
    have hR2nonneg : 0 ≤ 16 * R ^ 2 := by positivity
    exact hN.trans (mul_le_mul_of_nonneg_left (by linarith) hR2nonneg)
  have hAcoarse : 4 * (A + 1) ≤ 68 * R ^ 2 * (M + 1) := by
    have hbase : 1 ≤ R ^ 2 * (M + 1) := by
      have hR2 : 1 ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
      have hMone : 1 ≤ M + 1 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hR2) (sub_nonneg.mpr hMone)]
    nlinarith
  have hmassCoarse : M + 1 ≤ R ^ 2 * (M + 1) := by
    have hMone : 0 ≤ M + 1 := by linarith
    have hR2 : 1 ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR2) hMone]
  have hbracket : 4 * (A + 1) + (M + 1) ≤ 69 * R ^ 2 * (M + 1) := by
    linarith
  have hnear :
      N * (4 * (A + 1) + (M + 1)) ≤ 1104 * R ^ 4 * (M + 1) ^ 2 := by
    have hmul := mul_le_mul hNcoarse hbracket
      (by positivity) (by positivity)
    calc
      N * (4 * (A + 1) + (M + 1)) ≤
          (16 * R ^ 2 * (M + 1)) * (69 * R ^ 2 * (M + 1)) := hmul
      _ = 1104 * R ^ 4 * (M + 1) ^ 2 := by ring
  have hRpow : R ≤ R ^ 4 := by
    have hRnonneg : 0 ≤ R := le_trans (by norm_num) hRone
    have hR2 : R ≤ R ^ 2 := by
      nlinarith [mul_nonneg hRnonneg (sub_nonneg.mpr hRone)]
    have hR2one : 1 ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
    have hR24 : R ^ 2 ≤ R ^ 4 := by
      nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hR2one)]
    exact hR2.trans hR24
  have hMpow : M ≤ (M + 1) ^ 2 := by nlinarith [sq_nonneg M]
  have hfar : 4 * R * M ≤ 4 * R ^ 4 * (M + 1) ^ 2 := by
    gcongr
  have hRpowOne : 1 ≤ R ^ 4 := hRone.trans hRpow
  have hconstant : C ≤ C * R ^ 4 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hRpowOne)]
  have hraw' := hraw n x hx
  rw [show (1 / (4 * (((gaussianXiNearAbsImFinset c n).card : ℝ) + 1)))⁻¹ =
      4 * (A + 1) by simpa only [A] using hdeltaInv] at hraw'
  calc
    ‖logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        C + N * (4 * (A + 1) + (M + 1)) + 4 * R * M := by
      simpa only [N, A, M, R, add_assoc] using hraw'
    _ ≤ C * R ^ 4 + 1104 * R ^ 4 * (M + 1) ^ 2 +
        4 * R ^ 4 * (M + 1) ^ 2 := by linarith
    _ = K * gaussianXiHeightScale c n ^ 4 := by
      dsimp only [K, R]
      ring

/-- The weighted logarithmic-derivative integral along the selected top horizontal edge. -/
noncomputable def gaussianXiTopHorizontalIntegral (a c : ℝ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in 1 - c..c,
    riemannXiGaussianWeight a
        ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
      logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)

/-- The selected top horizontal integral is bounded by a fixed constant times the fourth-power
Gaussian majorant. -/
theorem exists_norm_gaussianXiTopHorizontalIntegral_le
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖gaussianXiTopHorizontalIntegral a c n‖ ≤
        B * (gaussianXiHeightScale c n ^ 4 *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
  obtain ⟨K, hK, hlog⟩ :=
    exists_norm_logDeriv_selectedGaussianTopEdge_le_scale_pow_four hc
  let B : ℝ := (2 * c - 1) * Real.exp (a * (c - 1 / 2) ^ 2) * K
  refine ⟨B, by
    dsimp only [B]
    have hlength : 0 < 2 * c - 1 := by linarith
    positivity, ?_⟩
  intro n
  let R : ℝ := gaussianXiHeightScale c n
  let D : ℝ := Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * R ^ 2)
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖riemannXiGaussianWeight a
          ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
        logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        D * (K * R ^ 4) := by
    intro x hx
    rw [norm_mul]
    apply mul_le_mul
    · simpa only [D, R] using
        norm_riemannXiGaussianWeight_selectedTopEdge_le ha hc n
          (Set.uIoc_subset_uIcc hx)
    · simpa only [R] using hlog n x (Set.uIoc_subset_uIcc hx)
    · positivity
    · positivity
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [gaussianXiTopHorizontalIntegral]
  calc
    ‖∫ x : ℝ in 1 - c..c,
        riemannXiGaussianWeight a
            ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
          logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        (D * (K * R ^ 4)) * |c - (1 - c)| := hintegral
    _ = B * (gaussianXiHeightScale c n ^ 4 *
        Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [B, D, R]
      ring

/-- Gaussian decay forces the selected top horizontal integral to vanish. -/
theorem tendsto_gaussianXiTopHorizontalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (gaussianXiTopHorizontalIntegral a c) atTop (𝓝 0) := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_norm_gaussianXiTopHorizontalIntegral_le ha hc
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => hbound n
  · simpa using
      (tendsto_gaussianXiHeightScale_pow_four_mul_exp_neg_sq
        (a := a) (c := c) ha).const_mul B

/-- The Gaussian-weighted xi logarithmic derivative is odd under `s |-> 1-s`. -/
theorem riemannXiGaussianWeightedLogDeriv_one_sub (a : ℝ) (z : ℂ) :
    riemannXiGaussianWeight a (1 - z) * logDeriv riemannXi (1 - z) =
      -(riemannXiGaussianWeight a z * logDeriv riemannXi z) := by
  rw [riemannXiGaussianWeight_one_sub, logDeriv_riemannXi_one_sub]
  ring

/-- The weighted logarithmic-derivative integral along the selected right vertical edge. -/
noncomputable def gaussianXiRightVerticalIntegral (a c : ℝ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
    riemannXiGaussianWeight a ((c : ℂ) + y * I) *
      logDeriv riemannXi ((c : ℂ) + y * I)

/-- Reflection across the critical line identifies the bottom horizontal integral with the
negative of the selected top horizontal integral. -/
theorem gaussianXiBottomHorizontalIntegral_eq_neg_top
    (a c : ℝ) (n : ℕ) :
    (∫ x : ℝ in 1 - c..c,
      riemannXiGaussianWeight a
          ((x : ℂ) - gaussianXiSelectedHeight c n * I) *
        logDeriv riemannXi
          ((x : ℂ) - gaussianXiSelectedHeight c n * I)) =
      -gaussianXiTopHorizontalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun x =>
    riemannXiGaussianWeight a ((x : ℂ) + T * I) *
      logDeriv riemannXi ((x : ℂ) + T * I)
  have hpoint : ∀ x : ℝ,
      riemannXiGaussianWeight a ((x : ℂ) - T * I) *
          logDeriv riemannXi ((x : ℂ) - T * I) = -f (1 - x) := by
    intro x
    have href := riemannXiGaussianWeightedLogDeriv_one_sub a ((x : ℂ) - T * I)
    have harg : (1 : ℂ) - ((x : ℂ) - T * I) = ((1 - x : ℝ) : ℂ) + T * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ x : ℝ in 1 - c..c,
      riemannXiGaussianWeight a ((x : ℂ) - T * I) *
        logDeriv riemannXi ((x : ℂ) - T * I)) =
        ∫ x : ℝ in 1 - c..c, -f (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -(∫ x : ℝ in 1 - c..c, f (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in 1 - c..c, f x) := by
      rw [intervalIntegral.integral_comp_sub_left f 1]
      congr 2
      all_goals ring
    _ = -gaussianXiTopHorizontalIntegral a c n := by
      rfl

/-- Reflection across the critical line and ordinate reversal identify the left vertical
integral with the negative of the selected right vertical integral. -/
theorem gaussianXiLeftVerticalIntegral_eq_neg_right
    (a c : ℝ) (n : ℕ) :
    (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
      riemannXiGaussianWeight a (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -gaussianXiRightVerticalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun y =>
    riemannXiGaussianWeight a ((c : ℂ) + y * I) *
      logDeriv riemannXi ((c : ℂ) + y * I)
  have hpoint : ∀ y : ℝ,
      riemannXiGaussianWeight a (((1 - c : ℝ) : ℂ) + y * I) *
          logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I) = -f (-y) := by
    intro y
    have href := riemannXiGaussianWeightedLogDeriv_one_sub a ((c : ℂ) - y * I)
    have harg : (1 : ℂ) - ((c : ℂ) - y * I) =
        ((1 - c : ℝ) : ℂ) + y * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, neg_neg] using href
  calc
    (∫ y : ℝ in -T..T,
      riemannXiGaussianWeight a (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T, -f (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = -(∫ y : ℝ in -T..T, f (-y)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ y : ℝ in -T..T, f y) := by
      simpa only [zero_sub, neg_neg] using congrArg Neg.neg
        (intervalIntegral.integral_comp_sub_left (a := -T) (b := T) f 0)
    _ = -gaussianXiRightVerticalIntegral a c n := by
      rfl

/-- The finite multiplicity-bearing Gaussian zero sum inside the selected rectangle. -/
noncomputable def gaussianXiRectangleZeroFinsum (a c : ℝ) (n : ℕ) : ℂ :=
  ∑ᶠ p : RiemannXiDivisorZeroIndex,
    if riemannXiZeroStrictlyInsideRectangle
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p then
      riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
    else 0

/-- On the symmetric rectangle, functional-equation reflection reduces the full boundary to one
top horizontal edge and one right vertical edge. -/
theorem gaussianXiRectangleBoundary_eq_top_right
    (a c : ℝ) (n : ℕ) :
    rectangleBoundaryIntegral
        (fun z => riemannXiGaussianWeight a z * logDeriv riemannXi z)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      -2 * gaussianXiTopHorizontalIntegral a c n +
        2 * I * gaussianXiRightVerticalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  rw [rectangleBoundaryIntegral]
  simp only [Complex.ofReal_neg]
  rw [show (∫ x : ℝ in 1 - c..c,
      riemannXiGaussianWeight a ((x : ℂ) + (-T) * I) *
        logDeriv riemannXi ((x : ℂ) + (-T) * I)) =
      -gaussianXiTopHorizontalIntegral a c n by
        simpa only [T, neg_mul, sub_eq_add_neg] using
          gaussianXiBottomHorizontalIntegral_eq_neg_top a c n]
  rw [show (∫ x : ℝ in 1 - c..c,
      riemannXiGaussianWeight a ((x : ℂ) + T * I) *
        logDeriv riemannXi ((x : ℂ) + T * I)) =
      gaussianXiTopHorizontalIntegral a c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) =
      gaussianXiRightVerticalIntegral a c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      riemannXiGaussianWeight a (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -gaussianXiRightVerticalIntegral a c n by
        exact gaussianXiLeftVerticalIntegral_eq_neg_right a c n]
  ring

/-- The finite rectangle identity solved for the selected right vertical integral. The factor is
`pi`, because functional-equation symmetry pairs both vertical edges. -/
theorem gaussianXiRightVerticalIntegral_eq_top_add_zeroFinsum
    {a c : ℝ} (hc : 1 < c) (n : ℕ) :
    gaussianXiRightVerticalIntegral a c n =
      -I * gaussianXiTopHorizontalIntegral a c n +
        (Real.pi : ℂ) * gaussianXiRectangleZeroFinsum a c n := by
  have hTpos : 0 < gaussianXiSelectedHeight c n :=
    lt_trans (gaussianXiHeightScale_pos hc n)
      (gaussianXiSelectedHeight_spec c n).1.1
  have hres :=
    rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
      (differentiable_riemannXiGaussianWeight a)
      (show 1 - c < c by linarith)
      (show -gaussianXiSelectedHeight c n < gaussianXiSelectedHeight c n by linarith)
      (gaussianXiSelectedHeight_zeroFreeBoundary hc n)
  rw [gaussianXiRectangleBoundary_eq_top_right] at hres
  change
    -2 * gaussianXiTopHorizontalIntegral a c n +
        2 * I * gaussianXiRightVerticalIntegral a c n =
      2 * (Real.pi : ℂ) * I * gaussianXiRectangleZeroFinsum a c n at hres
  have hres' :
      2 * I * gaussianXiRightVerticalIntegral a c n =
        2 * gaussianXiTopHorizontalIntegral a c n +
          2 * (Real.pi : ℂ) * I * gaussianXiRectangleZeroFinsum a c n := by
    linear_combination hres
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    ((2 : ℂ) * I) * gaussianXiRightVerticalIntegral a c n =
        2 * I * gaussianXiRightVerticalIntegral a c n := by ring
    _ = 2 * gaussianXiTopHorizontalIntegral a c n +
          2 * (Real.pi : ℂ) * I * gaussianXiRectangleZeroFinsum a c n := hres'
    _ = ((2 : ℂ) * I) *
        (-I * gaussianXiTopHorizontalIntegral a c n +
          (Real.pi : ℂ) * gaussianXiRectangleZeroFinsum a c n) := by
      calc
        2 * gaussianXiTopHorizontalIntegral a c n +
            2 * (Real.pi : ℂ) * I * gaussianXiRectangleZeroFinsum a c n =
          2 * (-(I * I)) * gaussianXiTopHorizontalIntegral a c n +
            2 * (Real.pi : ℂ) * I * gaussianXiRectangleZeroFinsum a c n := by
              rw [Complex.I_mul_I]
              ring
        _ = ((2 : ℂ) * I) *
            (-I * gaussianXiTopHorizontalIntegral a c n +
              (Real.pi : ℂ) * gaussianXiRectangleZeroFinsum a c n) := by ring

/-- The Gaussian interior-zero cutoff has finite support for every finite rectangle. -/
theorem hasFiniteSupport_gaussianXiRectangleZeroCutoff
    (a l r b t : ℝ) :
    Function.HasFiniteSupport
      (fun p : RiemannXiDivisorZeroIndex =>
        if riemannXiZeroStrictlyInsideRectangle l r b t p then
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
        else 0) := by
  classical
  apply (finite_riemannXiZeroStrictlyInsideRectangle l r b t).subset
  intro p hp
  simp only [Function.mem_support] at hp
  by_contra hout
  have hout' : ¬riemannXiZeroStrictlyInsideRectangle l r b t p := by
    simpa only [Set.mem_setOf_eq] using hout
  exact hp (if_neg hout')

/-- Along any heights tending to infinity, the finite symmetric rectangle cutoff of the Gaussian
zero sum converges to its absolute global sum. The fixed vertical lines only need to enclose the
critical strip. -/
theorem tendsto_gaussianXiRectangleZeroFinsum
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n =>
        ∑ᶠ p : RiemannXiDivisorZeroIndex,
          if riemannXiZeroStrictlyInsideRectangle (1 - c) c (-T n) (T n) p then
            riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
          else 0)
      atTop
      (𝓝 (∑' p : RiemannXiDivisorZeroIndex,
        riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) := by
  classical
  let f : ℕ → RiemannXiDivisorZeroIndex → ℂ := fun n p =>
    if riemannXiZeroStrictlyInsideRectangle (1 - c) c (-T n) (T n) p then
      riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
    else 0
  let g : RiemannXiDivisorZeroIndex → ℂ := fun p =>
    riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
  have hpoint : ∀ p : RiemannXiDivisorZeroIndex,
      Tendsto (fun n => f n p) atTop (𝓝 (g p)) := by
    intro p
    let rho : ℂ := riemannXiDivisorZeroValue p
    have hrho : IsNontrivialZero rho :=
      riemannXiDivisorZeroIndex_val_isNontrivialZero p
    have hreflect : IsNontrivialZero (1 - rho) := by
      rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
      exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
    have hre0 : 0 < rho.re := by
      have hreflectRe := nontrivial_zero_re_lt_one hreflect
      simp only [sub_re, one_re] at hreflectRe
      linarith
    have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
    have hheight : ∀ᶠ n : ℕ in atTop, |rho.im| < T n :=
      hT.eventually (eventually_gt_atTop |rho.im|)
    apply tendsto_const_nhds.congr'
    filter_upwards [hheight] with n hn
    have hinside :
        riemannXiZeroStrictlyInsideRectangle (1 - c) c (-T n) (T n) p := by
      unfold riemannXiZeroStrictlyInsideRectangle
      dsimp only [rho] at hre0 hre1 hn ⊢
      rw [abs_lt] at hn
      constructor
      · linarith
      · constructor
        · linarith
        · constructor <;> linarith
    simp only [f, g, if_pos hinside]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ p : RiemannXiDivisorZeroIndex,
      ‖f n p‖ ≤ ‖g p‖ := by
    filter_upwards [] with n
    intro p
    by_cases hinside :
        riemannXiZeroStrictlyInsideRectangle (1 - c) c (-T n) (T n) p
    · simp only [f, g, if_pos hinside]
      exact le_rfl
    · simp only [f, g, if_neg hinside, norm_zero, norm_nonneg]
  have hlim :
      Tendsto (fun n => ∑' p : RiemannXiDivisorZeroIndex, f n p) atTop
        (𝓝 (∑' p : RiemannXiDivisorZeroIndex, g p)) :=
    tendsto_tsum_of_dominated_convergence
      (summable_riemannXiGaussianWeight ha).norm hpoint hbound
  have heq :
      (fun n => ∑' p : RiemannXiDivisorZeroIndex, f n p) =
        fun n => ∑ᶠ p : RiemannXiDivisorZeroIndex, f n p := by
    funext n
    rw [tsum_eq_finsum]
    exact hasFiniteSupport_gaussianXiRectangleZeroCutoff
      a (1 - c) c (-T n) (T n)
  rw [← heq]
  exact hlim

/-- The finite Gaussian zero sum on the selected zero-free rectangles converges to the absolute
multiplicity-bearing global Gaussian zero sum. -/
theorem tendsto_selectedGaussianXiRectangleZeroFinsum
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (gaussianXiRectangleZeroFinsum a c) atTop
      (𝓝 (∑' p : RiemannXiDivisorZeroIndex,
        riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) := by
  have heq : gaussianXiRectangleZeroFinsum a c = fun n =>
      ∑ᶠ p : RiemannXiDivisorZeroIndex,
        if riemannXiZeroStrictlyInsideRectangle
            (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p then
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)
        else 0 := by
    rfl
  rw [heq]
  exact tendsto_gaussianXiRectangleZeroFinsum ha hc
    (tendsto_gaussianXiSelectedHeight c)

/-- Along the selected zero-free heights, the right vertical integral converges to `pi` times
the absolute Gaussian xi-zero sum. -/
theorem tendsto_gaussianXiRightVerticalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (gaussianXiRightVerticalIntegral a c) atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) := by
  have htop := (tendsto_gaussianXiTopHorizontalIntegral ha hc).const_mul (-I)
  have hzero := (tendsto_selectedGaussianXiRectangleZeroFinsum ha hc).const_mul
    (Real.pi : ℂ)
  have hcombined :
      Tendsto
        (fun n : ℕ =>
          -I * gaussianXiTopHorizontalIntegral a c n +
            (Real.pi : ℂ) * gaussianXiRectangleZeroFinsum a c n)
        atTop
        (𝓝 ((Real.pi : ℂ) *
          ∑' p : RiemannXiDivisorZeroIndex,
            riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) := by
    simpa only [mul_zero, zero_add] using htop.add hzero
  apply hcombined.congr'
  exact Filter.Eventually.of_forall fun n =>
    (gaussianXiRightVerticalIntegral_eq_top_add_zeroFinsum hc n).symm

/-- Existential fixed-test height-limit endpoint for the Gaussian Weil campaign. The selected
heights tend to infinity, every symmetric rectangle is zero-free on its boundary, and the right
vertical integral converges to `pi` times the absolute multiplicity-bearing Gaussian zero sum. -/
theorem exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    ∃ T : ℕ → ℝ,
      Tendsto T atTop atTop ∧
      (∀ n : ℕ, ∀ p : RiemannXiDivisorZeroIndex,
        ¬riemannXiZeroOnRectangleBoundary (1 - c) c (-T n) (T n) p) ∧
      Tendsto
        (fun n : ℕ =>
          ∫ y : ℝ in -T n..T n,
            riemannXiGaussianWeight a ((c : ℂ) + y * I) *
              logDeriv riemannXi ((c : ℂ) + y * I))
        atTop
        (𝓝 ((Real.pi : ℂ) *
          ∑' p : RiemannXiDivisorZeroIndex,
            riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) := by
  refine ⟨gaussianXiSelectedHeight c, tendsto_gaussianXiSelectedHeight c, ?_, ?_⟩
  · exact fun n p => gaussianXiSelectedHeight_zeroFreeBoundary hc n p
  · exact tendsto_gaussianXiRightVerticalIntegral ha hc

end

end LeanLab.Riemann
