import LeanLab.Riemann.LiReverseCriterion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Finite power-sum spectral rigidity

This module isolates the last finite-spectral step in the function-field Riemann hypothesis.
An all-power aggregate bound controls every spectral radius despite arbitrary complex cancellation;
a reciprocal pairing then forces the critical circle.
-/

open Complex Filter Set Topology
open scoped BigOperators Topology

namespace LeanLab.Riemann

noncomputable section

/-- The aggregate `n`-th power sum of a finite complex family. -/
def finiteComplexPowerSum {ι : Type*} [Fintype ι]
    (alpha : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i, alpha i ^ n

private def finitePowerSumUnitPhase (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    have hnormPos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnorm : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hnormPos, div_self hnormPos.ne']
    simpa [Submonoid.unitSphere] using mem_sphere_zero_iff_norm.mpr hnorm⟩

@[simp]
private theorem coe_finitePowerSumUnitPhase (z : ℂ) (hz : z ≠ 0) :
    (finitePowerSumUnitPhase z hz : ℂ) = z / (‖z‖ : ℂ) :=
  rfl

private theorem three_quarters_mul_norm_pow_lt_re_pow
    (z : ℂ) (hz : z ≠ 0) (n : ℕ)
    (hphase : dist (finitePowerSumUnitPhase z hz ^ n) 1 < 1 / 4) :
    3 / 4 * ‖z‖ ^ n < (z ^ n).re := by
  let u := finitePowerSumUnitPhase z hz
  have hnormPos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdist : ‖((u ^ n : Circle) : ℂ) - 1‖ < 1 / 4 := by
    have hphaseU : dist (u ^ n) 1 < 1 / 4 := by
      simpa only [u] using hphase
    change dist (((u ^ n : Circle) : ℂ)) ((1 : Circle) : ℂ) < 1 / 4 at hphaseU
    simpa only [Circle.coe_one, Complex.dist_eq] using hphaseU
  have hrePhase : 3 / 4 < (((u ^ n : Circle) : ℂ)).re := by
    have habs := Complex.abs_re_le_norm ((((u ^ n : Circle) : ℂ)) - 1)
    have hlt := habs.trans_lt hdist
    simp only [Complex.sub_re, Complex.one_re] at hlt
    linarith [(abs_lt.mp hlt).1]
  have hrecover : z = (‖z‖ : ℂ) * (u : ℂ) := by
    change z = (‖z‖ : ℂ) * (finitePowerSumUnitPhase z hz : ℂ)
    rw [coe_finitePowerSumUnitPhase]
    field_simp [hnormPos.ne']
  have hmul := mul_lt_mul_of_pos_left hrePhase (pow_pos hnormPos n)
  have hpow := congrArg (fun w : ℂ ↦ w ^ n) hrecover
  rw [mul_pow] at hpow
  have hpowRe : (z ^ n).re = ‖z‖ ^ n * (((u ^ n : Circle) : ℂ)).re := by
    rw [hpow, ← Complex.ofReal_pow, ← Circle.coe_pow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hpowRe]
  simpa only [mul_comm] using hmul

/-- An all-power aggregate bound controls every member of a finite complex spectrum. -/
theorem norm_le_of_forall_norm_finiteComplexPowerSum_le
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖finiteComplexPowerSum alpha n‖ ≤ C * R ^ n) :
    ∀ i, ‖alpha i‖ ≤ R := by
  have hCnonneg : 0 ≤ C := hC
  intro i₀
  by_contra hi₀
  have hRi₀ : R < ‖alpha i₀‖ := lt_of_not_ge hi₀
  have hi₀ne : alpha i₀ ≠ 0 := by
    rw [← norm_pos_iff]
    exact hR.trans hRi₀
  let r : ℝ := ‖alpha i₀‖ / R
  have hr : 1 < r := (one_lt_div hR).2 hRi₀
  have hgrowth : ∀ᶠ n : ℕ in atTop, (4 / 3 : ℝ) * C < r ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop ((4 / 3 : ℝ) * C)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgrowth
  let nz := {i : ι // alpha i ≠ 0}
  let phase : nz → Circle := fun i ↦ finitePowerSumUnitPhase (alpha i) i.property
  obtain ⟨n, hnN, _hnEven, hphase⟩ :=
    exists_even_gt_forall_circle_pow_dist_one_lt phase N
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hRpow : 0 < R ^ n := pow_pos hR n
  have hrpow : (4 / 3 : ℝ) * C < r ^ n := hN n hnN.le
  have hrecoverPow : r ^ n * R ^ n = ‖alpha i₀‖ ^ n := by
    dsimp only [r]
    rw [div_pow]
    field_simp [hR.ne']
  have hdominates : C * R ^ n < 3 / 4 * ‖alpha i₀‖ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hrpow hRpow
    rw [hrecoverPow] at hmul
    nlinarith [hCnonneg]
  have htermNonneg (i : ι) : 0 ≤ (alpha i ^ n).re := by
    by_cases hi : alpha i = 0
    · by_cases hn : n = 0 <;> simp [hi, hn]
    · have hstrict := three_quarters_mul_norm_pow_lt_re_pow (alpha i) hi n
          (hphase ⟨i, hi⟩)
      have hleft : 0 ≤ 3 / 4 * ‖alpha i‖ ^ n := by positivity
      linarith
  have hi₀Phase :
      dist (finitePowerSumUnitPhase (alpha i₀) hi₀ne ^ n) 1 < 1 / 4 :=
    hphase ⟨i₀, hi₀ne⟩
  have hi₀Strict :=
    three_quarters_mul_norm_pow_lt_re_pow (alpha i₀) hi₀ne n hi₀Phase
  have hsingle : (alpha i₀ ^ n).re ≤ ∑ i, (alpha i ^ n).re :=
    Finset.single_le_sum (fun i _hi ↦ htermNonneg i) (Finset.mem_univ i₀)
  have hsumRe : 3 / 4 * ‖alpha i₀‖ ^ n < (finiteComplexPowerSum alpha n).re := by
    rw [finiteComplexPowerSum, Complex.re_sum]
    exact hi₀Strict.trans_le hsingle
  have hreNorm : (finiteComplexPowerSum alpha n).re ≤ ‖finiteComplexPowerSum alpha n‖ :=
    Complex.re_le_norm _
  have hcontra : C * R ^ n < ‖finiteComplexPowerSum alpha n‖ :=
    hdominates.trans (hsumRe.trans_le hreNorm)
  exact (not_lt_of_ge (hbound n)) hcontra

/-- A reciprocal pairing upgrades the power-sum radius bound to the exact critical circle. -/
theorem norm_eq_sqrt_of_powerSum_bound_and_reciprocal
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (sigma : Equiv.Perm ι)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hpair : ∀ i, alpha (sigma i) * alpha i = (q : ℂ))
    (hbound : ∀ n : ℕ,
      ‖finiteComplexPowerSum alpha n‖ ≤ C * Real.sqrt q ^ n) :
    ∀ i, ‖alpha i‖ = Real.sqrt q := by
  have hsqrtPos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hle : ∀ i, ‖alpha i‖ ≤ Real.sqrt q :=
    norm_le_of_forall_norm_finiteComplexPowerSum_le alpha hsqrtPos hC hbound
  intro i
  have hpairNorm : ‖alpha (sigma i)‖ * ‖alpha i‖ = q := by
    rw [← norm_mul, hpair, norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hsqrtSq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
  nlinarith [norm_nonneg (alpha i), norm_nonneg (alpha (sigma i)), hle i, hle (sigma i)]

end

end LeanLab.Riemann
