import LeanLab.Riemann.AnalyticLogBranch
import LeanLab.Riemann.ZetaConvexity
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option linter.style.header false

/-!
# Reciprocal-zeta subpower growth under RH

This module formalizes the reciprocal-zeta growth input in Titchmarsh Theorem 14.2. It is a
source-proof dependency of the Balazard-Saias Mobius partial-sum estimate.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped LSeries.notation

namespace LeanLab.Riemann

/-- A uniform polynomial estimate on the bounded real strip containing the Borel circles in
Titchmarsh's proof. The deliberately coarse linear exponent is sufficient because
Borel-Caratheodory only uses its logarithm. -/
theorem norm_riemannZeta_le_linear_of_re_mem_Icc
    {s : ℂ} (hre : s.re ∈ Set.Icc (1 / 2 : ℝ) 8) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 20 * (1 + |s.im|) := by
  have hs_ne : s ≠ 1 := by
    intro hs
    have hs_im := congrArg Complex.im hs
    norm_num at hs_im
    rw [hs_im, abs_zero] at him
    norm_num at him
  have hs_mem : s ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hs_ne
      (zetaAbelContinuationReLower_lt_half.trans_le (by
        simpa [one_div] using hre.1))
  have hformula := riemannZeta_eq_zetaPartialSum_sub_tail s hs_mem 1 (by norm_num)
  norm_num only [Nat.cast_one] at hformula
  have hpartial : zetaPartialSum s 1 = 1 := by
    simp [zetaPartialSum]
  have hpole : ‖(1 : ℂ) ^ (1 - s) / (1 - s)‖ ≤ 1 := by
    rw [Complex.one_cpow, norm_div, norm_one]
    have him_le : |s.im| ≤ ‖(1 : ℂ) - s‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - s)
      simpa using h
    exact (div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne.symm))).2
      (him.trans him_le)
  let measureOne := volume.restrict (Set.Ioi (1 : ℝ))
  let g : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  have hexp : -s.re - 1 < -1 := by linarith [hre.1]
  have hg : Integrable g measureOne := by
    simpa [measureOne, g, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (a := -s.re - 1) hexp (by norm_num))
  have hbound : ∀ᵐ u ∂measureOne, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    exact norm_zetaAbelFractKernel_le u hu.le s
  have hint :
      ‖∫ u in Set.Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ 2 := by
    calc
      ‖∫ u in Set.Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ∫ u in Set.Ioi (1 : ℝ), g u :=
        MeasureTheory.norm_integral_le_of_norm_le hg hbound
      _ = 1 / s.re := by
        change (∫ u in Set.Ioi (1 : ℝ), u ^ (-s.re - 1)) = 1 / s.re
        rw [integral_Ioi_rpow_of_lt (a := -s.re - 1) hexp (by norm_num)]
        rw [Real.one_rpow]
        field_simp [show s.re ≠ 0 by linarith [hre.1]]
        ring
      _ ≤ 2 := by
        rw [div_le_iff₀ (by linarith [hre.1])]
        linarith [hre.1]
  have hs_norm : ‖s‖ ≤ 8 + |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 8 + |s.im| := by
        rw [abs_of_nonneg (by linarith [hre.1] : 0 ≤ s.re)]
        linarith [hre.2]
  rw [hformula, hpartial]
  calc
    ‖(1 : ℂ) - (1 : ℂ) ^ (1 - s) / (1 - s) -
          s * ∫ u in Set.Ioi (1 : ℝ), zetaAbelFractKernel s u‖
        ≤ 1 + ‖(1 : ℂ) ^ (1 - s) / (1 - s)‖ +
            ‖s‖ * ‖∫ u in Set.Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
      grw [norm_sub_le, norm_sub_le, norm_mul]
      norm_num
    _ ≤ 1 + 1 + (8 + |s.im|) * 2 := by gcongr
    _ ≤ 20 * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]

/-- In the absolute-convergence half-plane `Re(s) >= 3`, zeta stays in a fixed ball strictly
inside the open unit ball about `1`. This supplies the bounded right-hand logarithm circle in the
three-circles argument. -/
theorem norm_riemannZeta_sub_one_lt_three_fourths_of_three_le_re
    {s : ℂ} (hre : 3 ≤ s.re) :
    ‖riemannZeta s - 1‖ < 3 / 4 := by
  have hs : 1 < s.re := lt_of_lt_of_le (by norm_num) hre
  let f : ℕ → ℂ := fun n => 1 / (n + 1 : ℂ) ^ s
  have hfsum : Summable f := by
    simpa [f, Function.comp_def] using
      (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective
  have hzeta : riemannZeta s = 1 + ∑' n : ℕ, f (n + 1) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have hsplit := hfsum.sum_add_tsum_nat_add 1
    simpa [f] using hsplit.symm
  let g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hgsum : Summable g := hasSum_zeta_two.summable
  have hgtail : ∑' n : ℕ, g (n + 2) = Real.pi ^ 2 / 6 - 1 := by
    have hsplit := hgsum.sum_add_tsum_nat_add 2
    rw [hasSum_zeta_two.tsum_eq] at hsplit
    norm_num [g] at hsplit ⊢
    linarith
  have hterm : ∀ n : ℕ, ‖f (n + 1)‖ ≤ g (n + 2) := by
    intro n
    have hn_pos : 0 < n + 2 := by omega
    have hn_one : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
    simp only [f, g, norm_div, norm_one]
    have hcast : ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    rw [Complex.norm_natCast_cpow_of_pos hn_pos]
    rw [one_div, one_div]
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
        ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hn_one (by linarith [hre])
    have hpow' : ((n + 2 : ℕ) : ℝ) ^ (2 : ℕ) ≤
        ((n + 2 : ℕ) : ℝ) ^ s.re := by
      simpa only [Real.rpow_two] using hpow
    exact inv_anti₀ (by positivity) hpow'
  have htail_sum : Summable fun n : ℕ => ‖f (n + 1)‖ := by
    exact (hgsum.comp_injective (fun _ _ h => by omega)).of_nonneg_of_le
      (fun _ => norm_nonneg _) hterm
  have hgtail_sum : Summable fun n : ℕ => g (n + 2) :=
    hgsum.comp_injective (fun _ _ h => by omega)
  have hpi : Real.pi ^ 2 / 6 < 7 / 4 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  rw [hzeta, add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ :=
      norm_tsum_le_tsum_norm htail_sum
    _ ≤ ∑' n : ℕ, g (n + 2) :=
      htail_sum.tsum_le_tsum hterm hgtail_sum
    _ = Real.pi ^ 2 / 6 - 1 := hgtail
    _ < 3 / 4 := by linarith

/-- The principal logarithm of zeta is uniformly bounded in `Re(s) >= 3`. -/
theorem norm_log_riemannZeta_le_two_of_three_le_re
    {s : ℂ} (hre : 3 ≤ s.re) :
    ‖Complex.log (riemannZeta s)‖ ≤ 2 := by
  have hdist := norm_riemannZeta_sub_one_lt_three_fourths_of_three_le_re hre
  let r : ℝ := ‖riemannZeta s - 1‖
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hr_lt_one : r < 1 := by dsimp only [r]; linarith
  have hr_le : r ≤ 3 / 4 := by dsimp only [r]; exact hdist.le
  have hinv : (1 - r)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rw [show riemannZeta s = 1 + (riemannZeta s - 1) by ring]
  calc
    ‖Complex.log (1 + (riemannZeta s - 1))‖
        ≤ r ^ 2 * (1 - r)⁻¹ / 2 + r := by
      simpa only [r] using Complex.norm_log_one_add_le hr_lt_one
    _ ≤ (3 / 4 : ℝ) ^ 2 * 4 / 2 + 3 / 4 := by
      gcongr
    _ ≤ 2 := by norm_num

/-- Center of the local Borel and three-circles argument. -/
def reciprocalZetaBorelCenter (t : ℝ) : ℂ := (4 : ℂ) + t * Complex.I

/-- On the horizontal line through the Borel center, points in the critical strip have purely
real displacement from that center. -/
theorem norm_sub_reciprocalZetaBorelCenter_eq
    {s : ℂ} {t : ℝ} (hsim : s.im = t) (hsre : s.re ≤ 1) :
    ‖s - reciprocalZetaBorelCenter t‖ = 4 - s.re := by
  let c := reciprocalZetaBorelCenter t
  have hc_re : c.re = 4 := by simp [c, reciprocalZetaBorelCenter]
  have hc_im : c.im = t := by simp [c, reciprocalZetaBorelCenter]
  change ‖s - c‖ = 4 - s.re
  rw [Complex.norm_def, Complex.normSq_apply]
  have hre : (s - c).re = s.re - 4 := by simp [hc_re]
  have him : (s - c).im = 0 := by simp [hc_im, hsim]
  rw [hre, him]
  simp only [mul_zero, add_zero]
  rw [← pow_two, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Radius of the zero-free outer Borel circle. Its left edge is `1/2 + delta/2`. -/
def reciprocalZetaBorelOuterRadius (delta : ℝ) : ℝ := 7 / 2 - delta / 2

/-- Radius of the inner Borel circle. Its left edge is `1/2 + delta`. -/
def reciprocalZetaBorelInnerRadius (delta : ℝ) : ℝ := 7 / 2 - delta

/-- Interpolation exponent between the fixed radius `1/2` and the inner Borel radius produced
with parameter `delta / 2`. -/
def reciprocalZetaThreeCirclesExponent (delta rho : ℝ) : ℝ :=
  (Real.log rho - Real.log (1 / 2 : ℝ)) /
    (Real.log (reciprocalZetaBorelInnerRadius (delta / 2)) - Real.log (1 / 2 : ℝ))

/-- The largest interpolation exponent needed on `Re(s) >= 1/2 + delta`. -/
def reciprocalZetaThreeCirclesMaxExponent (delta : ℝ) : ℝ :=
  reciprocalZetaThreeCirclesExponent delta (7 / 2 - delta)

/-- The radial gap created by the `delta / 2` Borel disk makes the maximum interpolation
exponent strictly smaller than one. -/
theorem reciprocalZetaThreeCirclesExponent_bounds
    {delta rho : ℝ} (hdelta : 0 < delta) (hdelta_le : delta ≤ 1 / 2)
    (hrho_lower : 1 / 2 ≤ rho) (hrho_upper : rho ≤ 7 / 2 - delta) :
    0 ≤ reciprocalZetaThreeCirclesExponent delta rho ∧
      reciprocalZetaThreeCirclesExponent delta rho ≤
        reciprocalZetaThreeCirclesMaxExponent delta ∧
      reciprocalZetaThreeCirclesMaxExponent delta < 1 := by
  let r₁ : ℝ := 1 / 2
  let r₂ : ℝ := 7 / 2 - delta
  let r₃ := reciprocalZetaBorelInnerRadius (delta / 2)
  have hr₁_pos : 0 < r₁ := by norm_num [r₁]
  have hr₂_pos : 0 < r₂ := by dsimp only [r₂]; linarith
  have hr₃_pos : 0 < r₃ := by
    dsimp only [r₃, reciprocalZetaBorelInnerRadius]
    linarith
  have hr₁r₃ : r₁ < r₃ := by
    dsimp only [r₁, r₃, reciprocalZetaBorelInnerRadius]
    linarith
  have hr₂r₃ : r₂ < r₃ := by
    dsimp only [r₂, r₃, reciprocalZetaBorelInnerRadius]
    linarith
  have hrho_pos : 0 < rho := hr₁_pos.trans_le hrho_lower
  have hlog₁rho : Real.log r₁ ≤ Real.log rho :=
    Real.strictMonoOn_log.monotoneOn hr₁_pos hrho_pos hrho_lower
  have hlogrho₂ : Real.log rho ≤ Real.log r₂ :=
    Real.strictMonoOn_log.monotoneOn hrho_pos hr₂_pos hrho_upper
  have hlog₂₃ : Real.log r₂ < Real.log r₃ :=
    Real.strictMonoOn_log hr₂_pos hr₃_pos hr₂r₃
  have hden : 0 < Real.log r₃ - Real.log r₁ := by
    have := Real.strictMonoOn_log hr₁_pos hr₃_pos hr₁r₃
    linarith
  change 0 ≤ (Real.log rho - Real.log r₁) / (Real.log r₃ - Real.log r₁) ∧
    (Real.log rho - Real.log r₁) / (Real.log r₃ - Real.log r₁) ≤
      (Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁) ∧
    (Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁) < 1
  refine ⟨div_nonneg (sub_nonneg.mpr hlog₁rho) hden.le, ?_, ?_⟩
  · exact (div_le_div_iff_of_pos_right hden).2 (by linarith)
  · rw [div_lt_one hden]
    linarith

/-- A real power with exponent strictly below one is eventually dominated by any positive
multiple of the identity. -/
theorem eventually_const_mul_rpow_le_mul_self
    {K theta eta : ℝ} (htheta : theta < 1) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in Filter.atTop, K * x ^ theta ≤ eta * x := by
  have hgap : 0 < 1 - theta := sub_pos.mpr htheta
  have hpow : ∀ᶠ x : ℝ in Filter.atTop, K / eta ≤ x ^ (1 - theta) :=
    (tendsto_rpow_atTop hgap).eventually (Filter.eventually_ge_atTop (K / eta))
  filter_upwards [hpow, Filter.eventually_gt_atTop (0 : ℝ)] with x hx hxp
  have hK : K ≤ eta * x ^ (1 - theta) := by
    have h := (div_le_iff₀ heta).mp hx
    simpa only [mul_comm] using h
  have hpower_nonneg : 0 ≤ x ^ theta := Real.rpow_nonneg hxp.le _
  calc
    K * x ^ theta ≤ (eta * x ^ (1 - theta)) * x ^ theta :=
      mul_le_mul_of_nonneg_right hK hpower_nonneg
    _ = eta * x := by
      rw [mul_assoc, ← Real.rpow_add hxp]
      ring_nf
      rw [Real.rpow_one]

/-- Reciprocal zeta is bounded in a neighborhood of its pole. This includes Mathlib's junk value
at `s = 1`, which is nonzero but does not make the reciprocal function continuous there. -/
theorem exists_norm_reciprocal_riemannZeta_le_near_one :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, dist s 1 < epsilon → ‖(riemannZeta s)⁻¹‖ ≤ C := by
  have hevent :
      {s : ℂ | ‖(s - 1) * riemannZeta s - 1‖ < (1 / 2 : ℝ)} ∈
        nhdsWithin (1 : ℂ) ({(1 : ℂ)} : Set ℂ)ᶜ := by
    have h := riemannZeta_residue_one.eventually
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    change ∀ᶠ s : ℂ in nhdsWithin (1 : ℂ) ({(1 : ℂ)} : Set ℂ)ᶜ,
      ‖(s - 1) * riemannZeta s - 1‖ < (1 / 2 : ℝ)
    simpa only [Metric.mem_ball, dist_eq_norm] using h
  rw [Metric.mem_nhdsWithin_iff] at hevent
  obtain ⟨epsilon, hepsilon, hevent⟩ := hevent
  let C := max 1 (max (2 * epsilon) ‖(riemannZeta (1 : ℂ))⁻¹‖)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨epsilon, hepsilon, C, hC, ?_⟩
  intro s hs
  by_cases hs_one : s = 1
  · subst s
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hs_compl : s ∈ ({(1 : ℂ)} : Set ℂ)ᶜ := by simpa
  have hclose := hevent ⟨hs, hs_compl⟩
  let P := (s - 1) * riemannZeta s
  change ‖P - 1‖ < (1 / 2 : ℝ) at hclose
  have hP : 1 / 2 < ‖P‖ := by
    have htri : (1 : ℝ) ≤ ‖P - 1‖ + ‖P‖ := by
      simpa only [norm_one, add_comm, norm_sub_rev] using
        (norm_le_norm_add_norm_sub P (1 : ℂ))
    linarith
  have hP_ne : P ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hP)
  have hzeta_ne : riemannZeta s ≠ 0 := by
    intro hz
    apply hP_ne
    simp [P, hz]
  have hnorm_eq : ‖(riemannZeta s)⁻¹‖ = ‖s - 1‖ / ‖P‖ := by
    dsimp only [P]
    rw [norm_inv, norm_mul]
    field_simp [norm_ne_zero_iff.mpr hzeta_ne, norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs_one)]
  have hnear : ‖(riemannZeta s)⁻¹‖ ≤ 2 * epsilon := by
    rw [hnorm_eq, div_le_iff₀ (lt_trans (by norm_num) hP)]
    rw [dist_eq_norm] at hs
    nlinarith [norm_nonneg (s - 1)]
  exact hnear.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- Hadamard's three-circles estimate, obtained from Mathlib's three-lines theorem by the
exponential map. The slightly stronger differentiability hypothesis on a larger open disk is
tailored to the local logarithm branches used below. -/
theorem norm_le_three_circles_of_differentiableOn_ball
    {f : ℂ → ℂ} {c z : ℂ} {r₁ r₃ R a b : ℝ}
    (hr₁ : 0 < r₁) (hr₁r₃ : r₁ < r₃) (hr₃R : r₃ < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (ha : ∀ x ∈ Metric.closedBall c r₁, ‖f x‖ ≤ a)
    (hb : ∀ x ∈ Metric.closedBall c r₃, ‖f x‖ ≤ b)
    (hz₁ : r₁ ≤ ‖z - c‖) (hz₃ : ‖z - c‖ ≤ r₃) :
    ‖f z‖ ≤
      a ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      b ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  let l := Real.log r₁
  let u := Real.log r₃
  let F : ℂ → ℂ := fun w => f (c + Complex.exp w)
  have hr₃_pos : 0 < r₃ := hr₁.trans hr₁r₃
  have hlu : l < u := by
    dsimp only [l, u]
    exact Real.strictMonoOn_log hr₁ hr₃_pos hr₁r₃
  have hclosed_subset : Metric.closedBall c r₃ ⊆ Metric.ball c R := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr₃R)
  have hf_ball : DiffContOnCl ℂ f (Metric.ball c r₃) :=
    hf.diffContOnCl_ball hclosed_subset
  have hinner_diff : Differentiable ℂ (fun w : ℂ => c + Complex.exp w) := by fun_prop
  have hmap : MapsTo (fun w : ℂ => c + Complex.exp w)
      (Complex.HadamardThreeLines.verticalStrip l u) (Metric.ball c r₃) := by
    intro w hw
    rw [Complex.HadamardThreeLines.verticalStrip] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_exp]
    rw [← Real.exp_log hr₃_pos, Real.exp_lt_exp]
    exact hw.2
  have hF_diff : DiffContOnCl ℂ F
      (Complex.HadamardThreeLines.verticalStrip l u) := by
    change DiffContOnCl ℂ (f ∘ fun w : ℂ => c + Complex.exp w)
      (Complex.HadamardThreeLines.verticalStrip l u)
    exact hf_ball.comp hinner_diff.diffContOnCl hmap
  have hF_bdd : BddAbove ((norm ∘ F) ''
      Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    rw [bddAbove_def]
    refine ⟨b, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_exp]
    rw [← Real.exp_log hr₃_pos, Real.exp_le_exp]
    exact hw.2
  have hF_left : ∀ w ∈ Complex.re ⁻¹' {l}, ‖F w‖ ≤ a := by
    intro w hw
    apply ha
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_exp]
    have hwre : w.re = l := hw
    rw [hwre]
    exact (Real.exp_log hr₁).le
  have hF_right : ∀ w ∈ Complex.re ⁻¹' {u}, ‖F w‖ ≤ b := by
    intro w hw
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_exp]
    have hwre : w.re = u := hw
    rw [hwre]
    exact (Real.exp_log hr₃_pos).le
  have hz_norm_pos : 0 < ‖z - c‖ := hr₁.trans_le hz₁
  have hz_ne : z - c ≠ 0 := norm_pos_iff.mp hz_norm_pos
  let w := Complex.log (z - c)
  have hw_re : w.re = Real.log ‖z - c‖ := by
    exact Complex.log_re (z - c)
  have hw_mem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
    rw [Complex.HadamardThreeLines.verticalClosedStrip]
    change w.re ∈ Set.Icc l u
    rw [hw_re]
    constructor
    · dsimp only [l]
      exact Real.strictMonoOn_log.monotoneOn hr₁ hz_norm_pos hz₁
    · dsimp only [u]
      exact Real.strictMonoOn_log.monotoneOn hz_norm_pos hr₃_pos hz₃
  have hHadamard := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlu hw_mem hF_diff hF_bdd hF_left hF_right
  have hFw : F w = f z := by
    change f (c + Complex.exp (Complex.log (z - c))) = f z
    rw [Complex.exp_log hz_ne]
    congr 1
    ring
  rw [hFw, hw_re] at hHadamard
  simpa only [l, u] using hHadamard

/-- Under RH, the logarithm branch on Titchmarsh's outer Borel disk can be normalized to the
principal logarithm at the center. It then agrees with the principal logarithm on the right-hand
unit disk and is uniformly bounded on the closed disk of radius `1/2`. -/
theorem RiemannHypothesis.exists_normalized_logBranch_on_borelBall
    (hRH : RiemannHypothesis) {delta t : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2)
    (ht : 5 ≤ |t|) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f
          (Metric.ball (reciprocalZetaBorelCenter t) (reciprocalZetaBorelOuterRadius delta)) ∧
      Set.EqOn (Complex.exp ∘ f) riemannZeta
          (Metric.ball (reciprocalZetaBorelCenter t) (reciprocalZetaBorelOuterRadius delta)) ∧
      f (reciprocalZetaBorelCenter t) =
          Complex.log (riemannZeta (reciprocalZetaBorelCenter t)) ∧
      Set.EqOn f (fun z => Complex.log (riemannZeta z))
          (Metric.ball (reciprocalZetaBorelCenter t) 1) ∧
      ∀ z ∈ Metric.closedBall (reciprocalZetaBorelCenter t) (1 / 2 : ℝ), ‖f z‖ ≤ 2 := by
  let c := reciprocalZetaBorelCenter t
  let R := reciprocalZetaBorelOuterRadius delta
  have hR_pos : 0 < R := by dsimp only [R, reciprocalZetaBorelOuterRadius]; linarith
  have hR_lt_four : R < 4 := by dsimp only [R, reciprocalZetaBorelOuterRadius]; linarith
  have hR_one : 1 < R := by dsimp only [R, reciprocalZetaBorelOuterRadius]; linarith
  have hone : (1 : ℂ) ∉ Metric.ball c R := by
    intro hone_mem
    have hdist := Metric.mem_ball.mp hone_mem
    have him_le := Complex.abs_im_le_norm ((1 : ℂ) - c)
    have hc_im : c.im = t := by simp [c, reciprocalZetaBorelCenter]
    rw [dist_eq_norm] at hdist
    have : |t| ≤ ‖(1 : ℂ) - c‖ := by
      simpa [hc_im] using him_le
    linarith
  have hzero : ∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 := by
    intro z hz
    have hdist := Metric.mem_ball.mp hz
    have hre_abs := Complex.abs_re_le_norm (z - c)
    have hc_re : c.re = 4 := by simp [c, reciprocalZetaBorelCenter]
    rw [dist_eq_norm] at hdist
    have hz_re : (1 / 2 : ℝ) < z.re := by
      have hR_eq : R = 7 / 2 - delta / 2 := rfl
      simp [hc_re] at hre_abs
      linarith [neg_abs_le (z.re - 4)]
    exact RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) hz_re
  letI : ContractibleSpace (Metric.ball c R) := Metric.contractibleSpace_ball hR_pos
  have hsimple : IsSimplyConnected (Metric.ball c R) := by
    change SimplyConnectedSpace (Metric.ball c R)
    infer_instance
  obtain ⟨f₀, hf₀_diff, hf₀_exp, hf₀_deriv⟩ :=
    exists_riemannZeta_differentiableLogBranch hsimple Metric.isOpen_ball hone hzero
  let f : ℂ → ℂ := fun z =>
    f₀ z - f₀ c + Complex.log (riemannZeta c)
  have hc_mem : c ∈ Metric.ball c R := Metric.mem_ball_self hR_pos
  have hc_zero : riemannZeta c ≠ 0 := hzero c hc_mem
  have hf_diff : DifferentiableOn ℂ f (Metric.ball c R) := by
    exact (hf₀_diff.sub (differentiableOn_const (c := f₀ c))).add
      (differentiableOn_const (c := Complex.log (riemannZeta c)))
  have hf_exp : Set.EqOn (Complex.exp ∘ f) riemannZeta (Metric.ball c R) := by
    intro z hz
    have hz_exp : Complex.exp (f₀ z) = riemannZeta z := by
      simpa [Function.comp_apply] using hf₀_exp hz
    have hc_exp : Complex.exp (f₀ c) = riemannZeta c := by
      simpa [Function.comp_apply] using hf₀_exp hc_mem
    change Complex.exp (f₀ z - f₀ c + Complex.log (riemannZeta c)) = riemannZeta z
    rw [Complex.exp_add, Complex.exp_sub, hz_exp, hc_exp,
      Complex.exp_log hc_zero]
    field_simp
  have hf_center : f c = Complex.log (riemannZeta c) := by simp [f]
  have hsmall_subset : Metric.ball c 1 ⊆ Metric.ball c R :=
    Metric.ball_subset_ball hR_one.le
  have hprincipal_slit :
      ∀ z ∈ Metric.ball c 1, riemannZeta z ∈ Complex.slitPlane := by
    intro z hz
    have hdist := Metric.mem_ball.mp hz
    have hre_abs := Complex.abs_re_le_norm (z - c)
    have hc_re : c.re = 4 := by simp [c, reciprocalZetaBorelCenter]
    rw [dist_eq_norm] at hdist
    simp [hc_re] at hre_abs
    have hz_re : 3 ≤ z.re := by linarith [neg_abs_le (z.re - 4)]
    have hclose := norm_riemannZeta_sub_one_lt_three_fourths_of_three_le_re hz_re
    rw [show riemannZeta z = 1 + (riemannZeta z - 1) by ring]
    exact Complex.mem_slitPlane_of_norm_lt_one (hclose.trans (by norm_num))
  have hprincipal_diff :
      DifferentiableOn ℂ (fun z => Complex.log (riemannZeta z)) (Metric.ball c 1) := by
    have hzeta_diff : DifferentiableOn ℂ riemannZeta (Metric.ball c 1) := by
      intro z hz
      have hz1 : z ≠ 1 := by
        intro h
        subst z
        exact hone (hsmall_subset hz)
      exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
    exact hzeta_diff.clog hprincipal_slit
  have hf_deriv : ∀ z ∈ Metric.ball c R,
      HasDerivAt f (deriv riemannZeta z / riemannZeta z) z := by
    intro z hz
    simpa only [f] using (hf₀_deriv z hz).sub_const (f₀ c) |>.add_const
      (Complex.log (riemannZeta c))
  have hprincipal_deriv : ∀ z ∈ Metric.ball c 1,
      HasDerivAt (fun w => Complex.log (riemannZeta w))
        (deriv riemannZeta z / riemannZeta z) z := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      exact hone (hsmall_subset hz)
    exact (differentiableAt_riemannZeta hz1).hasDerivAt.clog (hprincipal_slit z hz)
  have hf_eq_principal :
      Set.EqOn f (fun z => Complex.log (riemannZeta z)) (Metric.ball c 1) := by
    apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball c 1).isPreconnected
      (hf_diff.mono hsmall_subset) hprincipal_diff
    · intro z hz
      exact (hf_deriv z (hsmall_subset hz)).deriv.trans (hprincipal_deriv z hz).deriv.symm
    · exact Metric.mem_ball_self (by norm_num)
    · exact hf_center
  refine ⟨f, hf_diff, hf_exp, hf_center, hf_eq_principal, ?_⟩
  intro z hz
  change z ∈ Metric.closedBall c (1 / 2 : ℝ) at hz
  have hz_small : z ∈ Metric.ball c 1 := by
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by norm_num))
  rw [hf_eq_principal hz_small]
  change ‖Complex.log (riemannZeta z)‖ ≤ 2
  have hdist := Metric.mem_closedBall.mp hz
  have hre_abs := Complex.abs_re_le_norm (z - c)
  have hc_re : c.re = 4 := by simp [c, reciprocalZetaBorelCenter]
  rw [dist_eq_norm] at hdist
  simp [hc_re] at hre_abs
  apply norm_log_riemannZeta_le_two_of_three_le_re
  linarith [neg_abs_le (z.re - 4)]

/-- Borel-Caratheodory bounds a normalized logarithm branch by `O_delta(log |t|)` on the inner
circle. This is the first quantitative half of Titchmarsh's three-circles argument. -/
theorem RiemannHypothesis.exists_logBranch_borel_bound
    (hRH : RiemannHypothesis) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) :
    ∀ t : ℝ, 5 ≤ |t| →
      ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f
            (Metric.ball (reciprocalZetaBorelCenter t)
              (reciprocalZetaBorelOuterRadius delta)) ∧
        Set.EqOn (Complex.exp ∘ f) riemannZeta
            (Metric.ball (reciprocalZetaBorelCenter t)
              (reciprocalZetaBorelOuterRadius delta)) ∧
        (∀ z ∈ Metric.closedBall (reciprocalZetaBorelCenter t) (1 / 2 : ℝ), ‖f z‖ ≤ 2) ∧
        ∀ z ∈ Metric.closedBall (reciprocalZetaBorelCenter t)
            (reciprocalZetaBorelInnerRadius delta),
          ‖f z‖ ≤ (80 / delta) * Real.log (2 + |t|) := by
  intro t ht
  obtain ⟨f, hf_diff, hf_exp, hf_center, hf_principal, hf_small⟩ :=
    RiemannHypothesis.exists_normalized_logBranch_on_borelBall
      hRH hdelta hdelta_le ht
  let c := reciprocalZetaBorelCenter t
  let R := reciprocalZetaBorelOuterRadius delta
  let r := reciprocalZetaBorelInnerRadius delta
  let M := Real.log (40 * (1 + |t|))
  let logHeight := Real.log (2 + |t|)
  have hR_pos : 0 < R := by dsimp only [R, reciprocalZetaBorelOuterRadius]; linarith
  have hR_le : R ≤ 4 := by dsimp only [R, reciprocalZetaBorelOuterRadius]; linarith
  have hR_lt_seven_halves : R < 7 / 2 := by
    dsimp only [R, reciprocalZetaBorelOuterRadius]
    linarith
  have hr_pos : 0 < r := by dsimp only [r, reciprocalZetaBorelInnerRadius]; linarith
  have hr_lt_R : r < R := by
    dsimp only [r, R, reciprocalZetaBorelInnerRadius, reciprocalZetaBorelOuterRadius]
    linarith
  have hR_sub_r : R - r = delta / 2 := by
    dsimp only [r, R, reciprocalZetaBorelInnerRadius, reciprocalZetaBorelOuterRadius]
    ring
  have hM_pos : 0 < M := by
    dsimp only [M]
    apply Real.log_pos
    nlinarith [abs_nonneg t]
  have hlogHeight_pos : 0 < logHeight := by
    dsimp only [logHeight]
    apply Real.log_pos
    linarith [abs_nonneg t]
  have hlogHeight_one : 1 ≤ logHeight := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    dsimp only [logHeight]
    rw [← Real.exp_le_exp, Real.exp_log (by linarith [abs_nonneg t])]
    linarith [ht]
  have hM_le : M ≤ 3 * logHeight := by
    have hbase_pos : 0 < 2 + |t| := by positivity
    have hpoly : 40 * (1 + |t|) ≤ (2 + |t|) ^ 3 := by
      have hsquare : 40 ≤ (2 + |t|) ^ 2 := by nlinarith [ht]
      have hone : 1 + |t| ≤ 2 + |t| := by linarith
      calc
        40 * (1 + |t|) ≤ (2 + |t|) ^ 2 * (2 + |t|) :=
          mul_le_mul hsquare hone (show 0 ≤ 1 + |t| by positivity) (sq_nonneg _)
        _ = (2 + |t|) ^ 3 := by ring
    dsimp only [M, logHeight]
    calc
      Real.log (40 * (1 + |t|)) ≤ Real.log ((2 + |t|) ^ 3) :=
        Real.strictMonoOn_log.monotoneOn
          (by change 0 < 40 * (1 + |t|); positivity)
          (by change 0 < (2 + |t|) ^ 3; positivity) hpoly
      _ = 3 * Real.log (2 + |t|) := by rw [Real.log_pow]; norm_num
  let g : ℂ → ℂ := fun w => f (c + w)
  have hmap : MapsTo (fun w : ℂ => c + w) (Metric.ball 0 R) (Metric.ball c R) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    simpa only [sub_zero, add_sub_cancel_left] using hw
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    exact hf_diff.comp (by fun_prop) hmap
  have hg_maps : MapsTo g (Metric.ball 0 R) {z : ℂ | z.re ≤ M} := by
    intro w hw
    have hcw := hmap hw
    have hw_norm : ‖w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw_re := Complex.abs_re_le_norm w
    have hw_im := Complex.abs_im_le_norm w
    have hcw_re : (c + w).re ∈ Set.Icc (1 / 2 : ℝ) 8 := by
      have hc_re : c.re = 4 := by simp [c, reciprocalZetaBorelCenter]
      simp [hc_re]
      constructor
      · linarith [neg_abs_le w.re]
      · linarith [le_abs_self w.re]
    have hc_im : c.im = t := by simp [c, reciprocalZetaBorelCenter]
    have hcw_im_lower : 1 ≤ |(c + w).im| := by
      have htri : |t| ≤ |(c + w).im| + |w.im| := by
        have habs := abs_sub_abs_le_abs_sub t (t + w.im)
        rw [show (c + w).im = t + w.im by simp only [Complex.add_im, hc_im]]
        have hdiff : |t - (t + w.im)| = |w.im| := by
          rw [show t - (t + w.im) = -w.im by ring, abs_neg]
        rw [hdiff] at habs
        linarith
      linarith
    have hcw_im_upper : 1 + |(c + w).im| ≤ 2 * (1 + |t|) := by
      have htri : |(c + w).im| ≤ |t| + |w.im| := by
        simpa [hc_im] using abs_add_le t w.im
      linarith
    have hzeta := norm_riemannZeta_le_linear_of_re_mem_Icc hcw_re hcw_im_lower
    have hzeta' : ‖riemannZeta (c + w)‖ ≤ 40 * (1 + |t|) := by
      calc
        ‖riemannZeta (c + w)‖ ≤ 20 * (1 + |(c + w).im|) := hzeta
        _ ≤ 20 * (2 * (1 + |t|)) := by gcongr
        _ = 40 * (1 + |t|) := by ring
    have hexp : Real.exp ((f (c + w)).re) = ‖riemannZeta (c + w)‖ := by
      rw [← hf_exp hcw]
      simp [Function.comp_apply, Complex.norm_exp]
    change (f (c + w)).re ≤ M
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [hexp]
    exact hzeta'
  have hg_zero : ‖g 0‖ ≤ 2 := by
    have hc_bound := hf_small c (by simp [c])
    simpa [g] using hc_bound
  refine ⟨f, hf_diff, hf_exp, hf_small, ?_⟩
  intro z hz
  change z ∈ Metric.closedBall c r at hz
  let w : ℂ := z - c
  have hw_norm : ‖w‖ ≤ r := by
    simpa [w, Metric.mem_closedBall, dist_eq_norm] using hz
  have hw_open : w ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hw_norm.trans_lt hr_lt_R
  have hB := Complex.borelCaratheodory hM_pos hg_diff hg_maps hR_pos hw_open
  have hden_pos : 0 < R - ‖w‖ := sub_pos.mpr (hw_norm.trans_lt hr_lt_R)
  have hden_inv : (R - ‖w‖)⁻¹ ≤ 2 / delta := by
    have hden_lower : delta / 2 ≤ R - ‖w‖ := by linarith [hR_sub_r]
    have hrecip := one_div_le_one_div_of_le (by positivity : 0 < delta / 2) hden_lower
    calc
      (R - ‖w‖)⁻¹ = 1 / (R - ‖w‖) := by rw [one_div]
      _ ≤ 1 / (delta / 2) := hrecip
      _ = 2 / delta := by field_simp
  have hg_eq : g w = f z := by simp [g, w]
  rw [hg_eq] at hB
  have hw_le_four : ‖w‖ ≤ 4 := hw_norm.trans hr_lt_R.le |>.trans hR_le
  have hsum_le_eight : R + ‖w‖ ≤ 8 := by linarith
  have htwo_div_nonneg : 0 ≤ 2 / delta := (div_pos (by norm_num) hdelta).le
  have hden_inv_nonneg : 0 ≤ (R - ‖w‖)⁻¹ := (inv_pos.mpr hden_pos).le
  have hfirst :
      2 * M * ‖w‖ * (R - ‖w‖)⁻¹ ≤ 16 * M / delta := by
    have hleft : 2 * M * ‖w‖ ≤ 2 * M * 4 := by
      exact mul_le_mul_of_nonneg_left hw_le_four (mul_nonneg (by norm_num) hM_pos.le)
    calc
      2 * M * ‖w‖ * (R - ‖w‖)⁻¹ ≤ (2 * M * 4) * (2 / delta) :=
        mul_le_mul hleft hden_inv hden_inv_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) (by norm_num))
      _ = 16 * M / delta := by ring
  have hsecond :
      ‖g 0‖ * (R + ‖w‖) * (R - ‖w‖)⁻¹ ≤ 32 / delta := by
    have hleft : ‖g 0‖ * (R + ‖w‖) ≤ 2 * 8 := by
      exact mul_le_mul hg_zero hsum_le_eight (by positivity) (by norm_num)
    calc
      ‖g 0‖ * (R + ‖w‖) * (R - ‖w‖)⁻¹ ≤ (2 * 8) * (2 / delta) :=
        mul_le_mul hleft hden_inv hden_inv_nonneg (by norm_num)
      _ = 32 / delta := by ring
  calc
    ‖f z‖ ≤ 2 * M * ‖w‖ / (R - ‖w‖) +
        ‖g 0‖ * (R + ‖w‖) / (R - ‖w‖) := hB
    _ ≤ 16 * M / delta + 32 / delta := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      exact add_le_add hfirst hsecond
    _ ≤ (80 / delta) * logHeight := by
      have hnum : 16 * M + 32 ≤ 80 * logHeight := by nlinarith
      calc
        16 * M / delta + 32 / delta = (16 * M + 32) / delta := by ring
        _ ≤ (80 * logHeight) / delta :=
          (div_le_div_iff_of_pos_right hdelta).2 hnum
        _ = (80 / delta) * logHeight := by ring
    _ = (80 / delta) * Real.log (2 + |t|) := rfl

/-- The exact Hadamard interpolation bound for the local logarithm branch. Calling the Borel
estimate with `delta / 2` leaves a positive radial gap between the target strip and the outer
controlled circle; this is what will make the exponent uniformly smaller than one. -/
theorem RiemannHypothesis.exists_logBranch_three_circles_bound
    (hRH : RiemannHypothesis) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) :
    ∀ t : ℝ, 5 ≤ |t| →
      ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f
          (Metric.ball (reciprocalZetaBorelCenter t)
            (reciprocalZetaBorelOuterRadius (delta / 2))) ∧
        Set.EqOn (Complex.exp ∘ f) riemannZeta
          (Metric.ball (reciprocalZetaBorelCenter t)
            (reciprocalZetaBorelOuterRadius (delta / 2))) ∧
        ∀ s : ℂ, s.im = t → s.re ∈ Set.Icc (1 / 2 + delta : ℝ) 1 →
          ‖f s‖ ≤
            2 ^ (1 - reciprocalZetaThreeCirclesExponent delta
              ‖s - reciprocalZetaBorelCenter t‖) *
            ((160 / delta) * Real.log (2 + |t|)) ^
              reciprocalZetaThreeCirclesExponent delta
                ‖s - reciprocalZetaBorelCenter t‖ := by
  intro t ht
  have hdelta_half : 0 < delta / 2 := by positivity
  have hdelta_half_le : delta / 2 ≤ 1 / 2 := by linarith
  obtain ⟨f, hf_diff, hf_exp, hf_small, hf_large⟩ :=
    RiemannHypothesis.exists_logBranch_borel_bound
      hRH hdelta_half hdelta_half_le t ht
  refine ⟨f, hf_diff, hf_exp, ?_⟩
  intro s hsim hsre
  let c := reciprocalZetaBorelCenter t
  let r₁ : ℝ := 1 / 2
  let r₃ := reciprocalZetaBorelInnerRadius (delta / 2)
  let R := reciprocalZetaBorelOuterRadius (delta / 2)
  let B := (160 / delta) * Real.log (2 + |t|)
  have hr₁ : 0 < r₁ := by norm_num [r₁]
  have hr₁r₃ : r₁ < r₃ := by
    dsimp only [r₁, r₃, reciprocalZetaBorelInnerRadius]
    linarith
  have hr₃R : r₃ < R := by
    dsimp only [r₃, R, reciprocalZetaBorelInnerRadius, reciprocalZetaBorelOuterRadius]
    linarith
  have hsmall : ∀ z ∈ Metric.closedBall c r₁, ‖f z‖ ≤ 2 := by
    simpa only [c, r₁] using hf_small
  have hlarge : ∀ z ∈ Metric.closedBall c r₃, ‖f z‖ ≤ B := by
    intro z hz
    have h := hf_large z (by simpa only [c, r₃] using hz)
    change ‖f z‖ ≤ (160 / delta) * Real.log (2 + |t|)
    convert h using 1
    field_simp
    ring
  have hnorm_eq : ‖s - c‖ = 4 - s.re := by
    simpa only [c] using norm_sub_reciprocalZetaBorelCenter_eq hsim hsre.2
  have hz₁ : r₁ ≤ ‖s - c‖ := by
    rw [hnorm_eq]
    dsimp only [r₁]
    linarith [hsre.2]
  have hz₃ : ‖s - c‖ ≤ r₃ := by
    rw [hnorm_eq]
    dsimp only [r₃, reciprocalZetaBorelInnerRadius]
    linarith [hsre.1]
  have hthree := norm_le_three_circles_of_differentiableOn_ball
    hr₁ hr₁r₃ hr₃R hf_diff hsmall hlarge hz₁ hz₃
  simpa only [c, r₁, r₃, R, B, reciprocalZetaThreeCirclesExponent] using hthree

/-- Uniform strictly sublinear logarithmic growth of the local logarithm branch on the target
strip. The exponent depends on `delta` but is always strictly smaller than one. -/
theorem RiemannHypothesis.exists_logBranch_log_rpow_bound
    (hRH : RiemannHypothesis) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) :
    let theta := reciprocalZetaThreeCirclesMaxExponent delta
    0 ≤ theta ∧ theta < 1 ∧
      ∀ t : ℝ, 5 ≤ |t| →
        ∃ f : ℂ → ℂ,
          DifferentiableOn ℂ f
            (Metric.ball (reciprocalZetaBorelCenter t)
              (reciprocalZetaBorelOuterRadius (delta / 2))) ∧
          Set.EqOn (Complex.exp ∘ f) riemannZeta
            (Metric.ball (reciprocalZetaBorelCenter t)
              (reciprocalZetaBorelOuterRadius (delta / 2))) ∧
          ∀ s : ℂ, s.im = t → s.re ∈ Set.Icc (1 / 2 + delta : ℝ) 1 →
            ‖f s‖ ≤
              (2 * (160 / delta) ^ theta) * (Real.log (2 + |t|)) ^ theta := by
  let theta := reciprocalZetaThreeCirclesMaxExponent delta
  have htheta := reciprocalZetaThreeCirclesExponent_bounds hdelta hdelta_le
    (rho := 7 / 2 - delta) (by linarith) le_rfl
  have htheta_nonneg : 0 ≤ theta := by
    simpa only [theta, reciprocalZetaThreeCirclesMaxExponent] using htheta.1
  have htheta_lt_one : theta < 1 := by simpa only [theta] using htheta.2.2
  refine ⟨htheta_nonneg, htheta_lt_one, ?_⟩
  intro t ht
  obtain ⟨f, hf_diff, hf_exp, hf_three⟩ :=
    RiemannHypothesis.exists_logBranch_three_circles_bound
      hRH hdelta hdelta_le t ht
  refine ⟨f, hf_diff, hf_exp, ?_⟩
  intro s hsim hsre
  let rho := ‖s - reciprocalZetaBorelCenter t‖
  let alpha := reciprocalZetaThreeCirclesExponent delta rho
  let logH := Real.log (2 + |t|)
  let B := (160 / delta) * logH
  have hrho_eq : rho = 4 - s.re := by
    simpa only [rho] using norm_sub_reciprocalZetaBorelCenter_eq hsim hsre.2
  have hrho_lower : 1 / 2 ≤ rho := by rw [hrho_eq]; linarith [hsre.2]
  have hrho_upper : rho ≤ 7 / 2 - delta := by rw [hrho_eq]; linarith [hsre.1]
  obtain ⟨halpha_nonneg, halpha_theta, _⟩ :=
    reciprocalZetaThreeCirclesExponent_bounds hdelta hdelta_le hrho_lower hrho_upper
  have hlog_one : 1 ≤ logH := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    dsimp only [logH]
    rw [← Real.exp_le_exp, Real.exp_log (by linarith [abs_nonneg t])]
    linarith [ht]
  have hfactor_one : 1 ≤ 160 / delta := by
    rw [le_div_iff₀ hdelta]
    linarith [hdelta_le]
  have hfactor_nonneg : 0 ≤ 160 / delta := hfactor_one.trans' zero_le_one
  have hlog_nonneg : 0 ≤ logH := zero_le_one.trans hlog_one
  have hB_one : 1 ≤ B := by
    dsimp only [B]
    nlinarith [mul_le_mul hfactor_one hlog_one zero_le_one hfactor_nonneg]
  have htwo_power : (2 : ℝ) ^ (1 - alpha) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := 1 - alpha) (z := 1)
        (by norm_num : (1 : ℝ) ≤ 2) (by
        have : 0 ≤ alpha := by simpa only [alpha] using halpha_nonneg
        linarith)
  have hB_power : B ^ alpha ≤ B ^ theta := by
    exact Real.rpow_le_rpow_of_exponent_le hB_one (by
      simpa only [alpha, theta] using halpha_theta)
  have hthree := hf_three s hsim hsre
  change ‖f s‖ ≤ (2 * (160 / delta) ^ theta) * logH ^ theta
  calc
    ‖f s‖ ≤ 2 ^ (1 - alpha) * B ^ alpha := by
      simpa only [alpha, rho, B, logH] using hthree
    _ ≤ 2 * B ^ theta := by
      exact mul_le_mul htwo_power hB_power (Real.rpow_nonneg (zero_le_one.trans hB_one) _)
        (by norm_num)
    _ = (2 * (160 / delta) ^ theta) * logH ^ theta := by
      dsimp only [B]
      rw [Real.mul_rpow hfactor_nonneg hlog_nonneg]
      ring

/-- At sufficiently large logarithmic height, the strictly sublinear logarithm-branch estimate
implies the source-equivalent arbitrary-power bound for reciprocal zeta. -/
theorem RiemannHypothesis.exists_reciprocalZeta_rpow_bound_at_large_logHeight
    (hRH : RiemannHypothesis) {delta eta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) (heta : 0 < eta) :
    ∃ A : ℝ, ∀ s : ℂ,
      5 ≤ |s.im| → A ≤ Real.log (2 + |s.im|) →
      s.re ∈ Set.Icc (1 / 2 + delta : ℝ) 1 →
      ‖(riemannZeta s)⁻¹‖ ≤ (2 + |s.im|) ^ eta := by
  let theta := reciprocalZetaThreeCirclesMaxExponent delta
  let K := 2 * (160 / delta) ^ theta
  obtain ⟨htheta_nonneg, htheta_lt_one, hbranch⟩ :=
    RiemannHypothesis.exists_logBranch_log_rpow_bound hRH hdelta hdelta_le
  have hevent := eventually_const_mul_rpow_le_mul_self
    (K := K) htheta_lt_one heta
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨A, hA⟩ := hevent
  refine ⟨A, ?_⟩
  intro s ht hlog hsre
  obtain ⟨f, hf_diff, hf_exp, hf_bound⟩ := hbranch s.im ht
  have hs_mem : s ∈ Metric.ball (reciprocalZetaBorelCenter s.im)
      (reciprocalZetaBorelOuterRadius (delta / 2)) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hrho := norm_sub_reciprocalZetaBorelCenter_eq (s := s) rfl hsre.2
    rw [hrho]
    dsimp only [reciprocalZetaBorelOuterRadius]
    linarith [hsre.1]
  have hexp : Complex.exp (f s) = riemannZeta s := by
    simpa only [Function.comp_apply] using hf_exp hs_mem
  have hf := hf_bound s rfl hsre
  have hsublinear : K * (Real.log (2 + |s.im|)) ^ theta ≤
      eta * Real.log (2 + |s.im|) := hA _ hlog
  have hf_eta : ‖f s‖ ≤ eta * Real.log (2 + |s.im|) := by
    exact hf.trans (by simpa only [K, theta] using hsublinear)
  have hneg_re : -(f s).re ≤ ‖f s‖ := by
    have hre := Complex.abs_re_le_norm (f s)
    linarith [neg_abs_le (f s).re]
  have hheight_pos : 0 < 2 + |s.im| := by positivity
  calc
    ‖(riemannZeta s)⁻¹‖ = Real.exp (-(f s).re) := by
      rw [← hexp, ← Complex.exp_neg]
      exact Complex.norm_exp (-f s)
    _ ≤ Real.exp ‖f s‖ := Real.exp_le_exp.mpr hneg_re
    _ ≤ Real.exp (eta * Real.log (2 + |s.im|)) := Real.exp_le_exp.mpr hf_eta
    _ = (2 + |s.im|) ^ eta := by
      rw [Real.rpow_def_of_pos hheight_pos]
      congr 1
      ring

/-- Global source-equivalent reciprocal-zeta growth bound, with the harmless shifted height
`2 + |Im(s)|`. The finite-height range is covered by the residue estimate near `s = 1` and
compactness away from that point. -/
theorem RiemannHypothesis.exists_reciprocalZeta_rpow_bound_two_add
    (hRH : RiemannHypothesis) {delta eta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc (1 / 2 + delta : ℝ) 1 →
      ‖(riemannZeta s)⁻¹‖ ≤ C * (2 + |s.im|) ^ eta := by
  obtain ⟨A, hlarge⟩ :=
    RiemannHypothesis.exists_reciprocalZeta_rpow_bound_at_large_logHeight
      hRH hdelta hdelta_le heta
  obtain ⟨epsilon, hepsilon, Cpole, hCpole, hpole⟩ :=
    exists_norm_reciprocal_riemannZeta_le_near_one
  let T := max 5 (Real.exp A)
  let rectangle : Set ℂ :=
    Set.Icc (1 / 2 + delta : ℝ) 1 ×ℂ Set.Icc (-T) T
  let compactPart : Set ℂ := rectangle \ Metric.ball 1 epsilon
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hcompact : IsCompact compactPart := by
    apply IsCompact.diff
    · exact isCompact_Icc.reProdIm isCompact_Icc
    · exact Metric.isOpen_ball
  have hcontinuous : ContinuousOn (fun s : ℂ => ‖(riemannZeta s)⁻¹‖) compactPart := by
    intro s hs
    have hs_ne : s ≠ 1 := by
      intro hs_one
      subst s
      exact hs.2 (Metric.mem_ball_self hepsilon)
    have hsrect : s ∈ rectangle := hs.1
    change s ∈ Set.Icc (1 / 2 + delta : ℝ) 1 ×ℂ Set.Icc (-T) T at hsrect
    rw [Complex.mem_reProdIm] at hsrect
    have hzeta_ne : riemannZeta s ≠ 0 :=
      RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) (by
        linarith [hsrect.1.1])
    exact ((differentiableAt_riemannZeta hs_ne).continuousAt.inv₀ hzeta_ne).norm.continuousWithinAt
  obtain ⟨M, hM⟩ := bddAbove_def.mp (hcompact.bddAbove_image hcontinuous)
  let C := max 1 (max Cpole M)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro s hsre
  have hheight_one : 1 ≤ (2 + |s.im|) ^ eta := by
    exact Real.one_le_rpow (by linarith [abs_nonneg s.im]) heta.le
  have hC_nonneg : 0 ≤ C := hC.le
  by_cases him_large : T ≤ |s.im|
  · have ht : 5 ≤ |s.im| := (le_max_left _ _).trans him_large
    have hexpA : Real.exp A ≤ 2 + |s.im| := by
      exact (le_max_right _ _).trans him_large |>.trans (by linarith)
    have hlog : A ≤ Real.log (2 + |s.im|) := by
      rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
      exact hexpA
    have h := hlarge s ht hlog hsre
    exact h.trans (by
      have hCone : 1 ≤ C := le_max_left _ _
      nlinarith [mul_le_mul_of_nonneg_right hCone (Real.rpow_nonneg (by positivity) eta)])
  · have him_lt : |s.im| < T := lt_of_not_ge him_large
    have hlocal : ‖(riemannZeta s)⁻¹‖ ≤ max Cpole M := by
      by_cases hs_ball : s ∈ Metric.ball 1 epsilon
      · exact (hpole s (Metric.mem_ball.mp hs_ball)).trans (le_max_left _ _)
      · have hs_rectangle : s ∈ rectangle := by
          change s ∈ Set.Icc (1 / 2 + delta : ℝ) 1 ×ℂ Set.Icc (-T) T
          rw [Complex.mem_reProdIm]
          refine ⟨hsre, ?_⟩
          exact ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩
        have hs_compact : s ∈ compactPart := ⟨hs_rectangle, hs_ball⟩
        have hs_image : ‖(riemannZeta s)⁻¹‖ ∈
            (fun z : ℂ => ‖(riemannZeta z)⁻¹‖) '' compactPart :=
          ⟨s, hs_compact, rfl⟩
        exact (hM _ hs_image).trans (le_max_right _ _)
    have hlocal_C : ‖(riemannZeta s)⁻¹‖ ≤ C :=
      hlocal.trans (le_max_right _ _)
    exact hlocal_C.trans (by nlinarith)

/-- Titchmarsh (14.2.6), in the reciprocal-zeta direction needed for the Burnol and
Balazard-Saias route: under RH, reciprocal zeta has arbitrarily small polynomial growth,
uniformly on every closed substrip to the right of the critical line. -/
theorem RiemannHypothesis.exists_reciprocalZeta_subpower_bound
    (hRH : RiemannHypothesis) {delta eta : ℝ} (hdelta : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc (1 / 2 + delta : ℝ) 1 →
      ‖(riemannZeta s)⁻¹‖ ≤ C * (1 + |s.im|) ^ eta := by
  obtain ⟨C, hC, hbound⟩ :=
    RiemannHypothesis.exists_reciprocalZeta_rpow_bound_two_add
      hRH hdelta hdelta_le heta
  let C' := C * 2 ^ eta
  have htwo_power_pos : 0 < (2 : ℝ) ^ eta := Real.rpow_pos_of_pos (by norm_num) _
  have hC' : 0 < C' := mul_pos hC htwo_power_pos
  refine ⟨C', hC', ?_⟩
  intro s hsre
  have hbase : 2 + |s.im| ≤ 2 * (1 + |s.im|) := by
    linarith [abs_nonneg s.im]
  have hpower : (2 + |s.im|) ^ eta ≤ (2 * (1 + |s.im|)) ^ eta :=
    Real.rpow_le_rpow (by positivity) hbase heta.le
  calc
    ‖(riemannZeta s)⁻¹‖ ≤ C * (2 + |s.im|) ^ eta := hbound s hsre
    _ ≤ C * (2 * (1 + |s.im|)) ^ eta :=
      mul_le_mul_of_nonneg_left hpower hC.le
    _ = C' * (1 + |s.im|) ^ eta := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      dsimp only [C']
      ring

end LeanLab.Riemann
