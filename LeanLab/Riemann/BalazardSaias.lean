import LeanLab.Riemann.Basic
import LeanLab.Riemann.BaezDuarteConvergence
import LeanLab.Riemann.ZetaConvexityMidpoint

set_option linter.style.header false

/-!
# The Balazard-Saias boundary in the Baez-Duarte route

This file records the exact quantitative statement used by Baez-Duarte and Burnol. The statement
is a proposition, not an axiom: later theorems that consume it retain it as an explicit premise.
-/

noncomputable section

open MeasureTheory
open scoped ArithmeticFunction.Moebius ENNReal

namespace LeanLab.Riemann

/-- The finite Mobius Dirichlet sum occurring in the Balazard-Saias estimate. -/
def mobiusDirichletPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)

/-- The exact uniform estimate quoted as Baez-Duarte Lemma 2.1.

Defining this proposition does not assert that it holds. In particular, it may only be used by
passing a proof as an explicit argument. -/
def BalazardSaiasEstimate : Prop :=
  ∀ α δ η : ℝ,
    1 / 2 ≤ α → α < 1 → 0 < δ → 0 < η →
      (∀ s : ℂ, α < s.re → riemannZeta s ≠ 0) →
        ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (s : ℂ),
          2 ≤ N → α + δ ≤ s.re → s.re ≤ 1 →
            ‖mobiusDirichletPartialSum N s - (riemannZeta s)⁻¹‖ ≤
              C * (N : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η

/-- Under RH, the already-compiled zero-free bridge supplies exactly the analytic premise in the
Balazard-Saias estimate at `alpha = 1/2`. This theorem does not prove the estimate itself. -/
theorem RiemannHypothesis.exists_balazardSaias_specialized_bound
    (hRH : RiemannHypothesis) (hBS : BalazardSaiasEstimate)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (s : ℂ),
      2 ≤ N → (1 / 2 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
        ‖mobiusDirichletPartialSum N s - (riemannZeta s)⁻¹‖ ≤
          C * (N : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  apply hBS (1 / 2) δ η (by rfl) (by norm_num) hδ hη
  intro s hs
  exact RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) hs

/-- The critical-line zeta estimate from the preceding batch, extended over the compact range
`|t| < 1`. -/
theorem exists_norm_riemannZeta_criticalLine_le_rpow_all :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (3 / 8 : ℝ) := by
  obtain ⟨A, hA, hlarge⟩ := exists_norm_riemannZeta_criticalLine_le_rpow
  let f : ℝ → ℂ := fun t => riemannZeta ((1 / 2 : ℂ) + t * Complex.I)
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs_ne : (1 / 2 : ℂ) + t * Complex.I ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      norm_num at hre
    change Filter.Tendsto
      (fun u : ℝ => riemannZeta ((1 / 2 : ℂ) + u * Complex.I))
      (nhds t) (nhds (riemannZeta ((1 / 2 : ℂ) + t * Complex.I)))
    have hg : Continuous (fun u : ℝ => (1 / 2 : ℂ) + u * Complex.I) := by fun_prop
    exact (differentiableAt_riemannZeta hs_ne).continuousAt.tendsto.comp (hg.tendsto t)
  have hnorm_cont : ContinuousOn (fun t : ℝ => ‖f t‖) (Set.Icc (-1 : ℝ) 1) :=
    hf.norm.continuousOn
  obtain ⟨B₀, hB₀⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc hnorm_cont)
  let B : ℝ := |B₀| + 1
  have hB : 0 < B := by dsimp only [B]; linarith [abs_nonneg B₀]
  have hBbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖f t‖ ≤ B := by
    intro t ht
    calc
      ‖f t‖ ≤ B₀ := hB₀ ‖f t‖ ⟨t, ht, rfl⟩
      _ ≤ |B₀| := le_abs_self B₀
      _ ≤ B := by simp [B]
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro t
  have hx : 1 ≤ (1 + |t|) ^ (3 / 8 : ℝ) := by
    exact Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  by_cases ht : 1 ≤ |t|
  · calc
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ A * (1 + |t|) ^ (3 / 8 : ℝ) := hlarge t ht
      _ ≤ (A + B) * (1 + |t|) ^ (3 / 8 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith [hB.le]) (Real.rpow_nonneg (by positivity) _)
  · have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      have habs : |t| < 1 := lt_of_not_ge ht
      exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
    have hsmall : ‖f t‖ ≤ B := hBbound t ht_mem
    calc
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ B := hsmall
      _ ≤ (A + B) * 1 := by linarith
      _ ≤ (A + B) * (1 + |t|) ^ (3 / 8 : ℝ) := by
        gcongr

/-- After division by the critical-line parameter, the unconditional `3/8` zeta bound becomes
the `-5/8` power needed in Burnol's square-integrability argument. -/
theorem exists_norm_riemannZeta_div_criticalLine_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I) /
          ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (-5 / 8 : ℝ) := by
  obtain ⟨A, hA, hzeta⟩ := exists_norm_riemannZeta_criticalLine_le_rpow_all
  refine ⟨3 * A, mul_pos (by norm_num) hA, ?_⟩
  intro t
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  let x : ℝ := 1 + |t|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hs_re : s.re = 1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs_norm_pos : 0 < ‖s‖ := by
    apply norm_pos_iff.mpr
    intro hs0
    have hre := congrArg Complex.re hs0
    simp [hs_re] at hre
  have hx_le : x ≤ 3 * ‖s‖ := by
    have hre_le : (1 / 2 : ℝ) ≤ ‖s‖ := by
      calc
        (1 / 2 : ℝ) = |s.re| := by rw [hs_re]; norm_num
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have him_le : |t| ≤ ‖s‖ := by
      calc
        |t| = |s.im| := by rw [hs_im]
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    dsimp only [x]
    linarith [abs_nonneg t]
  have hinv : ‖s‖⁻¹ ≤ 3 * x⁻¹ := by
    have hthird_pos : 0 < x / 3 := by positivity
    have hthird_le : x / 3 ≤ ‖s‖ := by linarith
    have h := (inv_le_inv₀ hs_norm_pos hthird_pos).2 hthird_le
    calc
      ‖s‖⁻¹ ≤ (x / 3)⁻¹ := h
      _ = 3 * x⁻¹ := by field_simp
  have hzeta' : ‖riemannZeta s‖ ≤ A * x ^ (3 / 8 : ℝ) := by
    simpa only [s, x] using hzeta t
  rw [norm_div]
  calc
    ‖riemannZeta s‖ / ‖s‖ = ‖riemannZeta s‖ * ‖s‖⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ (A * x ^ (3 / 8 : ℝ)) * (3 * x⁻¹) := by
      gcongr
    _ = 3 * A * (x ^ (3 / 8 : ℝ) * x⁻¹) := by ring
    _ = 3 * A * x ^ (-5 / 8 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
      norm_num
    _ = 3 * A * (1 + |t|) ^ (-5 / 8 : ℝ) := rfl

/-- Burnol's transformed finite-sum error on the critical line. -/
def burnolMobiusTransformedError (δ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  riemannZeta s / s *
    (mobiusDirichletPartialSum N (s + δ) - (riemannZeta (s + δ))⁻¹)

theorem norm_baezDuarteVerticalMajorant_three_eighths_add
    (η t : ℝ) :
    ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ =
      (1 + |t|) ^ (-5 / 8 + η : ℝ) := by
  rw [baezDuarteVerticalMajorant, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  congr 1
  ring

/-- The exact pointwise majorant obtained by combining Balazard-Saias with the unconditional
critical-line zeta bound. The Balazard-Saias estimate remains an explicit premise. -/
theorem RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le
    (hRH : RiemannHypothesis) (hBS : BalazardSaiasEstimate)
    {δ η : ℝ} (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N →
      ‖burnolMobiusTransformedError δ N t‖ ≤
        K * (N : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ := by
  obtain ⟨A, hA, hquot⟩ := exists_norm_riemannZeta_div_criticalLine_le_rpow
  obtain ⟨B, hB, hmobius⟩ :=
    RiemannHypothesis.exists_balazardSaias_specialized_bound hRH hBS hδ hη
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro N t hN
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  let z : ℂ := s + δ
  let x : ℝ := 1 + |t|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hz_re : z.re = (1 / 2 : ℝ) + δ := by simp [z, s]
  have hz_im : z.im = t := by simp [z, s]
  have hmobius' :
      ‖mobiusDirichletPartialSum N z - (riemannZeta z)⁻¹‖ ≤
        B * (N : ℝ) ^ (-δ / 3) * x ^ η := by
    have h := hmobius N z hN (by rw [hz_re]) (by rw [hz_re]; linarith)
    simpa only [hz_im, x] using h
  have hquot' : ‖riemannZeta s / s‖ ≤ A * x ^ (-5 / 8 : ℝ) := by
    simpa only [s, x] using hquot t
  change ‖riemannZeta s / s *
    (mobiusDirichletPartialSum N z - (riemannZeta z)⁻¹)‖ ≤ _
  rw [norm_mul]
  calc
    ‖riemannZeta s / s‖ *
        ‖mobiusDirichletPartialSum N z - (riemannZeta z)⁻¹‖
        ≤ (A * x ^ (-5 / 8 : ℝ)) *
          (B * (N : ℝ) ^ (-δ / 3) * x ^ η) := by gcongr
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) *
        (x ^ (-5 / 8 : ℝ) * x ^ η) := by ring
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) * x ^ (-5 / 8 + η : ℝ) := by
      rw [← Real.rpow_add hx]
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) *
        ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ := by
      rw [norm_baezDuarteVerticalMajorant_three_eighths_add]

/-- Burnol's power majorant is square-integrable precisely with the available `3/8` zeta
exponent whenever the Balazard-Saias height exponent is chosen below `1/8`. -/
theorem burnolMobiusMajorant_memLp
    {η : ℝ} (hη : η < 1 / 8) :
    MemLp (baezDuarteVerticalMajorant (3 / 8 + η))
      (2 : ℝ≥0∞) volume := by
  apply baezDuarteVerticalMajorant_memLp
  linarith

/-- The coefficient in the Balazard-Saias error tends to zero for every positive strip margin. -/
theorem tendsto_natCast_rpow_neg_delta_div_three
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ / 3))
      Filter.atTop (nhds 0) := by
  have hthird : 0 < δ / 3 := by positivity
  convert (tendsto_rpow_neg_atTop hthird).comp tendsto_natCast_atTop_atTop using 1
  funext N
  change (N : ℝ) ^ (-δ / 3) = (N : ℝ) ^ (-(δ / 3))
  congr 1
  ring

end LeanLab.Riemann
