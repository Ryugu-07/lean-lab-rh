import LeanLab.Riemann.LevinsonMontgomeryHeightTenEndpoint

set_option linter.style.header false
set_option linter.style.longLine false

namespace LeanLab.Riemann

open Complex Function Set
open scoped Topology

noncomputable section

private theorem exists_speiserStrictNegativePoint_near
    {s : ℂ} (hsOne : s ≠ 1)
    (hdata : riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 ∧
      (speiserZetaDerivRatio s).re < 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : ℂ, dist z s < epsilon →
        riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
          (speiserZetaDerivRatio z).re < 0 := by
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hsOne)
  have hderivAnalytic : AnalyticAt ℂ (deriv riemannZeta) s :=
    analyticOnNhd_deriv_riemannZeta s (by simpa using hsOne)
  have hratioContinuous : ContinuousAt speiserZetaDerivRatio s :=
    (hasDerivAt_speiserZetaDerivRatio hsOne hdata.1 hdata.2.1).continuousAt
  have hratioReContinuous :
      ContinuousAt (fun z : ℂ => (speiserZetaDerivRatio z).re) s :=
    Complex.continuous_re.continuousAt.comp hratioContinuous
  have heventually : ∀ᶠ z in nhds s,
      riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
        (speiserZetaDerivRatio z).re < 0 :=
    (hzetaAnalytic.continuousAt.eventually_ne hdata.1).and
      ((hderivAnalytic.continuousAt.eventually_ne hdata.2.1).and
        (hratioReContinuous.eventually_lt_const hdata.2.2))
  change {z : ℂ | riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
    (speiserZetaDerivRatio z).re < 0} ∈ nhds s at heventually
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp heventually
  exact ⟨epsilon, hepsilon, fun z hz =>
    hball (by simpa [Metric.mem_ball] using hz)⟩

private theorem heightTen_horizontal_dist_left (sigma : ℝ) :
    dist (((sigma : ℂ) + (10 : ℂ) * I)) ((10 : ℂ) * I) = |sigma| := by
  rw [dist_eq_norm]
  have hsub :
      ((sigma : ℂ) + (10 : ℂ) * I) - (10 : ℂ) * I = (sigma : ℂ) := by
    ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs]

private theorem heightTen_horizontal_dist_right (sigma : ℝ) :
    dist (((sigma : ℂ) + (10 : ℂ) * I)) heightTenEndpoint =
      |sigma - 1 / 2| := by
  rw [dist_eq_norm]
  have hsub :
      ((sigma : ℂ) + (10 : ℂ) * I) - heightTenEndpoint =
        ((sigma - 1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [heightTenEndpoint]
  rw [hsub, Complex.norm_real, Real.norm_eq_abs]

theorem exists_heightTen_left_strictNegative_interval :
    ∃ a : ℝ, 0 < a ∧
      ∀ sigma : ℝ, sigma ∈ Set.Icc 0 a →
        riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
          deriv riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
          (speiserZetaDerivRatio
            ((sigma : ℂ) + (10 : ℂ) * I)).re < 0 := by
  have hleft :
      riemannZeta ((10 : ℂ) * I) ≠ 0 ∧
        deriv riemannZeta ((10 : ℂ) * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((10 : ℂ) * I)).re < 0 := by
    simpa using
      (levinsonMontgomery_leftVertical_negative (b := 10) (t := 10)
        (by norm_num) 10 (by norm_num))
  obtain ⟨epsilon, hepsilon, hnear⟩ :=
    exists_speiserStrictNegativePoint_near (s := (10 : ℂ) * I)
      (by
        intro h
        have him := congrArg Complex.im h
        norm_num at him) hleft
  let a : ℝ := min epsilon (1 / 4) / 2
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haEpsilon : a < epsilon := by
    dsimp only [a]
    have hmin : min epsilon (1 / 4) ≤ epsilon := min_le_left _ _
    have hminPos : 0 < min epsilon (1 / 4) := lt_min hepsilon (by norm_num)
    linarith
  refine ⟨a, ha, fun sigma hsigma => ?_⟩
  apply hnear
  rw [heightTen_horizontal_dist_left, abs_of_nonneg hsigma.1]
  exact hsigma.2.trans_lt haEpsilon

theorem exists_heightTen_right_strictNegative_interval :
    ∃ b : ℝ, b < 1 / 2 ∧
      ∀ sigma : ℝ, sigma ∈ Set.Icc b (1 / 2) →
        riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
          deriv riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
          (speiserZetaDerivRatio
            ((sigma : ℂ) + (10 : ℂ) * I)).re < 0 := by
  obtain ⟨epsilon, hepsilon, hnear⟩ :=
    exists_speiserStrictNegativePoint_near (s := heightTenEndpoint)
      (by
        intro h
        have him := congrArg Complex.im h
        norm_num [heightTenEndpoint] at him)
      speiserStrictNegativePoint_heightTenEndpoint
  let delta : ℝ := min epsilon (1 / 4) / 2
  let b : ℝ := 1 / 2 - delta
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltaEpsilon : delta < epsilon := by
    dsimp only [delta]
    have hmin : min epsilon (1 / 4) ≤ epsilon := min_le_left _ _
    have hminPos : 0 < min epsilon (1 / 4) := lt_min hepsilon (by norm_num)
    linarith
  have hb : b < 1 / 2 := by
    dsimp only [b]
    linarith
  refine ⟨b, hb, fun sigma hsigma => ?_⟩
  apply hnear
  rw [heightTen_horizontal_dist_right,
    abs_of_nonpos (sub_nonpos.mpr hsigma.2)]
  dsimp only [b] at hsigma
  have hsigmaDelta : 1 / 2 - sigma ≤ delta := by linarith [hsigma.1]
  have hneg : -(sigma - 1 / 2) = 1 / 2 - sigma := by ring
  rw [hneg]
  exact hsigmaDelta.trans_lt hdeltaEpsilon

theorem exists_heightTen_compactMiddle_reduction :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < 1 / 2 ∧
      ((∀ sigma : ℝ, sigma ∈ Set.Icc a b →
          riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
            deriv riemannZeta ((sigma : ℂ) + (10 : ℂ) * I) ≠ 0 ∧
            (speiserZetaDerivRatio
              ((sigma : ℂ) + (10 : ℂ) * I)).re < 0) →
        SpeiserStrictNegativeHorizontal 10) := by
  obtain ⟨a0, ha0, hleft⟩ :=
    exists_heightTen_left_strictNegative_interval
  obtain ⟨b0, hb0, hright⟩ :=
    exists_heightTen_right_strictNegative_interval
  let a : ℝ := min a0 (1 / 8)
  let b : ℝ := max b0 (3 / 8)
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min ha0 (by norm_num)
  have haUpper : a ≤ 1 / 8 := by
    dsimp only [a]
    exact min_le_right _ _
  have haA0 : a ≤ a0 := by
    dsimp only [a]
    exact min_le_left _ _
  have hbLower : 3 / 8 ≤ b := by
    dsimp only [b]
    exact le_max_right _ _
  have hb0B : b0 ≤ b := by
    dsimp only [b]
    exact le_max_left _ _
  have hb : b < 1 / 2 := by
    dsimp only [b]
    exact max_lt hb0 (by norm_num)
  have hab : a ≤ b := by linarith
  refine ⟨a, b, ha, hab, hb, fun hmiddle => ?_⟩
  refine ⟨by norm_num, fun sigma hsigma => ?_⟩
  by_cases hsigmaLeft : sigma ≤ a
  · apply hleft sigma
    exact ⟨hsigma.1, hsigmaLeft.trans haA0⟩
  by_cases hsigmaRight : b ≤ sigma
  · apply hright sigma
    exact ⟨hb0B.trans hsigmaRight, hsigma.2⟩
  apply hmiddle sigma
  exact ⟨le_of_lt (lt_of_not_ge hsigmaLeft),
    le_of_lt (lt_of_not_ge hsigmaRight)⟩

end

end LeanLab.Riemann
