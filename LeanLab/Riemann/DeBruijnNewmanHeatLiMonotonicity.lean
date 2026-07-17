import LeanLab.Riemann.DeBruijnNewmanLiCriterion

set_option linter.style.header false

/-!
# Heat-time monotonicity reduction for the de Bruijn-Newman Li coefficients

This module isolates the exact all-index assumptions of the heat-Li monotonicity campaign and
proves that they imply the Riemann hypothesis.  It does not assert either analytic assumption.
-/

open Filter Set Topology

namespace LeanLab.Riemann

/-- Every heat-Li coefficient tends to zero at negative infinite heat time. -/
def DeBruijnNewmanHeatLiAtBotZero : Prop :=
  forall n : Nat,
    Tendsto (fun t : Real => (deBruijnNewmanHeatLiCoefficient t n).re)
      atBot (nhds 0)

/-- Every heat-Li coefficient is nondecreasing through heat time zero. -/
def DeBruijnNewmanHeatLiMonotoneToZero : Prop :=
  forall n : Nat,
    MonotoneOn
      (fun t : Real => (deBruijnNewmanHeatLiCoefficient t n).re)
      (Iic 0)

/-- The heat equation after division by the heat-Xi value.  This is the function-level input to
the logarithmic generating-series evolution; no nonvanishing assumption is needed for the
identity because division is total in `Complex`. -/
theorem deBruijnNewmanHeatXi_timeRatio_eq_spaceSecondRatio (t : Real) (s : Complex) :
    deriv (fun tau : Real => deBruijnNewmanHeatXi tau s) t /
        deBruijnNewmanHeatXi t s =
      ((1 / 4 : Complex) * deriv (deriv (deBruijnNewmanHeatXi t)) s) /
        deBruijnNewmanHeatXi t s := by
  rw [deBruijnNewmanHeatXi_heat_equation]

/-- The spatial second-derivative ratio is the logarithmic-derivative evolution expression at
every nonzero point of heat-Xi. -/
theorem deBruijnNewmanHeatXi_spaceSecondRatio_eq_logDeriv_evolution
    (t : Real) (s : Complex) (hs : deBruijnNewmanHeatXi t s ≠ 0) :
    deriv (deriv (deBruijnNewmanHeatXi t)) s / deBruijnNewmanHeatXi t s =
      deriv (logDeriv (deBruijnNewmanHeatXi t)) s +
        logDeriv (deBruijnNewmanHeatXi t) s ^ 2 := by
  have hquot := (hasDerivAt_deriv_deBruijnNewmanHeatXi t s).div
    (hasDerivAt_deBruijnNewmanHeatXi t s) hs
  rw [show logDeriv (deBruijnNewmanHeatXi t) =
      deriv (deBruijnNewmanHeatXi t) / deBruijnNewmanHeatXi t by
    funext z
    exact logDeriv_apply _ _]
  rw [hquot.deriv]
  simp only [Pi.div_apply]
  rw [(hasDerivAt_deBruijnNewmanHeatXi t s).deriv,
    (hasDerivAt_deriv_deBruijnNewmanHeatXi t s).deriv]
  field_simp [hs]
  ring

/-- Heat time evolves the local logarithm by the standard quadratic logarithmic-derivative
expression.  The left side is `partial_t F / F`; identifying it with `partial_t log F` and
commuting all higher derivatives are the remaining analytic steps for coefficient evolution. -/
theorem deBruijnNewmanHeatXi_timeRatio_eq_logDeriv_evolution
    (t : Real) (s : Complex) (hs : deBruijnNewmanHeatXi t s ≠ 0) :
    deriv (fun tau : Real => deBruijnNewmanHeatXi tau s) t /
        deBruijnNewmanHeatXi t s =
      (1 / 4 : Complex) *
        (deriv (logDeriv (deBruijnNewmanHeatXi t)) s +
          logDeriv (deBruijnNewmanHeatXi t) s ^ 2) := by
  rw [deBruijnNewmanHeatXi_timeRatio_eq_spaceSecondRatio]
  calc
    ((1 / 4 : Complex) * deriv (deriv (deBruijnNewmanHeatXi t)) s) /
        deBruijnNewmanHeatXi t s =
      (1 / 4 : Complex) *
        (deriv (deriv (deBruijnNewmanHeatXi t)) s /
          deBruijnNewmanHeatXi t s) := by ring
    _ = _ := by
      rw [deBruijnNewmanHeatXi_spaceSecondRatio_eq_logDeriv_evolution t s hs]

/-- The two all-index heat-time assumptions force every time-zero heat-Li coefficient to be
nonnegative. -/
theorem forall_heatLiCoefficient_zero_re_nonneg_of_atBot_zero_and_monotone
    (hlimit : DeBruijnNewmanHeatLiAtBotZero)
    (hmonotone : DeBruijnNewmanHeatLiMonotoneToZero) :
    forall n : Nat, 0 <= (deBruijnNewmanHeatLiCoefficient 0 n).re := by
  intro n
  apply le_of_tendsto (hlimit n)
  filter_upwards [eventually_le_atBot (0 : Real)] with t ht
  exact hmonotone n ht (mem_Iic.mpr le_rfl) ht

/-- Exact reduction of the registered all-index heat-time conjecture to RH. -/
theorem riemannHypothesis_of_heatLi_atBot_zero_and_monotone_assumptions
    (hlimit : DeBruijnNewmanHeatLiAtBotZero)
    (hmonotone : DeBruijnNewmanHeatLiMonotoneToZero) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_deBruijnNewmanHeatLiCoefficient_zero_re_nonneg]
  exact forall_heatLiCoefficient_zero_re_nonneg_of_atBot_zero_and_monotone
    hlimit hmonotone

end LeanLab.Riemann
