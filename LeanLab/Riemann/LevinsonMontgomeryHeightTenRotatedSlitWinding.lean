import LeanLab.Riemann.LevinsonMontgomeryHeightTenBoundaryNeighborhood

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Rotated slit-plane winding at height ten

This module gives a one-dimensional boundary criterion for the multiplicity-bearing
Levinson--Montgomery zero-count equality. If one rotation of `zeta'/zeta` stays in the complex
slit plane on all four rectangle edges, a common principal logarithm makes the four edge
increments telescope exactly.
-/

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace LeanLab.Riemann

noncomputable section

theorem intervalIntegral_deriv_div_eq_log_sub_of_smul_mem_slitPlane
    {g g' : ℝ → ℂ} {c : ℂ} {a b : ℝ}
    (hc : c ≠ 0)
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hslit : ∀ x ∈ Set.uIcc a b, c * g x ∈ Complex.slitPlane) :
    (∫ x : ℝ in a..b, g' x / g x) =
      Complex.log (c * g b) - Complex.log (c * g a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hrot : HasDerivAt (fun y => c * g y) (c * g' x) x :=
      (hderiv x hx).const_mul c
    have hlog := hrot.clog_real (hslit x hx)
    simpa only [mul_div_mul_left _ _ hc] using hlog
  · exact hintegrable

def SpeiserRotatedSlitBoundary (c : ℂ) (t : ℝ) : Prop :=
  0 < t ∧ c ≠ 0 ∧
    (∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      c * speiserZetaDerivRatio (sigma : ℂ) ∈ Complex.slitPlane) ∧
    (∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      c * speiserZetaDerivRatio ((sigma : ℂ) + t * I) ∈ Complex.slitPlane) ∧
    (∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      c * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane) ∧
    (∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      c * speiserZetaDerivRatio ((1 / 2 : ℂ) + y * I) ∈ Complex.slitPlane)

theorem nonzero_of_speiserRatio_smul_mem_slitPlane
    {c s : ℂ} (hslit : c * speiserZetaDerivRatio s ∈ Complex.slitPlane) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 := by
  have hproduct : c * speiserZetaDerivRatio s ≠ 0 :=
    Complex.slitPlane_ne_zero hslit
  have hratio : speiserZetaDerivRatio s ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).2
  exact ⟨(div_ne_zero_iff.mp hratio).2, (div_ne_zero_iff.mp hratio).1⟩

private theorem intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    {phi : ℝ → ℂ} {c : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hphi : Continuous phi)
    (hone : ∀ x : ℝ, x ∈ Set.Icc a b → phi x ≠ 1)
    (hslit : ∀ x : ℝ, x ∈ Set.Icc a b →
      c * speiserZetaDerivRatio (phi x) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun x : ℝ => logDeriv riemannZeta (phi x))
        (volume : Measure ℝ) a b ∧
      IntervalIntegrable
        (fun x : ℝ => logDeriv (deriv riemannZeta) (phi x))
        (volume : Measure ℝ) a b := by
  have hdata : ∀ x : ℝ, x ∈ Set.Icc a b →
      riemannZeta (phi x) ≠ 0 ∧ deriv riemannZeta (phi x) ≠ 0 := by
    intro x hx
    exact nonzero_of_speiserRatio_smul_mem_slitPlane (hslit x hx)
  constructor
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    have hanalytic : AnalyticAt ℂ riemannZeta (phi x) :=
      analyticOn_riemannZeta _ (by simpa using hone x hx)
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hdata x hx).1
    exact (ContinuousAt.comp (f := phi) (x := x)
      houter hphi.continuousAt).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    have hanalytic : AnalyticAt ℂ (deriv riemannZeta) (phi x) :=
      analyticOnNhd_deriv_riemannZeta _ (by simpa using hone x hx)
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hdata x hx).2
    exact (ContinuousAt.comp (f := phi) (x := x)
      houter hphi.continuousAt).continuousWithinAt

theorem intervalIntegral_speiserRatio_horizontal_of_rotatedSlit
    {c : ℂ} {t : ℝ} (hc : c ≠ 0)
    (hslit : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      c * speiserZetaDerivRatio ((sigma : ℂ) + t * I) ∈
        Complex.slitPlane) :
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) =
      Complex.log
          (c * speiserZetaDerivRatio ((1 / 2 : ℂ) + t * I)) -
        Complex.log (c * speiserZetaDerivRatio (t * I)) := by
  let phi : ℝ → ℂ := fun sigma => (sigma : ℂ) + t * I
  let g : ℝ → ℂ := fun sigma => speiserZetaDerivRatio (phi sigma)
  let d : ℝ → ℂ := fun sigma =>
    logDeriv (deriv riemannZeta) (phi sigma) - logDeriv riemannZeta (phi sigma)
  let g' : ℝ → ℂ := fun sigma => d sigma * g sigma
  have huIcc : Set.uIcc (0 : ℝ) (1 / 2) = Set.Icc 0 (1 / 2) :=
    Set.uIcc_of_le (by norm_num)
  have hnotone : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      phi sigma ≠ 1 := by
    intro sigma hsigma hEq
    have hre := congrArg Complex.re hEq
    simp only [phi, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      Complex.one_re] at hre
    linarith [hsigma.2]
  have hdata : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      riemannZeta (phi sigma) ≠ 0 ∧ deriv riemannZeta (phi sigma) ≠ 0 := by
    intro sigma hsigma
    exact nonzero_of_speiserRatio_smul_mem_slitPlane
      (by simpa only [phi] using hslit sigma hsigma)
  have hderiv : ∀ sigma ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt g (g' sigma) sigma := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [huIcc] using hsigma
    have houter := hasDerivAt_speiserZetaDerivRatio
      (hnotone sigma hsigmaIcc) (hdata sigma hsigmaIcc).1
        (hdata sigma hsigmaIcc).2
    have hline : HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 sigma := by
      simpa using
        (hasDerivAt_id sigma).ofReal_comp.add_const (t * I)
    change HasDerivAt
      (speiserZetaDerivRatio ∘ fun x : ℝ => (x : ℂ) + t * I) _ sigma
    simpa only [g', d, g, phi, one_smul] using houter.scomp sigma hline
  have hpairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := phi) (c := c) (a := 0) (b := 1 / 2)
      (by norm_num) (by fun_prop) hnotone
      (by intro sigma hsigma; simpa only [phi] using hslit sigma hsigma)
  have hdInt : IntervalIntegrable d (volume : Measure ℝ) 0 (1 / 2) :=
    hpairs.2.sub hpairs.1
  have hpoint : ∀ sigma ∈ Set.uIcc (0 : ℝ) (1 / 2),
      g' sigma / g sigma = d sigma := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [huIcc] using hsigma
    have hgNe : g sigma ≠ 0 := by
      dsimp only [g, speiserZetaDerivRatio]
      exact div_ne_zero (hdata sigma hsigmaIcc).2 (hdata sigma hsigmaIcc).1
    dsimp only [g']
    exact mul_div_cancel_right₀ _ hgNe
  have hquotInt : IntervalIntegrable (fun sigma => g' sigma / g sigma)
      (volume : Measure ℝ) 0 (1 / 2) := by
    apply hdInt.congr
    intro sigma hsigma
    exact (hpoint sigma (Set.uIoc_subset_uIcc hsigma)).symm
  have hformula :=
    intervalIntegral_deriv_div_eq_log_sub_of_smul_mem_slitPlane
      hc hderiv hquotInt
        (by intro sigma hsigma
            have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
              simpa only [huIcc] using hsigma
            simpa only [g, phi] using hslit sigma hsigmaIcc)
  calc
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) =
        ∫ sigma : ℝ in (0 : ℝ)..(1 / 2), g' sigma / g sigma := by
          apply intervalIntegral.integral_congr
          intro sigma hsigma
          exact (hpoint sigma hsigma).symm
    _ = Complex.log (c * g (1 / 2)) - Complex.log (c * g 0) := hformula
    _ = Complex.log
          (c * speiserZetaDerivRatio ((1 / 2 : ℂ) + t * I)) -
        Complex.log (c * speiserZetaDerivRatio (t * I)) := by
          simp only [g, phi]
          norm_num

theorem intervalIntegral_speiserRatio_vertical_of_rotatedSlit
    {c : ℂ} {r t : ℝ} (hc : c ≠ 0) (ht : 0 ≤ t) (hrOne : r ≠ 1)
    (hslit : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      c * speiserZetaDerivRatio ((r : ℂ) + y * I) ∈ Complex.slitPlane) :
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
        logDeriv riemannZeta ((r : ℂ) + y * I))) =
      Complex.log (c * speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (c * speiserZetaDerivRatio (r : ℂ)) := by
  let phi : ℝ → ℂ := fun y => (r : ℂ) + y * I
  let g : ℝ → ℂ := fun y => speiserZetaDerivRatio (phi y)
  let d : ℝ → ℂ := fun y =>
    logDeriv (deriv riemannZeta) (phi y) - logDeriv riemannZeta (phi y)
  let g' : ℝ → ℂ := fun y => I * (d y * g y)
  have huIcc : Set.uIcc (0 : ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
  have hnotone : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t → phi y ≠ 1 := by
    intro y hy hEq
    have hre := congrArg Complex.re hEq
    simp only [phi, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      Complex.one_re] at hre
    apply hrOne
    linarith
  have hdata : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      riemannZeta (phi y) ≠ 0 ∧ deriv riemannZeta (phi y) ≠ 0 := by
    intro y hy
    exact nonzero_of_speiserRatio_smul_mem_slitPlane
      (by simpa only [phi] using hslit y hy)
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) t, HasDerivAt g (g' y) y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) t := by
      simpa only [huIcc] using hy
    have houter := hasDerivAt_speiserZetaDerivRatio
      (hnotone y hyIcc) (hdata y hyIcc).1 (hdata y hyIcc).2
    have hline : HasDerivAt (fun u : ℝ => (r : ℂ) + u * I) I y := by
      have h := (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (r : ℂ))
      simpa [add_comm] using h
    change HasDerivAt
      (speiserZetaDerivRatio ∘ fun u : ℝ => (r : ℂ) + u * I) _ y
    simpa only [g', d, g, phi, smul_eq_mul] using houter.scomp y hline
  have hpairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := phi) (c := c) (a := 0) (b := t) ht (by fun_prop) hnotone
      (by intro y hy; simpa only [phi] using hslit y hy)
  have hdInt : IntervalIntegrable d (volume : Measure ℝ) 0 t :=
    hpairs.2.sub hpairs.1
  have hpoint : ∀ y ∈ Set.uIcc (0 : ℝ) t,
      g' y / g y = I * d y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) t := by
      simpa only [huIcc] using hy
    have hgNe : g y ≠ 0 := by
      dsimp only [g, speiserZetaDerivRatio]
      exact div_ne_zero (hdata y hyIcc).2 (hdata y hyIcc).1
    dsimp only [g']
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hgNe]
  have hquotInt : IntervalIntegrable (fun y => g' y / g y)
      (volume : Measure ℝ) 0 t := by
    apply (hdInt.const_mul I).congr
    intro y hy
    exact (hpoint y (Set.uIoc_subset_uIcc hy)).symm
  have hformula :=
    intervalIntegral_deriv_div_eq_log_sub_of_smul_mem_slitPlane
      hc hderiv hquotInt
        (by intro y hy
            have hyIcc : y ∈ Set.Icc (0 : ℝ) t := by
              simpa only [huIcc] using hy
            simpa only [g, phi] using hslit y hyIcc)
  calc
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
        logDeriv riemannZeta ((r : ℂ) + y * I))) =
        ∫ y : ℝ in (0 : ℝ)..t, I * d y := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ y : ℝ in (0 : ℝ)..t, g' y / g y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact (hpoint y hy).symm
    _ = Complex.log (c * g t) - Complex.log (c * g 0) := hformula
    _ = Complex.log (c * speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (c * speiserZetaDerivRatio (r : ℂ)) := by
          simp only [g, phi]
          norm_num

private theorem rotatedSlitBoundary_edgeIntegrable
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    (IntervalIntegrable
        (fun sigma : ℝ => logDeriv riemannZeta (sigma : ℂ))
        (volume : Measure ℝ) 0 (1 / 2) ∧
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv (deriv riemannZeta) (sigma : ℂ))
        (volume : Measure ℝ) 0 (1 / 2)) ∧
    (IntervalIntegrable
        (fun sigma : ℝ => logDeriv riemannZeta ((sigma : ℂ) + t * I))
        (volume : Measure ℝ) 0 (1 / 2) ∧
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I))
        (volume : Measure ℝ) 0 (1 / 2)) ∧
    (IntervalIntegrable
        (fun y : ℝ => logDeriv riemannZeta ((y : ℂ) * I))
        (volume : Measure ℝ) 0 t ∧
      IntervalIntegrable
        (fun y : ℝ => logDeriv (deriv riemannZeta) ((y : ℂ) * I))
        (volume : Measure ℝ) 0 t) ∧
    (IntervalIntegrable
        (fun y : ℝ =>
          logDeriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))
        (volume : Measure ℝ) 0 t ∧
      IntervalIntegrable
        (fun y : ℝ =>
          logDeriv (deriv riemannZeta) (((1 / 2 : ℝ) : ℂ) + y * I))
        (volume : Measure ℝ) 0 t) := by
  have hc : c ≠ 0 := h.2.1
  have ht : 0 ≤ t := h.1.le
  have hbottom : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      c * speiserZetaDerivRatio (sigma : ℂ) ∈ Complex.slitPlane :=
    h.2.2.1
  have htop : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      c * speiserZetaDerivRatio ((sigma : ℂ) + t * I) ∈ Complex.slitPlane :=
    h.2.2.2.1
  have hleft : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      c * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane :=
    h.2.2.2.2.1
  have hright : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
      c * speiserZetaDerivRatio ((1 / 2 : ℂ) + y * I) ∈ Complex.slitPlane :=
    h.2.2.2.2.2
  have hbPairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := fun sigma : ℝ => (sigma : ℂ)) (c := c)
      (a := 0) (b := 1 / 2) (by norm_num) (by fun_prop)
      (by
        intro sigma hsigma hEq
        have hre := congrArg Complex.re hEq
        norm_num at hre
        linarith [hsigma.2])
      hbottom
  have htPairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := fun sigma : ℝ => (sigma : ℂ) + t * I) (c := c)
      (a := 0) (b := 1 / 2) (by norm_num) (by fun_prop)
      (by
        intro sigma hsigma hEq
        have hre := congrArg Complex.re hEq
        norm_num at hre
        linarith [hsigma.2])
      htop
  have hlPairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := fun y : ℝ => (y : ℂ) * I) (c := c)
      (a := 0) (b := t) ht (by fun_prop)
      (by
        intro y hy hEq
        have hre := congrArg Complex.re hEq
        norm_num at hre)
      hleft
  have hrPairs := intervalIntegrable_logDeriv_pair_comp_of_rotatedSlit
    (phi := fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * I)) (c := c)
      (a := 0) (b := t) ht (by fun_prop)
      (by
        intro y hy hEq
        have hre := congrArg Complex.re hEq
        norm_num at hre)
      (by intro y hy; simpa using hright y hy)
  exact ⟨hbPairs, htPairs, hlPairs, hrPairs⟩

private def speiserOrientedBoundaryLogDerivDifference (t : ℝ) : ℂ :=
  (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) (sigma : ℂ) -
        logDeriv riemannZeta (sigma : ℂ))) -
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) +
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) (((1 / 2 : ℝ) : ℂ) + y * I) -
        logDeriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))) -
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) ((y : ℂ) * I) -
        logDeriv riemannZeta ((y : ℂ) * I)) )

private theorem rectangleBoundaryIntegral_logDerivDifference_eq_orientedEdges
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 (1 / 2) 0 t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 (1 / 2) 0 t =
      speiserOrientedBoundaryLogDerivDifference t := by
  have hedges := rotatedSlitBoundary_edgeIntegrable h
  have hbPairs := hedges.1
  have htPairs := hedges.2.1
  have hlPairs := hedges.2.2.1
  have hrPairs := hedges.2.2.2
  unfold speiserOrientedBoundaryLogDerivDifference
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_sub hbPairs.2 hbPairs.1,
    intervalIntegral.integral_sub htPairs.2 htPairs.1,
    intervalIntegral.integral_sub hrPairs.2 hrPairs.1,
    intervalIntegral.integral_sub hlPairs.2 hlPairs.1]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, mul_sub, mul_comm, add_comm]
  abel

private theorem rotatedSlitBoundary_bottomFormula
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) (sigma : ℂ) -
        logDeriv riemannZeta (sigma : ℂ))) =
      Complex.log (c * speiserZetaDerivRatio (1 / 2 : ℂ)) -
        Complex.log (c * speiserZetaDerivRatio 0) := by
  have hformula := intervalIntegral_speiserRatio_horizontal_of_rotatedSlit
    (c := c) (t := 0) h.2.1 (by
      intro sigma hsigma
      simpa using h.2.2.1 sigma hsigma)
  simpa using hformula

private theorem rotatedSlitBoundary_topFormula
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) =
      Complex.log
          (c * speiserZetaDerivRatio ((1 / 2 : ℂ) + t * I)) -
        Complex.log (c * speiserZetaDerivRatio (t * I)) := by
  exact intervalIntegral_speiserRatio_horizontal_of_rotatedSlit
    h.2.1 h.2.2.2.1

private theorem rotatedSlitBoundary_leftFormula
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) ((y : ℂ) * I) -
        logDeriv riemannZeta ((y : ℂ) * I))) =
      Complex.log (c * speiserZetaDerivRatio (t * I)) -
        Complex.log (c * speiserZetaDerivRatio 0) := by
  have hformula := intervalIntegral_speiserRatio_vertical_of_rotatedSlit
    (c := c) (r := 0) (t := t) h.2.1 h.1.le (by norm_num) (by
      intro y hy
      simpa using h.2.2.2.2.1 y hy)
  simpa using hformula

private theorem rotatedSlitBoundary_rightFormula
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    I * (∫ y : ℝ in (0 : ℝ)..t,
      (logDeriv (deriv riemannZeta) (((1 / 2 : ℝ) : ℂ) + y * I) -
        logDeriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))) =
      Complex.log
          (c * speiserZetaDerivRatio (((1 / 2 : ℝ) : ℂ) + t * I)) -
        Complex.log
          (c * speiserZetaDerivRatio (((1 / 2 : ℝ) : ℂ))) := by
  exact intervalIntegral_speiserRatio_vertical_of_rotatedSlit
    h.2.1 h.1.le (by norm_num) (by
      intro y hy
      simpa using h.2.2.2.2.2 y hy)

private def speiserRotatedSlitCornerCombination (c : ℂ) (t : ℝ) : ℂ :=
  (Complex.log (c * speiserZetaDerivRatio (1 / 2 : ℂ)) -
      Complex.log (c * speiserZetaDerivRatio 0)) -
    (Complex.log (c * speiserZetaDerivRatio ((1 / 2 : ℂ) + t * I)) -
      Complex.log (c * speiserZetaDerivRatio (t * I))) +
    (Complex.log (c * speiserZetaDerivRatio ((1 / 2 : ℂ) + t * I)) -
      Complex.log (c * speiserZetaDerivRatio (1 / 2 : ℂ))) -
    (Complex.log (c * speiserZetaDerivRatio (t * I)) -
      Complex.log (c * speiserZetaDerivRatio 0))

private theorem speiserOrientedBoundaryLogDerivDifference_eq_cornerCombination
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    speiserOrientedBoundaryLogDerivDifference t =
      speiserRotatedSlitCornerCombination c t := by
  unfold speiserOrientedBoundaryLogDerivDifference
  rw [rotatedSlitBoundary_bottomFormula h,
    rotatedSlitBoundary_topFormula h,
    rotatedSlitBoundary_rightFormula h,
    rotatedSlitBoundary_leftFormula h]
  unfold speiserRotatedSlitCornerCombination
  norm_num

private theorem speiserRotatedSlitCornerCombination_eq_zero
    (c : ℂ) (t : ℝ) :
    speiserRotatedSlitCornerCombination c t = 0 := by
  unfold speiserRotatedSlitCornerCombination
  abel

private theorem speiserOrientedBoundaryLogDerivDifference_eq_zero
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    speiserOrientedBoundaryLogDerivDifference t = 0 := by
  rw [speiserOrientedBoundaryLogDerivDifference_eq_cornerCombination h,
    speiserRotatedSlitCornerCombination_eq_zero]

theorem rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_rotatedSlit
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 (1 / 2) 0 t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 (1 / 2) 0 t = 0 := by
  rw [rectangleBoundaryIntegral_logDerivDifference_eq_orientedEdges h,
    speiserOrientedBoundaryLogDerivDifference_eq_zero h]

private theorem compactZetaStrictRectangleCount_zero_eq_speiserCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {t : ℝ} (ht : 0 < t)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[0, t]]) ⊆ K) :
    compactZetaStrictRectangleCount K hK 0 (1 / 2) 0 t =
      speiserUpperLeftZetaZeroCount t := by
  unfold compactZetaStrictRectangleCount speiserUpperLeftZetaZeroCount
  rw [compactZeta_strictRectangleFinset_eq_speiser_filter
    hK hKDomain (by norm_num) ht hrectK]
  have hfilter :
      (speiserUpperLeftZetaZeroFinset t).filter (fun u => 0 < u.im) =
        speiserUpperLeftZetaZeroFinset t := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact (mem_speiserUpperLeftZetaZeroFinset.mp hu).1.1.1
  rw [hfilter]

private theorem compactZetaDerivStrictRectangleCount_zero_eq_speiserCount
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {t : ℝ} (ht : 0 < t)
    (hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[0, t]]) ⊆ K) :
    compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) 0 t =
      speiserUpperLeftDerivZeroCount t := by
  unfold compactZetaDerivStrictRectangleCount speiserUpperLeftDerivZeroCount
  rw [compactZetaDeriv_strictRectangleFinset_eq_speiser_filter
    hK hKDomain (by norm_num) ht hrectK]
  have hfilter :
      (speiserUpperLeftDerivZeroFinset t).filter (fun u => 0 < u.im) =
        speiserUpperLeftDerivZeroFinset t := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact (mem_speiserUpperLeftDerivZeroFinset.mp hu).1.1.1
  rw [hfilter]

private theorem rotatedSlitBoundary_countDifference
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 (1 / 2) 0 t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 (1 / 2) 0 t =
      2 * (Real.pi : ℂ) * I *
        ((speiserUpperLeftDerivZeroCount t : ℂ) -
          (speiserUpperLeftZetaZeroCount t : ℂ)) := by
  let K : Set ℂ := levinsonMontgomeryCountCompactCutoff 0 t
  let V : Set ℂ := levinsonMontgomeryCountOpenCutoff 0 t
  have hK : IsCompact K :=
    isCompact_levinsonMontgomeryCountCompactCutoff 0 t
  have hKDomain : K ⊆ ({1} : Set ℂ)ᶜ :=
    levinsonMontgomeryCountCompactCutoff_subset_zetaDomain 0 t
  have hVOpen : IsOpen V := isOpen_levinsonMontgomeryCountOpenCutoff 0 t
  have hVPre : IsPreconnected V :=
    isPreconnected_levinsonMontgomeryCountOpenCutoff 0 t
  have hVK : V ⊆ K := levinsonMontgomeryCountOpenCutoff_subset_compact 0 t
  have hz0 : (1 / 4 : ℂ) ∈ V := by
    simpa only [V, Complex.ofReal_zero, zero_mul, add_zero] using
      (exists_mem_levinsonMontgomeryCountOpenCutoff h.1)
  have hrect : ([[0, (1 / 2 : ℝ)]] ×ℂ [[0, t]]) ⊆ V := by
    simpa only [V] using levinsonMontgomery_sourceRectangle_subset_openCutoff h.1
  have hbottom : ∀ sigma : ℝ, sigma ∈ [[0, (1 / 2 : ℝ)]] →
      riemannZeta (sigma : ℂ) ≠ 0 ∧ deriv riemannZeta (sigma : ℂ) ≠ 0 := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hsigma
    exact nonzero_of_speiserRatio_smul_mem_slitPlane
      (h.2.2.1 sigma hsigmaIcc)
  have htop : ∀ sigma : ℝ, sigma ∈ [[0, (1 / 2 : ℝ)]] →
      riemannZeta ((sigma : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + t * I) ≠ 0 := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hsigma
    exact nonzero_of_speiserRatio_smul_mem_slitPlane
      (h.2.2.2.1 sigma hsigmaIcc)
  have hleft : ∀ y : ℝ, y ∈ [[0, t]] →
      riemannZeta ((0 : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((0 : ℂ) + y * I) ≠ 0 := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) t := by
      simpa only [Set.uIcc_of_le h.1.le] using hy
    simpa only [Complex.ofReal_zero, zero_add] using
      (nonzero_of_speiserRatio_smul_mem_slitPlane
        (h.2.2.2.2.1 y hyIcc))
  have hright : ∀ y : ℝ, y ∈ [[0, t]] →
      riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) t := by
      simpa only [Set.uIcc_of_le h.1.le] using hy
    simpa using nonzero_of_speiserRatio_smul_mem_slitPlane
      (h.2.2.2.2.2 y hyIcc)
  have harg := levinsonMontgomery_zeroFreeRectangle_countDifference
    hK hKDomain hVOpen hVPre hVK hz0 hrect (by norm_num) h.1
      (fun sigma hsigma => by simpa using (hbottom sigma hsigma).1)
      (fun sigma hsigma => (htop sigma hsigma).1)
      (fun y hy => (hright y hy).1)
      (fun y hy => (hleft y hy).1)
      (fun sigma hsigma => by simpa using (hbottom sigma hsigma).2)
      (fun sigma hsigma => (htop sigma hsigma).2)
      (fun y hy => (hright y hy).2)
      (fun y hy => (hleft y hy).2)
  rw [sum_divisor_deriv_riemannZeta_eq_compactCount hK hKDomain
      0 (1 / 2) 0 t,
    sum_divisor_riemannZeta_eq_compactCount hK hKDomain 0 (1 / 2) 0 t,
    compactZetaDerivStrictRectangleCount_zero_eq_speiserCount
      hK hKDomain h.1 (fun z hz => hVK (hrect hz)),
    compactZetaStrictRectangleCount_zero_eq_speiserCount
      hK hKDomain h.1 (fun z hz => hVK (hrect hz))] at harg
  exact harg

theorem speiserUpperLeftCounts_eq_of_rotatedSlitBoundary
    {c : ℂ} {t : ℝ} (h : SpeiserRotatedSlitBoundary c t) :
    speiserUpperLeftDerivZeroCount t = speiserUpperLeftZetaZeroCount t := by
  have hzero :=
    rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_rotatedSlit h
  have hcount := rotatedSlitBoundary_countDifference h
  rw [hzero] at hcount
  have hfactor : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdiff :
      (speiserUpperLeftDerivZeroCount t : ℂ) -
          (speiserUpperLeftZetaZeroCount t : ℂ) = 0 :=
    (mul_eq_zero.mp hcount.symm).resolve_left hfactor
  have hcast :
      (speiserUpperLeftDerivZeroCount t : ℂ) =
        (speiserUpperLeftZetaZeroCount t : ℂ) := sub_eq_zero.mp hdiff
  have hre := congrArg Complex.re hcast
  norm_num at hre
  exact_mod_cast hre

theorem levinsonMontgomeryHeightTenCertificate_of_positiveImaginaryRayAvoidance
    (hsign : SpeiserStrictNegativeHorizontal 10)
    (hboundary : SpeiserRotatedSlitBoundary I 10) :
    LevinsonMontgomeryHeightTenCertificate := by
  exact ⟨hsign,
    speiserUpperLeftCounts_eq_of_rotatedSlitBoundary hboundary⟩

end

end LeanLab.Riemann
