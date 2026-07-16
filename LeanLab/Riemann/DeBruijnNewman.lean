import LeanLab.Riemann.LiScaffold
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

set_option linter.style.header false

/-!
# The de Bruijn-Newman heat-flow kernel

This file fixes the normalization used by de Bruijn, Newman, and the Polymath paper.  Natural
indices are shifted by one, so every series below runs over the positive integers.
-/

open Asymptotics Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The positive integer represented by a natural-number series index. -/
private def dbnIndex (n : ℕ) : ℝ := n + 1

/-- One summand of the theta tail whose second-order differential expression is the `Phi` kernel. -/
def deBruijnNewmanThetaTailTerm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp u * Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))

/-- The theta tail `exp(u) * sum_{n >= 1} exp(-pi*n^2*exp(4*u))`. -/
def deBruijnNewmanThetaTail (u : ℝ) : ℝ :=
  ∑' n : ℕ, deBruijnNewmanThetaTailTerm n u

/-- The first derivative of one theta-tail summand, written explicitly. -/
def deBruijnNewmanThetaTailDerivTerm (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp u - 4 * π * dbnIndex n ^ 2 * Real.exp (5 * u)) *
    Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))

/-- The second derivative of one theta-tail summand, written explicitly. -/
def deBruijnNewmanThetaTailSecondDerivTerm (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp u - 24 * π * dbnIndex n ^ 2 * Real.exp (5 * u) +
      16 * π ^ 2 * dbnIndex n ^ 4 * Real.exp (9 * u)) *
    Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))

/-- One summand of the source-normalized de Bruijn-Newman kernel `Phi`. -/
def deBruijnNewmanPhiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * dbnIndex n ^ 4 * Real.exp (9 * u) -
      3 * π * dbnIndex n ^ 2 * Real.exp (5 * u)) *
    Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))

theorem deBruijnNewmanPhiTerm_eq (n : ℕ) (u : ℝ) :
    deBruijnNewmanPhiTerm n u =
      (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) -
          3 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) *
        Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) := by
  rfl

/-- The source-normalized de Bruijn-Newman kernel `Phi`. -/
def deBruijnNewmanPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ, deBruijnNewmanPhiTerm n u

/-- The de Bruijn-Newman heat-flow family. -/
def deBruijnNewmanH (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    ((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (z * (u : ℂ))

theorem summable_deBruijnNewmanThetaTailTerm (u : ℝ) :
    Summable fun n : ℕ ↦ deBruijnNewmanThetaTailTerm n u := by
  have h := HurwitzKernelBounds.summable_f_nat 0 1 (Real.exp_pos (4 * u))
  simpa [deBruijnNewmanThetaTailTerm, dbnIndex, HurwitzKernelBounds.f_nat] using
    h.mul_left (Real.exp u)

theorem summable_deBruijnNewmanThetaTailDerivTerm (u : ℝ) :
    Summable fun n : ℕ ↦ deBruijnNewmanThetaTailDerivTerm n u := by
  have h0 := (HurwitzKernelBounds.summable_f_nat 0 1 (Real.exp_pos (4 * u))).mul_left
    (Real.exp u)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (4 * u))).mul_left
    (4 * π * Real.exp (5 * u))
  apply (h0.sub h2).congr
  intro n
  simp only [deBruijnNewmanThetaTailDerivTerm, dbnIndex,
    HurwitzKernelBounds.f_nat]
  ring

theorem summable_deBruijnNewmanThetaTailSecondDerivTerm (u : ℝ) :
    Summable fun n : ℕ ↦ deBruijnNewmanThetaTailSecondDerivTerm n u := by
  have h0 := (HurwitzKernelBounds.summable_f_nat 0 1 (Real.exp_pos (4 * u))).mul_left
    (Real.exp u)
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (4 * u))).mul_left
    (24 * π * Real.exp (5 * u))
  have h4 := (HurwitzKernelBounds.summable_f_nat 4 1 (Real.exp_pos (4 * u))).mul_left
    (16 * π ^ 2 * Real.exp (9 * u))
  apply ((h0.sub h2).add h4).congr
  intro n
  simp only [deBruijnNewmanThetaTailSecondDerivTerm, dbnIndex,
    HurwitzKernelBounds.f_nat]
  ring

theorem summable_deBruijnNewmanPhiTerm (u : ℝ) :
    Summable fun n : ℕ ↦ deBruijnNewmanPhiTerm n u := by
  have h4 := (HurwitzKernelBounds.summable_f_nat 4 1 (Real.exp_pos (4 * u))).mul_left
    (2 * π ^ 2 * Real.exp (9 * u))
  have h2 := (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (4 * u))).mul_left
    (3 * π * Real.exp (5 * u))
  apply (h4.sub h2).congr
  intro n
  simp only [deBruijnNewmanPhiTerm, dbnIndex, HurwitzKernelBounds.f_nat]
  ring

theorem hasDerivAt_deBruijnNewmanThetaTailTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (deBruijnNewmanThetaTailTerm n)
      (deBruijnNewmanThetaTailDerivTerm n u) u := by
  have hinner : HasDerivAt
      (fun x : ℝ ↦ -π * dbnIndex n ^ 2 * Real.exp (4 * x))
      ((-π * dbnIndex n ^ 2) * (4 * Real.exp (4 * u))) u := by
    have hraw := ((hasDerivAt_id u).const_mul 4).exp.const_mul
      (-π * dbnIndex n ^ 2)
    refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
    · simp only [id_eq]
    · simp only [id_eq]
      ring
  have hexp5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hraw := (hasDerivAt_id u).exp.mul hinner.exp
  unfold deBruijnNewmanThetaTailTerm deBruijnNewmanThetaTailDerivTerm
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply, id_eq]
  · simp only [id_eq]
    rw [hexp5]
    ring

theorem hasDerivAt_deBruijnNewmanThetaTailDerivTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (deBruijnNewmanThetaTailDerivTerm n)
      (deBruijnNewmanThetaTailSecondDerivTerm n u) u := by
  have hcoeff : HasDerivAt
      (fun x : ℝ ↦ Real.exp x - 4 * π * dbnIndex n ^ 2 * Real.exp (5 * x))
      (Real.exp u - 20 * π * dbnIndex n ^ 2 * Real.exp (5 * u)) u := by
    have hraw := (hasDerivAt_id u).exp.sub
      (((hasDerivAt_id u).const_mul 5).exp.const_mul (4 * π * dbnIndex n ^ 2))
    refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
    · simp only [Pi.sub_apply, id_eq]
    · simp only [id_eq]
      ring
  have hinner : HasDerivAt
      (fun x : ℝ ↦ -π * dbnIndex n ^ 2 * Real.exp (4 * x))
      ((-π * dbnIndex n ^ 2) * (4 * Real.exp (4 * u))) u := by
    have hraw := ((hasDerivAt_id u).const_mul 4).exp.const_mul
      (-π * dbnIndex n ^ 2)
    refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
    · simp only [id_eq]
    · simp only [id_eq]
      ring
  have hexp5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hraw := hcoeff.mul hinner.exp
  unfold deBruijnNewmanThetaTailDerivTerm deBruijnNewmanThetaTailSecondDerivTerm
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply]
  · rw [hexp5, hexp9, hexp5]
    ring

theorem deBruijnNewmanThetaTailSecondDerivTerm_sub_self
    (n : ℕ) (u : ℝ) :
    deBruijnNewmanThetaTailSecondDerivTerm n u -
        deBruijnNewmanThetaTailTerm n u =
      8 * deBruijnNewmanPhiTerm n u := by
  simp only [deBruijnNewmanThetaTailSecondDerivTerm, deBruijnNewmanThetaTailTerm,
    deBruijnNewmanPhiTerm]
  ring

theorem tsum_deBruijnNewmanThetaTailSecondDerivTerm_sub_self (u : ℝ) :
    (∑' n : ℕ, deBruijnNewmanThetaTailSecondDerivTerm n u) -
        deBruijnNewmanThetaTail u =
      8 * deBruijnNewmanPhi u := by
  rw [deBruijnNewmanThetaTail, deBruijnNewmanPhi,
    ← (summable_deBruijnNewmanThetaTailSecondDerivTerm u).tsum_sub
      (summable_deBruijnNewmanThetaTailTerm u), ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact deBruijnNewmanThetaTailSecondDerivTerm_sub_self n u

/-- A summable majorant for first derivatives of theta-tail terms on `(-1, 1)`. -/
private def dbnThetaTailDerivBound (n : ℕ) : ℝ :=
  Real.exp 1 * HurwitzKernelBounds.f_nat 0 1 (Real.exp (-4)) n +
    (4 * π * Real.exp 5) * HurwitzKernelBounds.f_nat 2 1 (Real.exp (-4)) n

private theorem summable_dbnThetaTailDerivBound : Summable dbnThetaTailDerivBound := by
  apply ((HurwitzKernelBounds.summable_f_nat 0 1 (Real.exp_pos (-4))).mul_left
    (Real.exp 1)).add
  exact (HurwitzKernelBounds.summable_f_nat 2 1 (Real.exp_pos (-4))).mul_left
    (4 * π * Real.exp 5)

private theorem norm_deBruijnNewmanThetaTailDerivTerm_le_bound
    (n : ℕ) {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    ‖deBruijnNewmanThetaTailDerivTerm n u‖ ≤ dbnThetaTailDerivBound n := by
  have hpi : 0 ≤ π := pi_pos.le
  have hm : 0 ≤ dbnIndex n ^ 2 := sq_nonneg _
  have hcoeff : 0 ≤ 4 * π * dbnIndex n ^ 2 := by positivity
  have hu1 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.mpr hu.2.le
  have hu5 : Real.exp (5 * u) ≤ Real.exp 5 := by
    apply Real.exp_le_exp.mpr
    linarith [hu.2]
  have hu4 : Real.exp (-4) ≤ Real.exp (4 * u) := by
    apply Real.exp_le_exp.mpr
    linarith [hu.1]
  have hgauss :
      Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u)) ≤
        Real.exp (-π * dbnIndex n ^ 2 * Real.exp (-4)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, mul_assoc] using
      neg_le_neg (mul_le_mul_of_nonneg_left hu4 (mul_nonneg hpi hm))
  rw [Real.norm_eq_abs, deBruijnNewmanThetaTailDerivTerm, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    |Real.exp u - 4 * π * dbnIndex n ^ 2 * Real.exp (5 * u)| *
          Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u)) ≤
        (Real.exp u + 4 * π * dbnIndex n ^ 2 * Real.exp (5 * u)) *
          Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u)) := by
      gcongr
      exact (abs_sub _ _).trans_eq (by rw [abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (mul_nonneg hcoeff (Real.exp_pos _).le)])
    _ ≤ (Real.exp 1 + 4 * π * dbnIndex n ^ 2 * Real.exp 5) *
          Real.exp (-π * dbnIndex n ^ 2 * Real.exp (-4)) := by
      gcongr
    _ = dbnThetaTailDerivBound n := by
      simp only [dbnThetaTailDerivBound, HurwitzKernelBounds.f_nat, dbnIndex]
      ring

theorem hasDerivAt_deBruijnNewmanThetaTail_zero :
    HasDerivAt deBruijnNewmanThetaTail
      (∑' n : ℕ, deBruijnNewmanThetaTailDerivTerm n 0) 0 := by
  have h := hasDerivAt_tsum_of_isPreconnected
    summable_dbnThetaTailDerivBound isOpen_Ioo isPreconnected_Ioo
    (fun n u _ ↦ hasDerivAt_deBruijnNewmanThetaTailTerm n u)
    (fun n u hu ↦ norm_deBruijnNewmanThetaTailDerivTerm_le_bound n hu)
    (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)
    (summable_deBruijnNewmanThetaTailTerm 0)
    (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)
  simpa only [deBruijnNewmanThetaTail] using! h

private theorem F_nat_zero_one_eq_cosKernel_sub_one_div_two {x : ℝ} (hx : 0 < x) :
    HurwitzKernelBounds.F_nat 0 1 x = (HurwitzZeta.cosKernel 0 x - 1) / 2 := by
  have hsum := (HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx).tsum_eq
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  apply (eq_div_iff htwo).2
  rw [HurwitzKernelBounds.F_nat, ← tsum_mul_right]
  simpa only [HurwitzKernelBounds.f_nat, pow_zero, one_mul, zero_mul,
    Real.cos_zero, mul_one, mul_comm] using! hsum

theorem deBruijnNewmanThetaTail_eq_cosKernel (u : ℝ) :
    deBruijnNewmanThetaTail u =
      Real.exp u * (HurwitzZeta.cosKernel 0 (Real.exp (4 * u)) - 1) / 2 := by
  rw [deBruijnNewmanThetaTail]
  have hfun : (fun n : ℕ ↦ deBruijnNewmanThetaTailTerm n u) =
      fun n : ℕ ↦ Real.exp u *
        HurwitzKernelBounds.f_nat 0 1 (Real.exp (4 * u)) n := by
    funext n
    simp [deBruijnNewmanThetaTailTerm, HurwitzKernelBounds.f_nat, dbnIndex]
  rw [hfun, tsum_mul_left, ← HurwitzKernelBounds.F_nat,
    F_nat_zero_one_eq_cosKernel_sub_one_div_two (Real.exp_pos (4 * u))]
  ring

private theorem cosKernel_zero_exp_neg_four (u : ℝ) :
    HurwitzZeta.cosKernel 0 (Real.exp (-4 * u)) =
      Real.exp (2 * u) * HurwitzZeta.cosKernel 0 (Real.exp (4 * u)) := by
  have h := HurwitzZeta.evenKernel_functional_equation 0 (Real.exp (-4 * u))
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at h
  rw [h]
  have hrpow : Real.exp (-4 * u) ^ (1 / 2 : ℝ) = Real.exp (-2 * u) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hrpow]
  rw [show -2 * u = -(2 * u) by ring, Real.exp_neg, one_div, inv_inv]
  congr 1
  rw [one_div, show -4 * u = -(4 * u) by ring, Real.exp_neg, inv_inv]

theorem deBruijnNewmanThetaTail_neg (u : ℝ) :
    deBruijnNewmanThetaTail (-u) =
      deBruijnNewmanThetaTail u + Real.sinh u := by
  rw [deBruijnNewmanThetaTail_eq_cosKernel,
    deBruijnNewmanThetaTail_eq_cosKernel]
  rw [show 4 * -u = -4 * u by ring, cosKernel_zero_exp_neg_four]
  rw [Real.sinh_eq]
  have hexp : Real.exp (-u) * Real.exp (2 * u) = Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub, ← mul_assoc, hexp]
  ring

theorem tsum_deBruijnNewmanThetaTailDerivTerm_zero :
    (∑' n : ℕ, deBruijnNewmanThetaTailDerivTerm n 0) = -1 / 2 := by
  let D : ℝ := ∑' n : ℕ, deBruijnNewmanThetaTailDerivTerm n 0
  have hD : HasDerivAt deBruijnNewmanThetaTail D 0 := by
    simpa only [D] using hasDerivAt_deBruijnNewmanThetaTail_zero
  have hleft : HasDerivAt (fun u : ℝ ↦ deBruijnNewmanThetaTail (-u)) (-D) 0 := by
    have hDneg : HasDerivAt deBruijnNewmanThetaTail D (-0) := by simpa using hD
    simpa only [Function.comp_apply, neg_zero, mul_neg, mul_one] using!
      hDneg.comp 0 (hasDerivAt_neg 0)
  have hright : HasDerivAt
      (fun u : ℝ ↦ deBruijnNewmanThetaTail u + Real.sinh u) (D + 1) 0 := by
    simpa only [Pi.add_apply, Real.cosh_zero] using!
      hD.add (Real.hasDerivAt_sinh 0)
  have hleft' : HasDerivAt
      (fun u : ℝ ↦ deBruijnNewmanThetaTail u + Real.sinh u) (-D) 0 :=
    hleft.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun u ↦
      (deBruijnNewmanThetaTail_neg u).symm
  have hvalue : -D = D + 1 := hleft'.unique hright
  change D = -1 / 2
  linarith

private theorem tendsto_dbn_exp_dominates (a : ℝ) (ha : 0 < a) (r : ℝ) :
    Tendsto (fun u : ℝ ↦ a * Real.exp (4 * u) - r * u) atTop atTop := by
  have hlinear : Tendsto (fun u : ℝ ↦ 8 * a * u - r) atTop atTop := by
    exact tendsto_atTop_add_const_right _ (-r)
      (tendsto_id.const_mul_atTop (by positivity : 0 < 8 * a))
  have hquadratic : Tendsto (fun u : ℝ ↦ u * (8 * a * u - r)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ hlinear
  apply tendsto_atTop_mono' atTop
    (eventually_atTop.2 ⟨0, fun u hu ↦ by
      have hexp := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 * u by positivity)
      have hsquare : 8 * u ^ 2 ≤ Real.exp (4 * u) := by
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hsquare ha.le
      nlinarith⟩)
    hquadratic

theorem integrableOn_dbn_exp_mul_exp_neg_exp
    (a : ℝ) (ha : 0 < a) (r : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)))
      (Ioi 0) := by
  have htop : Tendsto
      (fun u : ℝ ↦ (r * u - a * Real.exp (4 * u)) - (-u)) atTop atBot := by
    rw [← tendsto_neg_atTop_iff]
    convert tendsto_dbn_exp_dominates a ha (r + 1) using 1
    · funext u
      ring
  have hbigO :
      (fun u : ℝ ↦ Real.exp (r * u - a * Real.exp (4 * u))) =O[atTop]
        fun u : ℝ ↦ Real.exp (-1 * u) := by
    apply Real.isBigO_exp_comp_exp_comp.mpr
    have heq :
        (fun u : ℝ ↦ r * u - a * Real.exp (4 * u)) - (fun u : ℝ ↦ -1 * u) =
          fun u : ℝ ↦ (r * u - a * Real.exp (4 * u)) - (-u) := by
      funext u
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact Tendsto.isBoundedUnder_le_atBot htop
  have hint := integrable_of_isBigO_exp_neg (a := (0 : ℝ)) zero_lt_one
    (by fun_prop : ContinuousOn
      (fun u : ℝ ↦ Real.exp (r * u - a * Real.exp (4 * u))) (Ici 0)) hbigO
  apply hint.congr_fun
  · intro u _
    change Real.exp (r * u - a * Real.exp (4 * u)) =
      Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u))
    rw [sub_eq_add_neg, Real.exp_add]
    congr 1
    ring_nf
  · exact measurableSet_Ioi

private theorem norm_complex_cos_le_exp_norm (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.cos, norm_div, Complex.norm_two]
  calc
    ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ / 2 ≤
        (‖Complex.exp (w * I)‖ + ‖Complex.exp (-w * I)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) / 2 := by
      gcongr
      · rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        exact (Complex.re_le_norm _).trans_eq (by simp)
      · rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        exact (Complex.re_le_norm _).trans_eq (by simp)
    _ = Real.exp ‖w‖ := by ring

private theorem norm_complex_sin_le_exp_norm (w : ℂ) :
    ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.sin, norm_div, Complex.norm_two, norm_mul, norm_I, mul_one]
  calc
    ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ / 2 ≤
        (‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖) / 2 := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) / 2 := by
      gcongr
      · rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        exact (Complex.re_le_norm _).trans_eq (by simp)
      · rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        exact (Complex.re_le_norm _).trans_eq (by simp)
    _ = Real.exp ‖w‖ := by ring

theorem norm_complex_cos_mul_real_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) := by
  convert norm_complex_cos_le_exp_norm (z * (u : ℂ)) using 1
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

theorem norm_complex_sin_mul_real_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.sin (z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) := by
  convert norm_complex_sin_le_exp_norm (z * (u : ℂ)) using 1
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

private theorem integrableOn_dbn_expKernel_mul_cos
    (a : ℝ) (ha : 0 < a) (r : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        ((Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hmajor := integrableOn_dbn_exp_mul_exp_neg_exp a ha (r + ‖z‖)
  apply Integrable.mono' hmajor
  · fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    calc
      Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
        Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) *
          Real.exp (‖z‖ * u) := by
        gcongr
        exact norm_complex_cos_mul_real_le z hu0
      _ = Real.exp ((r + ‖z‖) * u) * Real.exp (-a * Real.exp (4 * u)) := by
        rw [show (r + ‖z‖) * u = r * u + ‖z‖ * u by ring, Real.exp_add]
        ring

private theorem integrableOn_dbn_expKernel_mul_sin
    (a : ℝ) (ha : 0 < a) (r : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        ((Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) : ℝ) : ℂ) *
          Complex.sin (z * (u : ℂ)))
      (Ioi 0) := by
  have hmajor := integrableOn_dbn_exp_mul_exp_neg_exp a ha (r + ‖z‖)
  apply Integrable.mono' hmajor
  · fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    calc
      Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) *
          ‖Complex.sin (z * (u : ℂ))‖ ≤
        Real.exp (r * u) * Real.exp (-a * Real.exp (4 * u)) *
          Real.exp (‖z‖ * u) := by
        gcongr
        exact norm_complex_sin_mul_real_le z hu0
      _ = Real.exp ((r + ‖z‖) * u) * Real.exp (-a * Real.exp (4 * u)) := by
        rw [show (r + ‖z‖) * u = r * u + ‖z‖ * u by ring, Real.exp_add]
        ring

private theorem dbnGaussianCoefficient_pos (n : ℕ) :
    0 < π * dbnIndex n ^ 2 := by
  apply mul_pos pi_pos
  apply sq_pos_of_pos
  unfold dbnIndex
  positivity

theorem integrableOn_deBruijnNewmanThetaTailTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailTerm n u : ℂ) *
        Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have h := integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 1 z
  apply h.congr_fun
  · intro u _
    simp only [deBruijnNewmanThetaTailTerm, one_mul]
    push_cast
    ring_nf
  · exact measurableSet_Ioi

theorem integrableOn_deBruijnNewmanThetaTailTerm_mul_sin (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailTerm n u : ℂ) *
        Complex.sin (z * (u : ℂ)))
      (Ioi 0) := by
  have h := integrableOn_dbn_expKernel_mul_sin
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 1 z
  apply h.congr_fun
  · intro u _
    simp only [deBruijnNewmanThetaTailTerm, one_mul]
    push_cast
    ring_nf
  · exact measurableSet_Ioi

theorem integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_sin (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
        Complex.sin (z * (u : ℂ)))
      (Ioi 0) := by
  have h1 := integrableOn_dbn_expKernel_mul_sin
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 1 z
  have h5 := (integrableOn_dbn_expKernel_mul_sin
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 5 z).const_mul
      ((4 * π * dbnIndex n ^ 2 : ℝ) : ℂ)
  apply (h1.sub h5).congr_fun
  · intro u _
    simp only [Pi.sub_apply, deBruijnNewmanThetaTailDerivTerm]
    push_cast
    ring_nf
  · exact measurableSet_Ioi

theorem integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
        Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have h1 := integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 1 z
  have h5 := (integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 5 z).const_mul
      ((4 * π * dbnIndex n ^ 2 : ℝ) : ℂ)
  apply (h1.sub h5).congr_fun
  · intro u _
    simp only [Pi.sub_apply, deBruijnNewmanThetaTailDerivTerm]
    push_cast
    ring_nf
  · exact measurableSet_Ioi

theorem integrableOn_deBruijnNewmanThetaTailSecondDerivTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
        Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have h1 := integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 1 z
  have h5 := (integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 5 z).const_mul
      ((24 * π * dbnIndex n ^ 2 : ℝ) : ℂ)
  have h9 := (integrableOn_dbn_expKernel_mul_cos
    (π * dbnIndex n ^ 2) (dbnGaussianCoefficient_pos n) 9 z).const_mul
      ((16 * π ^ 2 * dbnIndex n ^ 4 : ℝ) : ℂ)
  apply ((h1.sub h5).add h9).congr_fun
  · intro u _
    simp only [Pi.sub_apply, Pi.add_apply, deBruijnNewmanThetaTailSecondDerivTerm]
    push_cast
    ring_nf
  · exact measurableSet_Ioi

private theorem hasDerivAt_dbn_cos (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Complex.cos (z * (v : ℂ)))
      (-z * Complex.sin (z * (u : ℂ))) u := by
  have hcomplex := (Complex.hasDerivAt_cos (z * (u : ℂ))).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).const_mul z)
  have hreal := hcomplex.comp_ofReal
  apply hreal.congr_deriv
  ring

private theorem hasDerivAt_dbn_sin (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Complex.sin (z * (v : ℂ)))
      (z * Complex.cos (z * (u : ℂ))) u := by
  have hcomplex := (Complex.hasDerivAt_sin (z * (u : ℂ))).comp (u : ℂ)
    ((hasDerivAt_id (u : ℂ)).const_mul z)
  have hreal := hcomplex.comp_ofReal
  apply hreal.congr_deriv
  ring

private theorem hasDerivAt_ofReal_deBruijnNewmanThetaTailTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (deBruijnNewmanThetaTailTerm n v : ℂ))
      (deBruijnNewmanThetaTailDerivTerm n u : ℂ) u :=
  (hasDerivAt_deBruijnNewmanThetaTailTerm n u).ofReal_comp

private theorem hasDerivAt_ofReal_deBruijnNewmanThetaTailDerivTerm (n : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n v : ℂ))
      (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) u :=
  (hasDerivAt_deBruijnNewmanThetaTailDerivTerm n u).ofReal_comp

private theorem hasDerivAt_dbn_thetaDeriv_mul_cos (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n v : ℂ) *
        Complex.cos (z * (v : ℂ)))
      ((deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
          Complex.cos (z * (u : ℂ)) +
        (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
          (-z * Complex.sin (z * (u : ℂ)))) u :=
  (hasDerivAt_ofReal_deBruijnNewmanThetaTailDerivTerm n u).mul (hasDerivAt_dbn_cos z u)

private theorem hasDerivAt_dbn_theta_mul_sin (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ (deBruijnNewmanThetaTailTerm n v : ℂ) *
        Complex.sin (z * (v : ℂ)))
      ((deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
          Complex.sin (z * (u : ℂ)) +
        (deBruijnNewmanThetaTailTerm n u : ℂ) *
          (z * Complex.cos (z * (u : ℂ)))) u :=
  (hasDerivAt_ofReal_deBruijnNewmanThetaTailTerm n u).mul (hasDerivAt_dbn_sin z u)

private theorem integrableOn_dbn_thetaDeriv_mul_cos_deriv (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
            Complex.cos (z * (u : ℂ)) +
          (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
            (-z * Complex.sin (z * (u : ℂ))))
      (Ioi 0) := by
  have hsecond := integrableOn_deBruijnNewmanThetaTailSecondDerivTerm_mul_cos n z
  have hfirst :=
    (integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_sin n z).const_mul (-z)
  apply (hsecond.add hfirst).congr_fun
  · intro u _
    simp only [Pi.add_apply]
    ring
  · exact measurableSet_Ioi

private theorem integrableOn_dbn_theta_mul_sin_deriv (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
            Complex.sin (z * (u : ℂ)) +
          (deBruijnNewmanThetaTailTerm n u : ℂ) *
            (z * Complex.cos (z * (u : ℂ))))
      (Ioi 0) := by
  have hfirst := integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_sin n z
  have hzero := (integrableOn_deBruijnNewmanThetaTailTerm_mul_cos n z).const_mul z
  apply (hfirst.add hzero).congr_fun
  · intro u _
    simp only [Pi.add_apply]
    ring
  · exact measurableSet_Ioi

private theorem tendsto_dbn_thetaDeriv_mul_cos_atTop (n : ℕ) (z : ℂ) :
    Tendsto
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
        Complex.cos (z * (u : ℂ)))
      atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun u _ ↦ hasDerivAt_dbn_thetaDeriv_mul_cos n z u)
    (integrableOn_dbn_thetaDeriv_mul_cos_deriv n z)
    (integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_cos n z)

private theorem tendsto_dbn_theta_mul_sin_atTop (n : ℕ) (z : ℂ) :
    Tendsto
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailTerm n u : ℂ) *
        Complex.sin (z * (u : ℂ)))
      atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun u _ ↦ hasDerivAt_dbn_theta_mul_sin n z u)
    (integrableOn_dbn_theta_mul_sin_deriv n z)
    (integrableOn_deBruijnNewmanThetaTailTerm_mul_sin n z)

private theorem integral_Ioi_dbn_thetaDeriv_mul_cos_deriv (n : ℕ) (z : ℂ) :
    (∫ u : ℝ in Ioi 0,
      (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
          Complex.cos (z * (u : ℂ)) +
        (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
          (-z * Complex.sin (z * (u : ℂ)))) =
      -(deBruijnNewmanThetaTailDerivTerm n 0 : ℂ) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := (0 : ℂ))
    (fun u _ ↦ hasDerivAt_dbn_thetaDeriv_mul_cos n z u)
    (integrableOn_dbn_thetaDeriv_mul_cos_deriv n z)
    (tendsto_dbn_thetaDeriv_mul_cos_atTop n z)
  simpa using h

private theorem integral_Ioi_dbn_theta_mul_sin_deriv (n : ℕ) (z : ℂ) :
    (∫ u : ℝ in Ioi 0,
      (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
          Complex.sin (z * (u : ℂ)) +
        (deBruijnNewmanThetaTailTerm n u : ℂ) *
          (z * Complex.cos (z * (u : ℂ)))) = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (m := (0 : ℂ))
    (fun u _ ↦ hasDerivAt_dbn_theta_mul_sin n z u)
    (integrableOn_dbn_theta_mul_sin_deriv n z)
    (tendsto_dbn_theta_mul_sin_atTop n z)
  simpa using h

theorem integrableOn_deBruijnNewmanPhiTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanPhiTerm n u : ℂ) *
        Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hsecond := integrableOn_deBruijnNewmanThetaTailSecondDerivTerm_mul_cos n z
  have hzero := integrableOn_deBruijnNewmanThetaTailTerm_mul_cos n z
  have h := (hsecond.sub hzero).const_mul ((1 / 8 : ℝ) : ℂ)
  apply h.congr
  filter_upwards with u
  simp only [Pi.sub_apply, deBruijnNewmanThetaTailSecondDerivTerm,
    deBruijnNewmanThetaTailTerm, deBruijnNewmanPhiTerm]
  push_cast
  ring_nf

theorem integral_Ioi_deBruijnNewmanPhiTerm_mul_cos (n : ℕ) (z : ℂ) :
    (∫ u : ℝ in Ioi 0,
      (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
      (-(deBruijnNewmanThetaTailDerivTerm n 0 : ℂ) -
          (1 + z ^ 2) *
            ∫ u : ℝ in Ioi 0,
              (deBruijnNewmanThetaTailTerm n u : ℂ) *
                Complex.cos (z * (u : ℂ))) / 8 := by
  let A : ℂ := ∫ u : ℝ in Ioi 0,
    (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
      Complex.cos (z * (u : ℂ))
  let B : ℂ := ∫ u : ℝ in Ioi 0,
    (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
      Complex.sin (z * (u : ℂ))
  let C : ℂ := ∫ u : ℝ in Ioi 0,
    (deBruijnNewmanThetaTailTerm n u : ℂ) *
      Complex.cos (z * (u : ℂ))
  have hfirstPart : IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
        (-z * Complex.sin (z * (u : ℂ)))) (Ioi 0) := by
    have h := (integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_sin n z).const_mul (-z)
    apply h.congr
    filter_upwards with u
    ring
  have hzeroPart : IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTailTerm n u : ℂ) *
        (z * Complex.cos (z * (u : ℂ)))) (Ioi 0) := by
    have h := (integrableOn_deBruijnNewmanThetaTailTerm_mul_cos n z).const_mul z
    apply h.congr
    filter_upwards with u
    ring
  have h1 := integral_Ioi_dbn_thetaDeriv_mul_cos_deriv n z
  rw [integral_add
    (integrableOn_deBruijnNewmanThetaTailSecondDerivTerm_mul_cos n z)
    hfirstPart] at h1
  have hfirstIntegral :
      (∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTailDerivTerm n u : ℂ) *
          (-z * Complex.sin (z * (u : ℂ)))) = -z * B := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rw [hfirstIntegral] at h1
  change A + -z * B = -(deBruijnNewmanThetaTailDerivTerm n 0 : ℂ) at h1
  have h2 := integral_Ioi_dbn_theta_mul_sin_deriv n z
  rw [integral_add
    (integrableOn_deBruijnNewmanThetaTailDerivTerm_mul_sin n z)
    hzeroPart] at h2
  have hzeroIntegral :
      (∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTailTerm n u : ℂ) *
          (z * Complex.cos (z * (u : ℂ)))) = z * C := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rw [hzeroIntegral] at h2
  change B + z * C = 0 at h2
  have hphi :
      8 * (∫ u : ℝ in Ioi 0,
        (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) = A - C := by
    rw [← integral_const_mul]
    change (∫ u : ℝ in Ioi 0,
      8 * ((deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)))) = A - C
    rw [← integral_sub
      (integrableOn_deBruijnNewmanThetaTailSecondDerivTerm_mul_cos n z)
      (integrableOn_deBruijnNewmanThetaTailTerm_mul_cos n z)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    change 8 * ((deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
      (deBruijnNewmanThetaTailSecondDerivTerm n u : ℂ) *
          Complex.cos (z * (u : ℂ)) -
        (deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ))
    rw [← sub_mul]
    have hcast := congrArg ((↑) : ℝ → ℂ)
      (deBruijnNewmanThetaTailSecondDerivTerm_sub_self n u)
    push_cast at hcast
    rw [hcast]
    ring
  apply (eq_div_iff (by norm_num : (8 : ℂ) ≠ 0)).2
  rw [mul_comm _ (8 : ℂ), hphi]
  linear_combination h1 + z * h2

private theorem integrable_dbnGaussianMajor (r : ℝ) :
    Integrable (fun u : ℝ ↦ Real.exp (r * u - 8 * π * u ^ 2)) := by
  let c : ℝ := r / (16 * π)
  have hbase : Integrable (fun u : ℝ ↦ Real.exp (-(8 * π) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity : 0 < 8 * π)
  have hshift := Integrable.comp_sub_right hbase c
  have hscaled := hshift.const_mul (Real.exp (r ^ 2 / (32 * π)))
  apply hscaled.congr
  filter_upwards with u
  change Real.exp (r ^ 2 / (32 * π)) * Real.exp (-(8 * π) * (u - c) ^ 2) =
    Real.exp (r * u - 8 * π * u ^ 2)
  rw [← Real.exp_add]
  congr 1
  dsimp [c]
  field_simp [pi_ne_zero]
  ring

private def dbnPowerKernelTerm (k : ℕ) (r : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  dbnIndex n ^ k * Real.exp (r * u) *
    Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))

private def dbnPowerKernelMajor (k : ℕ) (r : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  HurwitzKernelBounds.f_nat k 1 1 n * Real.exp (r * u - 8 * π * u ^ 2)

private theorem norm_dbnPowerKernelTerm_mul_cos_le_major
    (k : ℕ) (r : ℝ) (n : ℕ) (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖((dbnPowerKernelTerm k r n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖ ≤
      dbnPowerKernelMajor k (r + ‖z‖) n u := by
  have hm1 : 1 ≤ dbnIndex n ^ 2 := by
    have hm : 1 ≤ dbnIndex n := by
      unfold dbnIndex
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  have hexpLower : 1 + 8 * u ^ 2 ≤ Real.exp (4 * u) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 * u by positivity)
    nlinarith
  have hpoly :
      π * dbnIndex n ^ 2 + 8 * π * u ^ 2 ≤
        π * dbnIndex n ^ 2 * (1 + 8 * u ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hm1
      (mul_nonneg (by positivity : 0 ≤ 8 * π) (sq_nonneg u))
    nlinarith
  have htotal :
      π * dbnIndex n ^ 2 + 8 * π * u ^ 2 ≤
      π * dbnIndex n ^ 2 * Real.exp (4 * u) :=
    hpoly.trans (mul_le_mul_of_nonneg_left hexpLower (by positivity))
  have hmk : 0 ≤ dbnIndex n ^ k := by
    apply pow_nonneg
    unfold dbnIndex
    positivity
  dsimp only [dbnPowerKernelTerm]
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg hmk (Real.exp_pos _).le) (Real.exp_pos _).le)]
  calc
    (dbnIndex n ^ k * Real.exp (r * u) *
        Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))) *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
      (dbnIndex n ^ k * Real.exp (r * u) *
        Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u))) *
          Real.exp (‖z‖ * u) := by
      exact mul_le_mul_of_nonneg_left (norm_complex_cos_mul_real_le z hu)
        (mul_nonneg (mul_nonneg hmk (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ ≤ dbnIndex n ^ k * Real.exp (r * u) *
          Real.exp (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) *
          Real.exp (‖z‖ * u) := by
      have hg :
          Real.exp (-π * dbnIndex n ^ 2 * Real.exp (4 * u)) ≤
            Real.exp (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hneg := neg_le_neg htotal
        nlinarith
      have hleft := mul_le_mul_of_nonneg_left hg
        (mul_nonneg hmk (Real.exp_pos (r * u)).le)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hleft (Real.exp_pos (‖z‖ * u)).le
    _ = dbnPowerKernelMajor k (r + ‖z‖) n u := by
      have hexp :
          Real.exp (r * u) *
              Real.exp (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) *
              Real.exp (‖z‖ * u) =
            Real.exp (-π * dbnIndex n ^ 2) *
              Real.exp ((r + ‖z‖) * u - 8 * π * u ^ 2) := by
        calc
          _ = Real.exp
              (r * u + (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) + ‖z‖ * u) := by
                rw [Real.exp_add, Real.exp_add]
          _ = Real.exp
              (-π * dbnIndex n ^ 2 + ((r + ‖z‖) * u - 8 * π * u ^ 2)) := by
                congr 1
                ring
          _ = _ := by rw [Real.exp_add]
      rw [show dbnIndex n ^ k * Real.exp (r * u) *
            Real.exp (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) *
            Real.exp (‖z‖ * u) =
          dbnIndex n ^ k *
            (Real.exp (r * u) *
              Real.exp (-π * dbnIndex n ^ 2 - 8 * π * u ^ 2) *
              Real.exp (‖z‖ * u)) by ring, hexp]
      simp only [dbnPowerKernelMajor, HurwitzKernelBounds.f_nat, dbnIndex]
      ring_nf

private theorem integrableOn_dbnPowerKernelTerm_mul_cos
    (k : ℕ) (r : ℝ) (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ ((dbnPowerKernelTerm k r n u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hmajor : IntegrableOn (dbnPowerKernelMajor k (r + ‖z‖) n) (Ioi 0) := by
    have hbase : IntegrableOn
        (fun u : ℝ ↦ Real.exp ((r + ‖z‖) * u - 8 * π * u ^ 2)) (Ioi 0) :=
      (integrable_dbnGaussianMajor (r + ‖z‖)).integrableOn
    have h := hbase.const_mul (HurwitzKernelBounds.f_nat k 1 1 n)
    apply h.congr
    filter_upwards with u
    rfl
  apply Integrable.mono' hmajor
  · apply Continuous.aestronglyMeasurable
    unfold dbnPowerKernelTerm
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_dbnPowerKernelTerm_mul_cos_le_major k r n z hu.le

private theorem summable_integral_norm_dbnPowerKernelTerm_mul_cos
    (k : ℕ) (r : ℝ) (z : ℂ) :
    Summable fun n : ℕ ↦
      ∫ u : ℝ in Ioi 0,
        ‖((dbnPowerKernelTerm k r n u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))‖ := by
  let K : ℝ := ∫ u : ℝ in Ioi 0, Real.exp ((r + ‖z‖) * u - 8 * π * u ^ 2)
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ (Real.exp_pos _).le
  have hmajorSummable :=
    (HurwitzKernelBounds.summable_f_nat k 1 (by norm_num : (0 : ℝ) < 1)).mul_right K
  apply hmajorSummable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ norm_nonneg _)]
  have hterm := (integrableOn_dbnPowerKernelTerm_mul_cos k r n z).norm
  have hmajor : IntegrableOn (dbnPowerKernelMajor k (r + ‖z‖) n) (Ioi 0) := by
    have hbase : IntegrableOn
        (fun u : ℝ ↦ Real.exp ((r + ‖z‖) * u - 8 * π * u ^ 2)) (Ioi 0) :=
      (integrable_dbnGaussianMajor (r + ‖z‖)).integrableOn
    have h := hbase.const_mul (HurwitzKernelBounds.f_nat k 1 1 n)
    apply h.congr
    filter_upwards with u
    rfl
  calc
    (∫ u : ℝ in Ioi 0,
        ‖((dbnPowerKernelTerm k r n u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))‖) ≤
        ∫ u : ℝ in Ioi 0, dbnPowerKernelMajor k (r + ‖z‖) n u := by
      apply integral_mono_ae hterm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_dbnPowerKernelTerm_mul_cos_le_major k r n z hu.le
    _ = HurwitzKernelBounds.f_nat k 1 1 n * K := by
      rw [← integral_const_mul]
      rfl

private theorem tsum_integral_dbnPowerKernelTerm_mul_cos
    (k : ℕ) (r : ℝ) (z : ℂ) :
    (∑' n : ℕ,
      ∫ u : ℝ in Ioi 0,
        ((dbnPowerKernelTerm k r n u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))) =
      ∫ u : ℝ in Ioi 0,
        ∑' n : ℕ,
          ((dbnPowerKernelTerm k r n u : ℝ) : ℂ) *
            Complex.cos (z * (u : ℂ)) := by
  exact integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi 0))
    (fun n ↦ integrableOn_dbnPowerKernelTerm_mul_cos k r n z)
    (summable_integral_norm_dbnPowerKernelTerm_mul_cos k r z)

private theorem dbnPowerKernelTerm_zero_one (n : ℕ) (u : ℝ) :
    dbnPowerKernelTerm 0 1 n u = deBruijnNewmanThetaTailTerm n u := by
  simp [dbnPowerKernelTerm, deBruijnNewmanThetaTailTerm]

theorem tsum_integral_deBruijnNewmanThetaTailTerm_mul_cos (z : ℂ) :
    (∑' n : ℕ,
      ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTailTerm n u : ℂ) *
          Complex.cos (z * (u : ℂ))) =
      ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  calc
    _ = ∑' n : ℕ,
        ∫ u : ℝ in Ioi 0,
          ((dbnPowerKernelTerm 0 1 n u : ℝ) : ℂ) *
            Complex.cos (z * (u : ℂ)) := by
      apply tsum_congr
      intro n
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      change (deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) =
        (dbnPowerKernelTerm 0 1 n u : ℂ) * Complex.cos (z * (u : ℂ))
      rw [dbnPowerKernelTerm_zero_one]
    _ = ∫ u : ℝ in Ioi 0,
        ∑' n : ℕ,
          ((dbnPowerKernelTerm 0 1 n u : ℝ) : ℂ) *
            Complex.cos (z * (u : ℂ)) :=
      tsum_integral_dbnPowerKernelTerm_mul_cos 0 1 z
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      simp_rw [dbnPowerKernelTerm_zero_one]
      rw [tsum_mul_right, ← Complex.ofReal_tsum]
      rfl

private theorem deBruijnNewmanPhiTerm_eq_powerKernel (n : ℕ) (u : ℝ) :
    deBruijnNewmanPhiTerm n u =
      2 * π ^ 2 * dbnPowerKernelTerm 4 9 n u -
        3 * π * dbnPowerKernelTerm 2 5 n u := by
  simp only [deBruijnNewmanPhiTerm, dbnPowerKernelTerm]
  ring

private theorem summable_integral_norm_deBruijnNewmanPhiTerm_mul_cos (z : ℂ) :
    Summable fun n : ℕ ↦
      ∫ u : ℝ in Ioi 0,
        ‖(deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖ := by
  let S4 : ℕ → ℝ := fun n ↦ ∫ u : ℝ in Ioi 0,
    ‖((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖
  let S2 : ℕ → ℝ := fun n ↦ ∫ u : ℝ in Ioi 0,
    ‖((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖
  have h4 : Summable S4 := summable_integral_norm_dbnPowerKernelTerm_mul_cos 4 9 z
  have h2 : Summable S2 := summable_integral_norm_dbnPowerKernelTerm_mul_cos 2 5 z
  have hmajor : Summable fun n ↦ 2 * π ^ 2 * S4 n + 3 * π * S2 n :=
    (h4.mul_left (2 * π ^ 2)).add (h2.mul_left (3 * π))
  apply hmajor.of_norm_bounded
  intro n
  have hphiNorm := (integrableOn_deBruijnNewmanPhiTerm_mul_cos n z).norm
  have hp4Norm := (integrableOn_dbnPowerKernelTerm_mul_cos 4 9 n z).norm
  have hp2Norm := (integrableOn_dbnPowerKernelTerm_mul_cos 2 5 n z).norm
  have hmajorInt : IntegrableOn
      (fun u : ℝ ↦
        2 * π ^ 2 *
            ‖((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖ +
          3 * π *
            ‖((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖)
      (Ioi 0) :=
    (hp4Norm.const_mul (2 * π ^ 2)).add (hp2Norm.const_mul (3 * π))
  have hpointwise : ∀ u : ℝ,
      ‖(deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖ ≤
        2 * π ^ 2 *
            ‖((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖ +
          3 * π *
            ‖((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖ := by
    intro u
    have hrewrite :
        (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) =
          ((2 * π ^ 2 : ℝ) : ℂ) *
              ((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)) -
            ((3 * π : ℝ) : ℂ) *
              ((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)) := by
      rw [deBruijnNewmanPhiTerm_eq_powerKernel]
      push_cast
      ring
    rw [hrewrite]
    calc
      _ = ‖((2 * π ^ 2 : ℝ) : ℂ) *
              (((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))) -
            ((3 * π : ℝ) : ℂ) *
              (((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))‖ := by
        congr 1
        ring
      _ ≤ ‖((2 * π ^ 2 : ℝ) : ℂ) *
              (((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))‖ +
            ‖((3 * π : ℝ) : ℂ) *
              (((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ)))‖ :=
        norm_sub_le _ _
      _ = _ := by
        simp only [norm_mul, norm_real, Real.norm_eq_abs]
        rw [abs_of_pos pi_pos, abs_of_nonneg (sq_nonneg π)]
        norm_num
  rw [Real.norm_eq_abs,
    abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi fun _ _ ↦ norm_nonneg _)]
  calc
    (∫ u : ℝ in Ioi 0,
      ‖(deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖) ≤
        ∫ u : ℝ in Ioi 0,
          (2 * π ^ 2 *
              ‖((dbnPowerKernelTerm 4 9 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖ +
            3 * π *
              ‖((dbnPowerKernelTerm 2 5 n u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))‖) := by
      apply integral_mono_ae hphiNorm hmajorInt
      exact Filter.Eventually.of_forall hpointwise
    _ = 2 * π ^ 2 * S4 n + 3 * π * S2 n := by
      rw [integral_add (hp4Norm.const_mul (2 * π ^ 2)) (hp2Norm.const_mul (3 * π)),
        integral_const_mul, integral_const_mul]

theorem tsum_integral_deBruijnNewmanPhiTerm_mul_cos (z : ℂ) :
    (∑' n : ℕ,
      ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
      ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanPhi u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  calc
    _ = ∫ u : ℝ in Ioi 0,
        ∑' n : ℕ,
          (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) :=
      integral_tsum_of_summable_integral_norm
        (μ := volume.restrict (Ioi 0))
        (fun n ↦ integrableOn_deBruijnNewmanPhiTerm_mul_cos n z)
        (summable_integral_norm_deBruijnNewmanPhiTerm_mul_cos z)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      change (∑' n : ℕ,
          (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
        (deBruijnNewmanPhi u : ℂ) * Complex.cos (z * (u : ℂ))
      rw [tsum_mul_right, ← Complex.ofReal_tsum]
      rfl

private theorem deBruijnNewmanThetaTail_eq_exp_mul_F_nat (u : ℝ) :
    deBruijnNewmanThetaTail u =
      Real.exp u * HurwitzKernelBounds.F_nat 0 1 (Real.exp (4 * u)) := by
  rw [deBruijnNewmanThetaTail]
  simp only [deBruijnNewmanThetaTailTerm, HurwitzKernelBounds.F_nat,
    HurwitzKernelBounds.f_nat, pow_zero, one_mul, dbnIndex]
  rw [tsum_mul_left]

private theorem norm_complex_exp_le_exp_norm (w : ℂ) :
    ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (Complex.re_le_norm w)

private theorem norm_complex_exp_I_mul_real_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.exp (I * z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) := by
  convert norm_complex_exp_le_exp_norm (I * z * (u : ℂ)) using 1
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu]

private theorem norm_complex_exp_neg_I_mul_real_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.exp (-I * z * (u : ℂ))‖ ≤ Real.exp (‖z‖ * u) := by
  convert norm_complex_exp_le_exp_norm (-I * z * (u : ℂ)) using 1
  rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu]

private theorem norm_deBruijnNewmanThetaTail_le (u : ℝ) (hu : 0 ≤ u) :
    ‖deBruijnNewmanThetaTail u‖ ≤
      Real.exp u * ((1 - Real.exp (-π))⁻¹ *
        Real.exp (-π * Real.exp (4 * u))) := by
  rw [deBruijnNewmanThetaTail_eq_exp_mul_F_nat, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hx : 1 ≤ Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  calc
    Real.exp u * ‖HurwitzKernelBounds.F_nat 0 1 (Real.exp (4 * u))‖ ≤
        Real.exp u *
          (Real.exp (-π * 1 ^ 2 * Real.exp (4 * u)) /
            (1 - Real.exp (-π * Real.exp (4 * u)))) := by
      gcongr
      exact HurwitzKernelBounds.F_nat_zero_le zero_le_one
        (Real.exp_pos (4 * u))
    _ ≤ Real.exp u * ((1 - Real.exp (-π))⁻¹ *
        Real.exp (-π * Real.exp (4 * u))) := by
      gcongr
      simpa only [one_pow, mul_one] using
        rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le hx

private theorem measurable_deBruijnNewmanThetaTail :
    Measurable deBruijnNewmanThetaTail := by
  change Measurable (fun u : ℝ ↦ ∑' n : ℕ, deBruijnNewmanThetaTailTerm n u)
  exact Measurable.tsum fun n ↦ by
    unfold deBruijnNewmanThetaTailTerm
    fun_prop

private theorem integrableOn_deBruijnNewmanThetaTail_mul_exp_I
    (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTail u : ℂ) *
        Complex.exp (I * z * (u : ℂ))) (Ioi 0) := by
  have hbase := integrableOn_dbn_exp_mul_exp_neg_exp π pi_pos (1 + ‖z‖)
  have hmajor := hbase.const_mul ((1 - Real.exp (-π))⁻¹)
  apply Integrable.mono' hmajor
  · exact ((Complex.continuous_ofReal.measurable.comp
      measurable_deBruijnNewmanThetaTail).mul (by fun_prop)).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hden : 0 < 1 - Real.exp (-π) := by
      simpa only [mul_one] using
        one_sub_rexp_neg_pi_mul_pos_of_pos (x := 1) zero_lt_one
    calc
      ‖(deBruijnNewmanThetaTail u : ℂ) * Complex.exp (I * z * (u : ℂ))‖ =
          ‖deBruijnNewmanThetaTail u‖ * ‖Complex.exp (I * z * (u : ℂ))‖ := by
        rw [norm_mul, norm_real]
      _ ≤ (Real.exp u * ((1 - Real.exp (-π))⁻¹ *
            Real.exp (-π * Real.exp (4 * u)))) *
          ‖Complex.exp (I * z * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (norm_deBruijnNewmanThetaTail_le u hu0)
          (norm_nonneg _)
      _ ≤ (Real.exp u * ((1 - Real.exp (-π))⁻¹ *
            Real.exp (-π * Real.exp (4 * u)))) * Real.exp (‖z‖ * u) :=
        mul_le_mul_of_nonneg_left (norm_complex_exp_I_mul_real_le z hu0) (by positivity)
      _ = (1 - Real.exp (-π))⁻¹ *
          (Real.exp ((1 + ‖z‖) * u) * Real.exp (-π * Real.exp (4 * u))) := by
        rw [show (1 + ‖z‖) * u = u + ‖z‖ * u by ring, Real.exp_add]
        ring

private theorem integrableOn_deBruijnNewmanThetaTail_mul_exp_neg_I
    (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTail u : ℂ) *
        Complex.exp (-I * z * (u : ℂ))) (Ioi 0) := by
  have hbase := integrableOn_dbn_exp_mul_exp_neg_exp π pi_pos (1 + ‖z‖)
  have hmajor := hbase.const_mul ((1 - Real.exp (-π))⁻¹)
  apply Integrable.mono' hmajor
  · exact ((Complex.continuous_ofReal.measurable.comp
      measurable_deBruijnNewmanThetaTail).mul (by fun_prop)).aestronglyMeasurable.restrict
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hden : 0 < 1 - Real.exp (-π) := by
      simpa only [mul_one] using
        one_sub_rexp_neg_pi_mul_pos_of_pos (x := 1) zero_lt_one
    calc
      ‖(deBruijnNewmanThetaTail u : ℂ) * Complex.exp (-I * z * (u : ℂ))‖ =
          ‖deBruijnNewmanThetaTail u‖ * ‖Complex.exp (-I * z * (u : ℂ))‖ := by
        rw [norm_mul, norm_real]
      _ ≤ (Real.exp u * ((1 - Real.exp (-π))⁻¹ *
            Real.exp (-π * Real.exp (4 * u)))) *
          ‖Complex.exp (-I * z * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_right (norm_deBruijnNewmanThetaTail_le u hu0)
          (norm_nonneg _)
      _ ≤ (Real.exp u * ((1 - Real.exp (-π))⁻¹ *
            Real.exp (-π * Real.exp (4 * u)))) * Real.exp (‖z‖ * u) :=
        mul_le_mul_of_nonneg_left (norm_complex_exp_neg_I_mul_real_le z hu0) (by positivity)
      _ = (1 - Real.exp (-π))⁻¹ *
          (Real.exp ((1 + ‖z‖) * u) * Real.exp (-π * Real.exp (4 * u))) := by
        rw [show (1 + ‖z‖) * u = u + ‖z‖ * u by ring, Real.exp_add]
        ring

private theorem hurwitzEvenFEPair_zero_g_modif_eq_f_modif :
    (HurwitzZeta.hurwitzEvenFEPair 0).g_modif =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif := by
  change (HurwitzZeta.hurwitzEvenFEPair 0).symm.f_modif =
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
  rw [HurwitzZeta.hurwitzEvenFEPair_zero_symm]

private theorem hurwitzEvenFEPair_zero_f_modif_inv {x : ℝ} (hx : 0 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [hurwitzEvenFEPair_zero_g_modif_eq_f_modif] at h
  simpa [HurwitzZeta.hurwitzEvenFEPair, smul_eq_mul] using h

private theorem mellin_hurwitzEvenFEPair_zero_eq_integral_split (q : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif q =
      (∫ x : ℝ in Ioo 0 1,
        (x : ℂ) ^ (q - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) +
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ (q - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  let G : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (q - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  have hM := (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin q
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa only [G, MellinConvergent, WeakFEPair.toStrongFEPair,
      smul_eq_mul] using hM.1
  unfold mellin
  change (∫ x : ℝ in Ioi 0, G x) =
    (∫ x : ℝ in Ioo 0 1, G x) + ∫ x : ℝ in Ioi 1, G x
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hG.mono_set (by intro x hx; exact Ioc_subset_Ioi_self hx))
    (hG.mono_set (by intro x hx; exact zero_lt_one.trans (by simpa using hx)))]
  rw [integral_Ioc_eq_integral_Ioo]

private theorem dbn_cpow_inversion_algebra (q A : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((((x⁻¹ : ℝ) : ℂ) ^ (q - 1)) *
          (((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * A)) =
      (x : ℂ) ^ ((1 / 2 - q) - 1) * A := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have harg : Complex.arg (x : ℂ) ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [ofReal_cpow hx.le, ofReal_cpow hx.le, Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  calc
    (x : ℂ) ^ ((-2 : ℝ) : ℂ) *
          ((x : ℂ) ^ (-(q - 1)) * ((x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * A)) =
        (((x : ℂ) ^ ((-2 : ℝ) : ℂ) * (x : ℂ) ^ (-(q - 1))) *
          (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) * A := by ring
    _ = ((x : ℂ) ^ (((-2 : ℝ) : ℂ) + -(q - 1)) *
          (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)) * A := by
      rw [Complex.cpow_add _ _ hxC]
    _ = (x : ℂ) ^
          ((((-2 : ℝ) : ℂ) + -(q - 1)) + ((1 / 2 : ℝ) : ℂ)) * A := by
      conv_rhs => rw [Complex.cpow_add _ _ hxC]
    _ = (x : ℂ) ^ ((1 / 2 - q) - 1) * A := by
      congr 2
      norm_num
      ring

private theorem integral_Ioo_mellin_f_modif_eq_integral_Ioi (q : ℂ) :
    (∫ x : ℝ in Ioo 0 1,
      (x : ℂ) ^ (q - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ ((1 / 2 - q) - 1) *
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  let f : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (q - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  let g : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator f
  let h : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ ((1 / 2 - q) - 1) *
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have hright : (∫ y : ℝ in Ioi 0, g y) = ∫ y : ℝ in Ioo 0 1, f y := by
    rw [show g = (Ioo (0 : ℝ) 1).indicator f by rfl,
      setIntegral_indicator measurableSet_Ioo]
    have hset : Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      tauto
    rw [hset]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ((|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        (Ioi (1 : ℝ)).indicator h x := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [Real.rpow_neg_one]
    by_cases hx1 : 1 < x
    · have hinv0 : 0 < x⁻¹ := inv_pos.mpr hx0
      have hinv1 : x⁻¹ < 1 := inv_lt_one₀ hx0 |>.2 hx1
      rw [show g = (Ioo (0 : ℝ) 1).indicator f by rfl,
        Set.indicator_of_mem (show x⁻¹ ∈ Ioo (0 : ℝ) 1 from ⟨hinv0, hinv1⟩),
        Set.indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx1)]
      dsimp only [f, h]
      rw [show (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x⁻¹ =
          ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x by
        simpa only [one_div] using hurwitzEvenFEPair_zero_f_modif_inv hx0]
      rw [show (-1 : ℝ) - 1 = -2 by norm_num, abs_neg, abs_one, one_mul,
        Complex.real_smul]
      exact dbn_cpow_inversion_algebra q _ hx0
    · have hx1le : x ≤ 1 := not_lt.mp hx1
      have hinv1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).2 hx1le
      rw [show g = (Ioo (0 : ℝ) 1).indicator f by rfl,
        Set.indicator_of_notMem (show x⁻¹ ∉ Ioo (0 : ℝ) 1 by
          intro hmem
          exact (not_lt_of_ge hinv1) hmem.2),
        Set.indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx1)]
      simp
  have hleft :
      (∫ x : ℝ in Ioi 0,
        (|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x : ℝ in Ioi 1, h x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator h x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact hpoint
      _ = ∫ x : ℝ in Ioi (0 : ℝ) ∩ Ioi 1, h x :=
        setIntegral_indicator measurableSet_Ioi
      _ = ∫ x : ℝ in Ioi 1, h x := by
        have hset : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by
          ext x
          simp only [mem_inter_iff, mem_Ioi]
          constructor
          · exact fun hx ↦ hx.2
          · exact fun hx ↦ ⟨zero_lt_one.trans hx, hx⟩
        rw [hset]
  change (∫ x : ℝ in Ioo 0 1, f x) = ∫ x : ℝ in Ioi 1, h x
  calc
    _ = ∫ y : ℝ in Ioi 0, g y := hright.symm
    _ = ∫ x : ℝ in Ioi 0,
        (|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ)) := hsub.symm
    _ = _ := hleft

private theorem hurwitzEvenFEPair_zero_f_modif_exp_four (u : ℝ) (hu : 0 < u) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u)) =
      ((2 * Real.exp (-u) * deBruijnNewmanThetaTail u : ℝ) : ℂ) := by
  have hx : 1 < Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by positivity)
  rw [hurwitzEvenFEPair_zero_f_modif_of_one_lt hx,
    HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  norm_cast
  rw [deBruijnNewmanThetaTail_eq_cosKernel, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

private theorem image_exp_four_Ioi :
    (fun u : ℝ ↦ Real.exp (4 * u)) '' Ioi 0 = Ioi 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_Ioi, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos (by norm_num) hu)
  · intro hx
    have hxpos : 0 < x := zero_lt_one.trans hx
    refine ⟨Real.log x / 4, ?_, ?_⟩
    · rw [mem_Ioi]
      exact div_pos (Real.log_pos hx) (by norm_num)
    · change Real.exp (4 * (Real.log x / 4)) = x
      rw [show 4 * (Real.log x / 4) = Real.log x by ring,
        Real.exp_log hxpos]

private theorem image_exp_four_Ici :
    (fun u : ℝ ↦ Real.exp (4 * u)) '' Ici 0 = Ici 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_Ici, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (by norm_num) hu)
  · intro hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    refine ⟨Real.log x / 4, ?_, ?_⟩
    · rw [mem_Ici]
      exact div_nonneg (Real.log_nonneg hx) (by norm_num)
    · change Real.exp (4 * (Real.log x / 4)) = x
      rw [show 4 * (Real.log x / 4) = Real.log x by ring,
        Real.exp_log hxpos]

private theorem continuousOn_hurwitzEvenFEPair_zero_f_modif_Ioi_one :
    ContinuousOn (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Ioi 1) := by
  have heven : ContinuousOn
      (fun x : ℝ ↦ (HurwitzZeta.evenKernel 0 x : ℂ)) (Ioi 1) := by
    exact Complex.continuous_ofReal.comp_continuousOn
      ((HurwitzZeta.continuousOn_evenKernel 0).mono
        (fun x hx ↦ by
          simpa only [mem_Ioi] using
            (zero_lt_one.trans (show (1 : ℝ) < x from hx))))
  have hkernel : ContinuousOn
      (fun x : ℝ ↦ (HurwitzZeta.evenKernel 0 x : ℂ) - 1) (Ioi 1) :=
    heven.sub continuousOn_const
  exact hkernel.congr fun x hx ↦
    hurwitzEvenFEPair_zero_f_modif_of_one_lt hx

private theorem continuousOn_mellin_f_modif_Ioi_one (q : ℂ) :
    ContinuousOn
      (fun x : ℝ ↦ (x : ℂ) ^ (q - 1) *
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) (Ioi 1) := by
  have hpow : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (q - 1)) (Ioi 1) :=
    Complex.continuous_ofReal.continuousOn.cpow_const fun x hx ↦
      Complex.ofReal_mem_slitPlane.2 (zero_lt_one.trans hx)
  exact hpow.mul continuousOn_hurwitzEvenFEPair_zero_f_modif_Ioi_one

private theorem ofReal_exp_four_cpow (u : ℝ) (q : ℂ) :
    ((Real.exp (4 * u) : ℝ) : ℂ) ^ q =
      Complex.exp (((4 * u : ℝ) : ℂ) * q) := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (4 * u))),
    ← Complex.ofReal_log (Real.exp_pos (4 * u)).le, Real.log_exp]

private theorem dbn_mellin_exp_substitution_integrand
    (w : ℂ) {u : ℝ} (hu : 0 < u) :
    (4 * Real.exp (4 * u)) •
        ((((Real.exp (4 * u) : ℝ) : ℂ) ^ (((1 + w) / 4) - 1)) *
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (4 * u))) =
      8 * ((deBruijnNewmanThetaTail u : ℂ) *
        Complex.exp (w * (u : ℂ))) := by
  rw [hurwitzEvenFEPair_zero_f_modif_exp_four u hu,
    ofReal_exp_four_cpow]
  simp only [Complex.real_smul]
  push_cast
  calc
    (4 * Complex.exp (4 * (u : ℂ))) *
          (Complex.exp ((4 * (u : ℂ)) * ((1 + w) / 4 - 1)) *
            (2 * Complex.exp (-(u : ℂ)) * (deBruijnNewmanThetaTail u : ℂ))) =
        8 * (deBruijnNewmanThetaTail u : ℂ) *
          (Complex.exp (4 * (u : ℂ)) *
            Complex.exp ((4 * (u : ℂ)) * ((1 + w) / 4 - 1)) *
            Complex.exp (-(u : ℂ))) := by ring
    _ = 8 * (deBruijnNewmanThetaTail u : ℂ) *
          Complex.exp (4 * (u : ℂ) +
            (4 * (u : ℂ)) * ((1 + w) / 4 - 1) + -(u : ℂ)) := by
      rw [Complex.exp_add, Complex.exp_add]
    _ = 8 * ((deBruijnNewmanThetaTail u : ℂ) *
          Complex.exp (w * (u : ℂ))) := by
      rw [show 4 * (u : ℂ) +
          (4 * (u : ℂ)) * ((1 + w) / 4 - 1) + -(u : ℂ) =
          w * (u : ℂ) by
        ring]
      ring

private theorem integral_Ioi_mellin_f_modif_eq_thetaTail_exp
    (w : ℂ)
    (hInt : IntegrableOn
      (fun u : ℝ ↦ (deBruijnNewmanThetaTail u : ℂ) *
        Complex.exp (w * (u : ℂ))) (Ioi 0)) :
    (∫ x : ℝ in Ioi 1,
      (x : ℂ) ^ (((1 + w) / 4) - 1) *
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      8 * ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTail u : ℂ) * Complex.exp (w * (u : ℂ)) := by
  let G : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (((1 + w) / 4) - 1) *
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  have hM := (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin
    ((1 + w) / 4)
  have hGall : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa only [G, MellinConvergent, WeakFEPair.toStrongFEPair,
      smul_eq_mul] using hM.1
  have hG : IntegrableOn G (Ioi (1 : ℝ)) :=
    hGall.mono_set fun x hx ↦ by
      simpa only [mem_Ioi] using (zero_lt_one.trans (show (1 : ℝ) < x from hx))
  have hchange := integral_deriv_smul_comp_Ioi
    (f := fun u : ℝ ↦ Real.exp (4 * u))
    (f' := fun u : ℝ ↦ 4 * Real.exp (4 * u))
    (g := G) (a := (0 : ℝ))
    (by fun_prop : ContinuousOn (fun u : ℝ ↦ Real.exp (4 * u)) (Ici 0))
    (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)))
    (by
      intro x _
      simpa only [Function.comp_def, mul_comm] using
        ((Real.hasDerivAt_exp (4 * x)).comp x
          (hasDerivAt_const_mul (x := x) 4)).hasDerivWithinAt)
    (by
      rw [image_exp_four_Ioi]
      exact continuousOn_mellin_f_modif_Ioi_one ((1 + w) / 4))
    (by
      rw [image_exp_four_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
      exact hG)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      change IntegrableOn
        (fun u : ℝ ↦ (4 * Real.exp (4 * u)) • G (Real.exp (4 * u))) (Ioi 0)
      have h8 : IntegrableOn
          (fun u : ℝ ↦ (8 : ℂ) *
            ((deBruijnNewmanThetaTail u : ℂ) *
              Complex.exp (w * (u : ℂ)))) (Ioi 0) :=
        hInt.const_mul (8 : ℂ)
      apply h8.congr_fun
      · intro u hu
        exact (dbn_mellin_exp_substitution_integrand w
          (show 0 < u from hu)).symm
      · exact measurableSet_Ioi)
  change (∫ x : ℝ in Ioi 1, G x) = _
  calc
    _ = ∫ u : ℝ in Ioi 0,
        (4 * Real.exp (4 * u)) • G (Real.exp (4 * u)) := by
      simpa only [Function.comp_apply, Real.exp_zero, mul_zero] using hchange.symm
    _ = ∫ u : ℝ in Ioi 0,
        8 * ((deBruijnNewmanThetaTail u : ℂ) *
          Complex.exp (w * (u : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact dbn_mellin_exp_substitution_integrand w (show 0 < u from hu)
    _ = _ := by
      rw [integral_const_mul]

private theorem dbn_thetaTail_exp_pair_eq_cos (z : ℂ) (u : ℝ) :
    (deBruijnNewmanThetaTail u : ℂ) *
          Complex.exp (-I * z * (u : ℂ)) +
        (deBruijnNewmanThetaTail u : ℂ) *
          Complex.exp (I * z * (u : ℂ)) =
      2 * ((deBruijnNewmanThetaTail u : ℂ) *
        Complex.cos (z * (u : ℂ))) := by
  rw [Complex.cos]
  have hneg : -I * z * (u : ℂ) = -(z * (u : ℂ)) * I := by ring
  have hpos : I * z * (u : ℂ) = (z * (u : ℂ)) * I := by ring
  rw [hneg, hpos]
  ring

theorem mellin_hurwitzEvenFEPair_zero_critical_line (z : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif ((1 + I * z) / 4) =
      16 * ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  have hminusInt := integrableOn_deBruijnNewmanThetaTail_mul_exp_neg_I z
  have hplusInt := integrableOn_deBruijnNewmanThetaTail_mul_exp_I z
  have hminus := integral_Ioi_mellin_f_modif_eq_thetaTail_exp
    (-I * z) hminusInt
  have hplus := integral_Ioi_mellin_f_modif_eq_thetaTail_exp
    (I * z) hplusInt
  have hq : (1 / 2 - (1 + I * z) / 4 : ℂ) = (1 - I * z) / 4 := by ring
  rw [mellin_hurwitzEvenFEPair_zero_eq_integral_split,
    integral_Ioo_mellin_f_modif_eq_integral_Ioi, hq]
  rw [show (1 + -I * z : ℂ) = 1 - I * z by ring] at hminus
  rw [hminus, hplus]
  calc
    8 * (∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (-I * z * (u : ℂ))) +
        8 * (∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (I * z * (u : ℂ))) =
      8 * ((∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (-I * z * (u : ℂ))) +
        ∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (I * z * (u : ℂ))) := by ring
    _ = 8 * (∫ u : ℝ in Ioi 0,
        ((deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (-I * z * (u : ℂ)) +
          (deBruijnNewmanThetaTail u : ℂ) *
            Complex.exp (I * z * (u : ℂ)))) := by
      rw [integral_add hminusInt hplusInt]
    _ = 8 * (∫ u : ℝ in Ioi 0,
        2 * ((deBruijnNewmanThetaTail u : ℂ) *
          Complex.cos (z * (u : ℂ)))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      exact dbn_thetaTail_exp_pair_eq_cos z u
    _ = _ := by
      rw [integral_const_mul]
      ring

theorem completedRiemannZeta₀_critical_line_eq_thetaTailIntegral (z : ℂ) :
    completedRiemannZeta₀ ((1 + I * z) / 2) =
      8 * ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀
  change mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
      (((1 + I * z) / 2) / 2) / 2 = _
  rw [show ((1 + I * z) / 2) / 2 = (1 + I * z) / 4 by ring,
    mellin_hurwitzEvenFEPair_zero_critical_line]
  ring

private theorem summable_integral_deBruijnNewmanThetaTailTerm_mul_cos (z : ℂ) :
    Summable fun n : ℕ ↦
      ∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  have hnorm := summable_integral_norm_dbnPowerKernelTerm_mul_cos 0 1 z
  apply hnorm.of_norm_bounded
  intro n
  calc
    ‖∫ u : ℝ in Ioi 0,
        (deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖ ≤
      ∫ u : ℝ in Ioi 0,
        ‖(deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u : ℝ in Ioi 0,
        ‖((dbnPowerKernelTerm 0 1 n u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))‖ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      change
        ‖(deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ))‖ =
          ‖(dbnPowerKernelTerm 0 1 n u : ℂ) * Complex.cos (z * (u : ℂ))‖
      rw [dbnPowerKernelTerm_zero_one]

theorem integral_Ioi_deBruijnNewmanPhi_mul_cos (z : ℂ) :
    (∫ u : ℝ in Ioi 0,
      (deBruijnNewmanPhi u : ℂ) * Complex.cos (z * (u : ℂ))) =
      (1 / 2 - (1 + z ^ 2) *
        ∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ))) / 8 := by
  let J : ℕ → ℂ := fun n ↦ ∫ u : ℝ in Ioi 0,
    (deBruijnNewmanThetaTailTerm n u : ℂ) * Complex.cos (z * (u : ℂ))
  have hJ : Summable J := summable_integral_deBruijnNewmanThetaTailTerm_mul_cos z
  have hD : Summable fun n : ℕ ↦ (deBruijnNewmanThetaTailDerivTerm n 0 : ℂ) := by
    exact Complex.summable_ofReal.mpr
      (summable_deBruijnNewmanThetaTailDerivTerm 0)
  calc
    _ = ∑' n : ℕ,
        ∫ u : ℝ in Ioi 0,
          (deBruijnNewmanPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) :=
      (tsum_integral_deBruijnNewmanPhiTerm_mul_cos z).symm
    _ = ∑' n : ℕ,
        (-(deBruijnNewmanThetaTailDerivTerm n 0 : ℂ) - (1 + z ^ 2) * J n) / 8 := by
      apply tsum_congr
      intro n
      exact integral_Ioi_deBruijnNewmanPhiTerm_mul_cos n z
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [tsum_mul_right,
        hD.neg.tsum_sub (hJ.mul_left (1 + z ^ 2)),
        tsum_neg, tsum_mul_left]
      rw [← Complex.ofReal_tsum, tsum_deBruijnNewmanThetaTailDerivTerm_zero]
      rw [tsum_integral_deBruijnNewmanThetaTailTerm_mul_cos]
      norm_num

theorem deBruijnNewmanH_zero_eq_thetaTailIntegral (z : ℂ) :
    deBruijnNewmanH 0 z =
      (1 / 2 - (1 + z ^ 2) *
        ∫ u : ℝ in Ioi 0,
          (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ))) / 8 := by
  rw [deBruijnNewmanH]
  simp only [zero_mul, Real.exp_zero, one_mul]
  exact integral_Ioi_deBruijnNewmanPhi_mul_cos z

/-- The source-normalized de Bruijn-Newman transform at `t = 0` is the
project-local Riemann xi function on the critical-line parametrization. -/
theorem deBruijnNewmanH_zero_eq_riemannXi (z : ℂ) :
    deBruijnNewmanH 0 z =
      (1 / 8) * riemannXi ((1 + I * z) / 2) := by
  rw [deBruijnNewmanH_zero_eq_thetaTailIntegral, riemannXi,
    completedRiemannZeta₀_critical_line_eq_thetaTailIntegral]
  ring_nf
  simp only [Complex.I_sq]
  ring

end


end LeanLab.Riemann
