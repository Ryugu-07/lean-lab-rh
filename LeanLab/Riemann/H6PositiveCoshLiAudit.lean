import LeanLab.Riemann.DeBruijnNewmanLiMoments
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false

/-!
# Positive-cosh third-Li audit

This module gives a positive two-atom hyperbolic transform whose first two standard Li
differential expressions are positive and whose third is negative. It isolates a generic
positive-kernel obstruction and makes no assertion about the theta kernel or RH.
-/

open Complex Filter Real

namespace LeanLab.Riemann

noncomputable section

private def h6PositiveCoshAtom (u : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh ((2 * s - 1) * (u : ℂ)) / (Real.cosh u : ℂ)

private def h6PositiveCoshAtomD1 (u : ℝ) (s : ℂ) : ℂ :=
  Complex.sinh ((2 * s - 1) * (u : ℂ)) * (2 * (u : ℂ)) /
    (Real.cosh u : ℂ)

private def h6PositiveCoshAtomD2 (u : ℝ) (s : ℂ) : ℂ :=
  Complex.cosh ((2 * s - 1) * (u : ℂ)) * (2 * (u : ℂ)) ^ 2 /
    (Real.cosh u : ℂ)

private def h6PositiveCoshAtomD3 (u : ℝ) (s : ℂ) : ℂ :=
  Complex.sinh ((2 * s - 1) * (u : ℂ)) * (2 * (u : ℂ)) *
    (2 * (u : ℂ)) ^ 2 /
    (Real.cosh u : ℂ)

private theorem hasDerivAt_h6PositiveCoshAtom_arg (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ ↦ (2 * z - 1) * (u : ℂ)) (2 * (u : ℂ)) s := by
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const 1).mul_const (u : ℂ)

private theorem hasDerivAt_h6PositiveCoshAtom (u : ℝ) (s : ℂ) :
    HasDerivAt (h6PositiveCoshAtom u) (h6PositiveCoshAtomD1 u s) s := by
  unfold h6PositiveCoshAtom h6PositiveCoshAtomD1
  exact (hasDerivAt_h6PositiveCoshAtom_arg u s).ccosh.div_const (Real.cosh u : ℂ)

private theorem hasDerivAt_h6PositiveCoshAtomD1 (u : ℝ) (s : ℂ) :
    HasDerivAt (h6PositiveCoshAtomD1 u) (h6PositiveCoshAtomD2 u s) s := by
  have h := ((hasDerivAt_h6PositiveCoshAtom_arg u s).csinh.mul_const
    (2 * (u : ℂ))).div_const (Real.cosh u : ℂ)
  unfold h6PositiveCoshAtomD1 h6PositiveCoshAtomD2
  simpa only [pow_two, mul_assoc] using h

private theorem hasDerivAt_h6PositiveCoshAtomD2 (u : ℝ) (s : ℂ) :
    HasDerivAt (h6PositiveCoshAtomD2 u) (h6PositiveCoshAtomD3 u s) s := by
  have h := ((hasDerivAt_h6PositiveCoshAtom_arg u s).ccosh.mul_const
    ((2 * (u : ℂ)) ^ 2)).div_const (Real.cosh u : ℂ)
  unfold h6PositiveCoshAtomD2 h6PositiveCoshAtomD3
  simpa only [mul_assoc] using h

/-- The first atom location, `log 2`. -/
def h6PositiveCoshAuditL : ℝ := Real.log 2

/-- A normalized positive two-atom hyperbolic transform. -/
def h6PositiveCoshAudit (s : ℂ) : ℂ :=
  (1 / 8 : ℂ) * h6PositiveCoshAtom h6PositiveCoshAuditL s +
    (7 / 8 : ℂ) * h6PositiveCoshAtom (10 * h6PositiveCoshAuditL) s

private def h6PositiveCoshAuditD1 (s : ℂ) : ℂ :=
  (1 / 8 : ℂ) * h6PositiveCoshAtomD1 h6PositiveCoshAuditL s +
    (7 / 8 : ℂ) * h6PositiveCoshAtomD1 (10 * h6PositiveCoshAuditL) s

private def h6PositiveCoshAuditD2 (s : ℂ) : ℂ :=
  (1 / 8 : ℂ) * h6PositiveCoshAtomD2 h6PositiveCoshAuditL s +
    (7 / 8 : ℂ) * h6PositiveCoshAtomD2 (10 * h6PositiveCoshAuditL) s

private def h6PositiveCoshAuditD3 (s : ℂ) : ℂ :=
  (1 / 8 : ℂ) * h6PositiveCoshAtomD3 h6PositiveCoshAuditL s +
    (7 / 8 : ℂ) * h6PositiveCoshAtomD3 (10 * h6PositiveCoshAuditL) s

/-- The first standard Li differential expression of the audit transform. -/
def h6PositiveCoshAuditLiOne : ℂ :=
  logDeriv h6PositiveCoshAudit 1

/-- The second standard Li differential expression of the audit transform. -/
def h6PositiveCoshAuditLiTwo : ℂ :=
  2 * logDeriv h6PositiveCoshAudit 1 +
    deriv (logDeriv h6PositiveCoshAudit) 1

/-- The third standard Li differential expression of the audit transform. -/
def h6PositiveCoshAuditLiThree : ℂ :=
  3 * logDeriv h6PositiveCoshAudit 1 +
    3 * deriv (logDeriv h6PositiveCoshAudit) 1 +
    (1 / 2) * iteratedDeriv 2 (logDeriv h6PositiveCoshAudit) 1

/-- The normalized first tilted moment of the two atoms. -/
def h6PositiveCoshAuditBeta : ℝ :=
  (1 / 8) * (3 / 5) + (7 / 8) * 10 * (1048575 / 1048577)

/-- The normalized second moment of the two atoms. -/
def h6PositiveCoshAuditGamma : ℝ :=
  (1 / 8) + (7 / 8) * 100

/-- The normalized third tilted moment of the two atoms. -/
def h6PositiveCoshAuditDelta : ℝ :=
  (1 / 8) * (3 / 5) + (7 / 8) * 1000 * (1048575 / 1048577)

private theorem hasDerivAt_h6PositiveCoshAudit (s : ℂ) :
    HasDerivAt h6PositiveCoshAudit (h6PositiveCoshAuditD1 s) s := by
  unfold h6PositiveCoshAudit h6PositiveCoshAuditD1
  convert
    ((hasDerivAt_h6PositiveCoshAtom h6PositiveCoshAuditL s).const_mul (1 / 8 : ℂ)).add
      ((hasDerivAt_h6PositiveCoshAtom (10 * h6PositiveCoshAuditL) s).const_mul
        (7 / 8 : ℂ)) using 1 <;> ext <;> simp

private theorem hasDerivAt_h6PositiveCoshAuditD1 (s : ℂ) :
    HasDerivAt h6PositiveCoshAuditD1 (h6PositiveCoshAuditD2 s) s := by
  unfold h6PositiveCoshAuditD1 h6PositiveCoshAuditD2
  convert
    ((hasDerivAt_h6PositiveCoshAtomD1 h6PositiveCoshAuditL s).const_mul
      (1 / 8 : ℂ)).add
      ((hasDerivAt_h6PositiveCoshAtomD1 (10 * h6PositiveCoshAuditL) s).const_mul
        (7 / 8 : ℂ)) using 1 <;> ext <;> simp

private theorem hasDerivAt_h6PositiveCoshAuditD2 (s : ℂ) :
    HasDerivAt h6PositiveCoshAuditD2 (h6PositiveCoshAuditD3 s) s := by
  unfold h6PositiveCoshAuditD2 h6PositiveCoshAuditD3
  convert
    ((hasDerivAt_h6PositiveCoshAtomD2 h6PositiveCoshAuditL s).const_mul
      (1 / 8 : ℂ)).add
      ((hasDerivAt_h6PositiveCoshAtomD2 (10 * h6PositiveCoshAuditL) s).const_mul
        (7 / 8 : ℂ)) using 1 <;> ext <;> simp

theorem h6PositiveCoshAudit_entire : Differentiable ℂ h6PositiveCoshAudit :=
  fun s ↦ (hasDerivAt_h6PositiveCoshAudit s).differentiableAt

theorem h6PositiveCoshAudit_reflection (s : ℂ) :
    h6PositiveCoshAudit (1 - s) = h6PositiveCoshAudit s := by
  have harg (u : ℝ) :
      (2 * (1 - s) - 1) * (u : ℂ) = -((2 * s - 1) * (u : ℂ)) := by ring
  simp only [h6PositiveCoshAudit, h6PositiveCoshAtom, harg, Complex.cosh_neg]

theorem h6PositiveCoshAudit_coefficients_pos :
    0 < (1 / 8 : ℝ) / Real.cosh h6PositiveCoshAuditL ∧
      0 < (7 / 8 : ℝ) / Real.cosh (10 * h6PositiveCoshAuditL) := by
  constructor <;> positivity

private theorem h6PositiveCoshAtom_one (u : ℝ) : h6PositiveCoshAtom u 1 = 1 := by
  simp only [h6PositiveCoshAtom]
  rw [show (2 * (1 : ℂ) - 1) * (u : ℂ) = (u : ℂ) by ring, ← Complex.ofReal_cosh]
  exact div_self (ofReal_ne_zero.mpr (Real.cosh_pos u).ne')

theorem h6PositiveCoshAudit_one : h6PositiveCoshAudit 1 = 1 := by
  rw [h6PositiveCoshAudit, h6PositiveCoshAtom_one, h6PositiveCoshAtom_one]
  norm_num

private theorem h6PositiveCoshAuditL_pos : 0 < h6PositiveCoshAuditL := by
  exact Real.log_pos (by norm_num)

private theorem sinh_h6PositiveCoshAuditL :
    Real.sinh h6PositiveCoshAuditL = 3 / 4 := by
  rw [h6PositiveCoshAuditL, Real.sinh_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem cosh_h6PositiveCoshAuditL :
    Real.cosh h6PositiveCoshAuditL = 5 / 4 := by
  rw [h6PositiveCoshAuditL, Real.cosh_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem ten_mul_h6PositiveCoshAuditL :
    10 * h6PositiveCoshAuditL = Real.log ((2 : ℝ) ^ 10) := by
  rw [h6PositiveCoshAuditL, Real.log_pow]
  norm_num

private theorem sinh_ten_mul_h6PositiveCoshAuditL :
    Real.sinh (10 * h6PositiveCoshAuditL) = 1048575 / 2048 := by
  rw [ten_mul_h6PositiveCoshAuditL, Real.sinh_log (by positivity)]
  norm_num

private theorem cosh_ten_mul_h6PositiveCoshAuditL :
    Real.cosh (10 * h6PositiveCoshAuditL) = 1048577 / 2048 := by
  rw [ten_mul_h6PositiveCoshAuditL, Real.cosh_log (by positivity)]
  norm_num

private theorem h6PositiveCoshAuditD1_one :
    h6PositiveCoshAuditD1 1 =
      (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) := by
  simp only [h6PositiveCoshAuditD1, h6PositiveCoshAtomD1]
  rw [show (2 * (1 : ℂ) - 1) * (h6PositiveCoshAuditL : ℂ) =
      (h6PositiveCoshAuditL : ℂ) by ring,
    show (2 * (1 : ℂ) - 1) * ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) =
      ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) by ring,
    ← Complex.ofReal_sinh, ← Complex.ofReal_sinh,
    sinh_h6PositiveCoshAuditL, sinh_ten_mul_h6PositiveCoshAuditL,
    cosh_h6PositiveCoshAuditL, cosh_ten_mul_h6PositiveCoshAuditL]
  push_cast
  norm_num [h6PositiveCoshAuditBeta]
  ring_nf

private theorem h6PositiveCoshAuditD2_one :
    h6PositiveCoshAuditD2 1 =
      (4 * h6PositiveCoshAuditGamma * h6PositiveCoshAuditL ^ 2 : ℝ) := by
  simp only [h6PositiveCoshAuditD2, h6PositiveCoshAtomD2]
  rw [show (2 * (1 : ℂ) - 1) * (h6PositiveCoshAuditL : ℂ) =
      (h6PositiveCoshAuditL : ℂ) by ring,
    show (2 * (1 : ℂ) - 1) * ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) =
      ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) by ring,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
  rw [cosh_h6PositiveCoshAuditL, cosh_ten_mul_h6PositiveCoshAuditL]
  push_cast
  norm_num [h6PositiveCoshAuditGamma]
  ring_nf

private theorem h6PositiveCoshAuditD3_one :
    h6PositiveCoshAuditD3 1 =
      (8 * h6PositiveCoshAuditDelta * h6PositiveCoshAuditL ^ 3 : ℝ) := by
  simp only [h6PositiveCoshAuditD3, h6PositiveCoshAtomD3]
  rw [show (2 * (1 : ℂ) - 1) * (h6PositiveCoshAuditL : ℂ) =
      (h6PositiveCoshAuditL : ℂ) by ring,
    show (2 * (1 : ℂ) - 1) * ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) =
      ((10 * h6PositiveCoshAuditL : ℝ) : ℂ) by ring,
    ← Complex.ofReal_sinh, ← Complex.ofReal_sinh,
    sinh_h6PositiveCoshAuditL, sinh_ten_mul_h6PositiveCoshAuditL,
    cosh_h6PositiveCoshAuditL, cosh_ten_mul_h6PositiveCoshAuditL]
  push_cast
  norm_num [h6PositiveCoshAuditDelta]
  ring_nf

private theorem deriv_h6PositiveCoshAudit (s : ℂ) :
    deriv h6PositiveCoshAudit s = h6PositiveCoshAuditD1 s :=
  (hasDerivAt_h6PositiveCoshAudit s).deriv

private theorem logDeriv_h6PositiveCoshAudit (s : ℂ) :
    logDeriv h6PositiveCoshAudit s =
      h6PositiveCoshAuditD1 s / h6PositiveCoshAudit s := by
  rw [logDeriv_apply, deriv_h6PositiveCoshAudit]

private def h6PositiveCoshAuditLogD1 : ℂ → ℂ :=
  (h6PositiveCoshAuditD2 * h6PositiveCoshAudit -
      h6PositiveCoshAuditD1 * h6PositiveCoshAuditD1) /
    h6PositiveCoshAudit ^ 2

private theorem hasDerivAt_logDeriv_h6PositiveCoshAudit (s : ℂ)
    (hs : h6PositiveCoshAudit s ≠ 0) :
    HasDerivAt (logDeriv h6PositiveCoshAudit)
      (h6PositiveCoshAuditLogD1 s) s := by
  have hquot := (hasDerivAt_h6PositiveCoshAuditD1 s).div
    (hasDerivAt_h6PositiveCoshAudit s) hs
  rw [show logDeriv h6PositiveCoshAudit =
      h6PositiveCoshAuditD1 / h6PositiveCoshAudit by
    funext z
    exact logDeriv_h6PositiveCoshAudit z]
  exact hquot

private theorem hasDerivAt_h6PositiveCoshAuditLogD1_one :
    HasDerivAt h6PositiveCoshAuditLogD1
      ((8 * h6PositiveCoshAuditDelta * h6PositiveCoshAuditL ^ 3 : ℝ) -
        3 * (4 * h6PositiveCoshAuditGamma * h6PositiveCoshAuditL ^ 2) *
          (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) +
        2 * (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) ^ 3) 1 := by
  have hnum := ((hasDerivAt_h6PositiveCoshAuditD2 1).mul
      (hasDerivAt_h6PositiveCoshAudit 1)).sub
    ((hasDerivAt_h6PositiveCoshAuditD1 1).mul
      (hasDerivAt_h6PositiveCoshAuditD1 1))
  have hden := (hasDerivAt_h6PositiveCoshAudit 1).pow 2
  have hden_ne : h6PositiveCoshAudit 1 ^ 2 ≠ 0 := by rw [h6PositiveCoshAudit_one]; norm_num
  have hquot := hnum.div hden hden_ne
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at hquot
  rw [h6PositiveCoshAudit_one, h6PositiveCoshAuditD1_one,
    h6PositiveCoshAuditD2_one, h6PositiveCoshAuditD3_one] at hquot
  unfold h6PositiveCoshAuditLogD1
  apply hquot.congr_deriv
  push_cast
  ring

private theorem hasDerivAt_deriv_logDeriv_h6PositiveCoshAudit_one :
    HasDerivAt (deriv (logDeriv h6PositiveCoshAudit))
      ((8 * h6PositiveCoshAuditDelta * h6PositiveCoshAuditL ^ 3 : ℝ) -
        3 * (4 * h6PositiveCoshAuditGamma * h6PositiveCoshAuditL ^ 2) *
          (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) +
        2 * (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) ^ 3) 1 := by
  have hne : ∀ᶠ s in nhds (1 : ℂ), h6PositiveCoshAudit s ≠ 0 :=
    (hasDerivAt_h6PositiveCoshAudit 1).continuousAt.eventually_ne (by
      rw [h6PositiveCoshAudit_one]
      norm_num)
  have heq : deriv (logDeriv h6PositiveCoshAudit) =ᶠ[nhds (1 : ℂ)]
      h6PositiveCoshAuditLogD1 := hne.mono fun s hs ↦
    (hasDerivAt_logDeriv_h6PositiveCoshAudit s hs).deriv
  exact hasDerivAt_h6PositiveCoshAuditLogD1_one.congr_of_eventuallyEq heq

private theorem logDeriv_h6PositiveCoshAudit_one :
    logDeriv h6PositiveCoshAudit 1 =
      (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) := by
  rw [logDeriv_h6PositiveCoshAudit, h6PositiveCoshAudit_one,
    h6PositiveCoshAuditD1_one]
  simp

private theorem deriv_logDeriv_h6PositiveCoshAudit_one :
    deriv (logDeriv h6PositiveCoshAudit) 1 =
      ((4 * h6PositiveCoshAuditGamma * h6PositiveCoshAuditL ^ 2 : ℝ) -
        (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) ^ 2) := by
  rw [(hasDerivAt_logDeriv_h6PositiveCoshAudit 1 (by
    rw [h6PositiveCoshAudit_one]
    norm_num)).deriv]
  simp only [h6PositiveCoshAuditLogD1, Pi.div_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.pow_apply, h6PositiveCoshAudit_one,
    h6PositiveCoshAuditD1_one, h6PositiveCoshAuditD2_one]
  push_cast
  ring

private theorem iteratedDeriv_two_logDeriv_h6PositiveCoshAudit_one :
    iteratedDeriv 2 (logDeriv h6PositiveCoshAudit) 1 =
      ((8 * h6PositiveCoshAuditDelta * h6PositiveCoshAuditL ^ 3 : ℝ) -
        3 * (4 * h6PositiveCoshAuditGamma * h6PositiveCoshAuditL ^ 2) *
          (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) +
        2 * (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL) ^ 3) := by
  simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using
    hasDerivAt_deriv_logDeriv_h6PositiveCoshAudit_one.deriv

theorem h6PositiveCoshAuditLiOne_eq :
    h6PositiveCoshAuditLiOne =
      (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) := by
  exact logDeriv_h6PositiveCoshAudit_one

theorem h6PositiveCoshAuditLiTwo_eq :
    h6PositiveCoshAuditLiTwo =
      (4 * (h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2) : ℝ) := by
  rw [h6PositiveCoshAuditLiTwo, logDeriv_h6PositiveCoshAudit_one,
    deriv_logDeriv_h6PositiveCoshAudit_one]
  push_cast
  ring

theorem h6PositiveCoshAuditLiThree_eq :
    h6PositiveCoshAuditLiThree =
      ((6 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2 +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 3 : ℝ) : ℂ) := by
  rw [h6PositiveCoshAuditLiThree, logDeriv_h6PositiveCoshAudit_one,
    deriv_logDeriv_h6PositiveCoshAudit_one,
    iteratedDeriv_two_logDeriv_h6PositiveCoshAudit_one]
  push_cast
  ring

private theorem h6PositiveCoshAuditGamma_sub_Beta_sq_pos :
    0 < h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2 := by
  norm_num [h6PositiveCoshAuditGamma, h6PositiveCoshAuditBeta]

theorem h6PositiveCoshAuditLiOne_re_pos :
    0 < h6PositiveCoshAuditLiOne.re := by
  rw [h6PositiveCoshAuditLiOne_eq]
  change 0 < 2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL
  have hbeta : 0 < h6PositiveCoshAuditBeta := by
    norm_num [h6PositiveCoshAuditBeta]
  exact mul_pos (mul_pos (by norm_num) hbeta) h6PositiveCoshAuditL_pos

theorem h6PositiveCoshAuditLiTwo_re_pos :
    0 < h6PositiveCoshAuditLiTwo.re := by
  rw [h6PositiveCoshAuditLiTwo_eq]
  change 0 < 4 * (h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
    (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
      h6PositiveCoshAuditL ^ 2)
  have hbeta : 0 < h6PositiveCoshAuditBeta := by
    norm_num [h6PositiveCoshAuditBeta]
  have hvar := h6PositiveCoshAuditGamma_sub_Beta_sq_pos
  have hfirst : 0 < h6PositiveCoshAuditBeta * h6PositiveCoshAuditL :=
    mul_pos hbeta h6PositiveCoshAuditL_pos
  have hsecond : 0 < (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
      h6PositiveCoshAuditL ^ 2 :=
    mul_pos hvar (sq_pos_of_pos h6PositiveCoshAuditL_pos)
  exact mul_pos (by norm_num) (add_pos hfirst hsecond)

private theorem h6PositiveCoshAuditLiThree_real_neg :
    (6 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
      12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
        h6PositiveCoshAuditL ^ 2 +
      (4 * h6PositiveCoshAuditDelta -
        12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
        8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 3) < 0 := by
  let a : ℝ := 6931471803 / 10000000000
  have hLa : a < h6PositiveCoshAuditL := by
    have h := Real.log_two_gt_d9
    norm_num [a, h6PositiveCoshAuditL] at h ⊢
    exact h
  have hLpos : 0 < h6PositiveCoshAuditL := h6PositiveCoshAuditL_pos
  have hbracketA :
      6 * h6PositiveCoshAuditBeta +
        12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) * a +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) * a ^ 2 < 0 := by
    norm_num [a, h6PositiveCoshAuditBeta, h6PositiveCoshAuditGamma,
      h6PositiveCoshAuditDelta]
  have hlead :
      4 * h6PositiveCoshAuditDelta -
        12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
        8 * h6PositiveCoshAuditBeta ^ 3 < 0 := by
    norm_num [h6PositiveCoshAuditBeta, h6PositiveCoshAuditGamma,
      h6PositiveCoshAuditDelta]
  have hslope :
      12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) *
            (h6PositiveCoshAuditL + a) < 0 := by
    have hLaSum : 2 * a < h6PositiveCoshAuditL + a := by linarith
    norm_num [a, h6PositiveCoshAuditBeta, h6PositiveCoshAuditGamma,
      h6PositiveCoshAuditDelta] at hLaSum ⊢
    nlinarith
  have hprod :
      (h6PositiveCoshAuditL - a) *
        (12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) +
          (4 * h6PositiveCoshAuditDelta -
            12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
            8 * h6PositiveCoshAuditBeta ^ 3) *
              (h6PositiveCoshAuditL + a)) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hLa) hslope
  have hbracket :
      6 * h6PositiveCoshAuditBeta +
        12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 2 < 0 := by
    nlinarith
  have := mul_neg_of_pos_of_neg hLpos hbracket
  nlinarith

theorem h6PositiveCoshAuditLiThree_re_neg :
    h6PositiveCoshAuditLiThree.re < 0 := by
  rw [h6PositiveCoshAuditLiThree_eq]
  exact h6PositiveCoshAuditLiThree_real_neg

theorem h6PositiveCoshAuditLiOne_im_eq_zero :
    h6PositiveCoshAuditLiOne.im = 0 := by
  calc
    h6PositiveCoshAuditLiOne.im =
        ((2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) : ℂ).im :=
      congrArg Complex.im h6PositiveCoshAuditLiOne_eq
    _ = 0 := Complex.ofReal_im _

theorem h6PositiveCoshAuditLiTwo_im_eq_zero :
    h6PositiveCoshAuditLiTwo.im = 0 := by
  calc
    h6PositiveCoshAuditLiTwo.im =
        ((4 * (h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
          (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
            h6PositiveCoshAuditL ^ 2) : ℝ) : ℂ).im :=
      congrArg Complex.im h6PositiveCoshAuditLiTwo_eq
    _ = 0 := Complex.ofReal_im _

theorem h6PositiveCoshAuditLiThree_im_eq_zero :
    h6PositiveCoshAuditLiThree.im = 0 := by
  calc
    h6PositiveCoshAuditLiThree.im =
        (((6 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
          12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
            h6PositiveCoshAuditL ^ 2 +
          (4 * h6PositiveCoshAuditDelta -
            12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
            8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 3 : ℝ) : ℂ)).im :=
      congrArg Complex.im h6PositiveCoshAuditLiThree_eq
    _ = 0 := Complex.ofReal_im _

/-- A positive, entire, reflection-symmetric `cosh` transform need not have nonnegative Li3. -/
theorem h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi :
    Differentiable ℂ h6PositiveCoshAudit ∧
    (∀ s : ℂ, h6PositiveCoshAudit (1 - s) = h6PositiveCoshAudit s) ∧
    (0 < (1 / 8 : ℝ) / Real.cosh h6PositiveCoshAuditL ∧
      0 < (7 / 8 : ℝ) / Real.cosh (10 * h6PositiveCoshAuditL)) ∧
    h6PositiveCoshAudit 1 = 1 ∧
    h6PositiveCoshAuditLiOne =
      (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) ∧
    h6PositiveCoshAuditLiTwo =
      (4 * (h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2) : ℝ) ∧
    h6PositiveCoshAuditLiThree =
      ((6 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2 +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 3 : ℝ) : ℂ) ∧
    0 < h6PositiveCoshAuditLiOne.re ∧ h6PositiveCoshAuditLiOne.im = 0 ∧
    0 < h6PositiveCoshAuditLiTwo.re ∧ h6PositiveCoshAuditLiTwo.im = 0 ∧
    h6PositiveCoshAuditLiThree.re < 0 ∧ h6PositiveCoshAuditLiThree.im = 0 := by
  exact ⟨h6PositiveCoshAudit_entire, h6PositiveCoshAudit_reflection,
    h6PositiveCoshAudit_coefficients_pos, h6PositiveCoshAudit_one,
    h6PositiveCoshAuditLiOne_eq, h6PositiveCoshAuditLiTwo_eq,
    h6PositiveCoshAuditLiThree_eq,
    h6PositiveCoshAuditLiOne_re_pos, h6PositiveCoshAuditLiOne_im_eq_zero,
    h6PositiveCoshAuditLiTwo_re_pos, h6PositiveCoshAuditLiTwo_im_eq_zero,
    h6PositiveCoshAuditLiThree_re_neg, h6PositiveCoshAuditLiThree_im_eq_zero⟩

end

end LeanLab.Riemann
