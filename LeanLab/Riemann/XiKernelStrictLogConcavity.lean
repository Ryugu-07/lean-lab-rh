import LeanLab.Riemann.DeBruijnNewmanThreshold
import Mathlib.Analysis.SumIntegralExpDecay

set_option linter.style.header false

/-!
# Strict log-concavity of the Riemann Xi kernel

This file works with the source-normalized theta kernel already used by the de Bruijn-Newman
development.  The first layer identifies its first two derivatives as explicit Gaussian series.
-/

open Filter Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- A common power-Gaussian summand used to organize the Xi-kernel derivatives. -/
def xiKernelPowerTerm (k : Nat) (r : Real) (n : Nat) (u : Real) : Real :=
  ((n : Real) + 1) ^ k * Real.exp (r * u) *
    Real.exp (-Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u))

theorem summable_xiKernelPowerTerm (k : Nat) (r u : Real) :
    Summable fun n : Nat => xiKernelPowerTerm k r n u := by
  have h := (HurwitzKernelBounds.summable_f_nat k 1 (Real.exp_pos (4 * u))).mul_left
    (Real.exp (r * u))
  apply h.congr
  intro n
  simp only [xiKernelPowerTerm, HurwitzKernelBounds.f_nat]
  ring_nf

theorem hasDerivAt_xiKernelPowerTerm (k : Nat) (r : Real) (n : Nat) (u : Real) :
    HasDerivAt (xiKernelPowerTerm k r n)
      (r * xiKernelPowerTerm k r n u -
        4 * Real.pi * xiKernelPowerTerm (k + 2) (r + 4) n u) u := by
  let m : Real := (n : Real) + 1
  have hleft : HasDerivAt
      (fun x : Real => m ^ k * Real.exp (r * x))
      (m ^ k * (Real.exp (r * u) * (r * 1))) u := by
    simpa only [id_eq] using
      (((hasDerivAt_id u).const_mul r).exp.const_mul (m ^ k))
  have hinner : HasDerivAt
      (fun x : Real => -Real.pi * m ^ 2 * Real.exp (4 * x))
      ((-Real.pi * m ^ 2) * (Real.exp (4 * u) * (4 * 1))) u := by
    simpa only [id_eq] using
      (((hasDerivAt_id u).const_mul 4).exp.const_mul (-Real.pi * m ^ 2))
  have hraw := hleft.mul hinner.exp
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · rfl
  · simp only [xiKernelPowerTerm]
    rw [show Real.exp ((r + 4) * u) = Real.exp (r * u) * Real.exp (4 * u) by
      rw [← Real.exp_add]
      congr 1
      ring, pow_add]
    dsimp only [m]
    ring_nf

/-- The explicit first derivative of one Xi-kernel summand. -/
def deBruijnNewmanPhiDerivTerm (n : Nat) (u : Real) : Real :=
  -8 * Real.pi ^ 3 * xiKernelPowerTerm 6 13 n u +
    30 * Real.pi ^ 2 * xiKernelPowerTerm 4 9 n u -
    15 * Real.pi * xiKernelPowerTerm 2 5 n u

/-- The explicit second derivative of one Xi-kernel summand. -/
def deBruijnNewmanPhiSecondDerivTerm (n : Nat) (u : Real) : Real :=
  32 * Real.pi ^ 4 * xiKernelPowerTerm 8 17 n u -
    224 * Real.pi ^ 3 * xiKernelPowerTerm 6 13 n u +
    330 * Real.pi ^ 2 * xiKernelPowerTerm 4 9 n u -
    75 * Real.pi * xiKernelPowerTerm 2 5 n u

/-- The explicit first derivative series of the Xi kernel. -/
def deBruijnNewmanPhiDeriv (u : Real) : Real :=
  ∑' n : Nat, deBruijnNewmanPhiDerivTerm n u

/-- The explicit second derivative series of the Xi kernel. -/
def deBruijnNewmanPhiSecondDeriv (u : Real) : Real :=
  ∑' n : Nat, deBruijnNewmanPhiSecondDerivTerm n u

theorem deBruijnNewmanPhiTerm_eq_powerTerms (n : Nat) (u : Real) :
    deBruijnNewmanPhiTerm n u =
      2 * Real.pi ^ 2 * xiKernelPowerTerm 4 9 n u -
        3 * Real.pi * xiKernelPowerTerm 2 5 n u := by
  rw [deBruijnNewmanPhiTerm_eq]
  simp only [xiKernelPowerTerm]
  ring_nf

theorem summable_deBruijnNewmanPhiDerivTerm (u : Real) :
    Summable fun n : Nat => deBruijnNewmanPhiDerivTerm n u := by
  simpa only [deBruijnNewmanPhiDerivTerm] using
    ((((summable_xiKernelPowerTerm 6 13 u).mul_left (-8 * Real.pi ^ 3)).add
    ((summable_xiKernelPowerTerm 4 9 u).mul_left (30 * Real.pi ^ 2))).sub
    ((summable_xiKernelPowerTerm 2 5 u).mul_left (15 * Real.pi)))

theorem summable_deBruijnNewmanPhiSecondDerivTerm (u : Real) :
    Summable fun n : Nat => deBruijnNewmanPhiSecondDerivTerm n u := by
  simpa only [deBruijnNewmanPhiSecondDerivTerm] using
    (((((summable_xiKernelPowerTerm 8 17 u).mul_left (32 * Real.pi ^ 4)).sub
    ((summable_xiKernelPowerTerm 6 13 u).mul_left (224 * Real.pi ^ 3))).add
    ((summable_xiKernelPowerTerm 4 9 u).mul_left (330 * Real.pi ^ 2))).sub
    ((summable_xiKernelPowerTerm 2 5 u).mul_left (75 * Real.pi)))

theorem hasDerivAt_deBruijnNewmanPhiTerm (n : Nat) (u : Real) :
    HasDerivAt (deBruijnNewmanPhiTerm n) (deBruijnNewmanPhiDerivTerm n u) u := by
  have h := ((hasDerivAt_xiKernelPowerTerm 4 9 n u).const_mul (2 * Real.pi ^ 2)).sub
    ((hasDerivAt_xiKernelPowerTerm 2 5 n u).const_mul (3 * Real.pi))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · exact deBruijnNewmanPhiTerm_eq_powerTerms n x
  · simp only [deBruijnNewmanPhiDerivTerm]
    ring_nf

theorem hasDerivAt_deBruijnNewmanPhiDerivTerm (n : Nat) (u : Real) :
    HasDerivAt (deBruijnNewmanPhiDerivTerm n)
      (deBruijnNewmanPhiSecondDerivTerm n u) u := by
  have h :=
    (((hasDerivAt_xiKernelPowerTerm 6 13 n u).const_mul (-8 * Real.pi ^ 3)).add
      ((hasDerivAt_xiKernelPowerTerm 4 9 n u).const_mul (30 * Real.pi ^ 2))).sub
      ((hasDerivAt_xiKernelPowerTerm 2 5 n u).const_mul (15 * Real.pi))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num
  simp only [deBruijnNewmanPhiSecondDerivTerm]
  ring_nf

/-- The logarithmic derivative of one positive Xi-kernel summand on the nonnegative axis. -/
def xiKernelTermLogSlope (n : Nat) (u : Real) : Real :=
  let y := Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)
  5 + 8 * y / (2 * y - 3) - 4 * y

/-- The second logarithmic derivative of one Xi-kernel summand. -/
def xiKernelTermLogCurvature (n : Nat) (u : Real) : Real :=
  -16 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) -
    96 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) /
      (2 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) - 3) ^ 2

private theorem xiKernel_term_core_pos (n : Nat) {u : Real} (hu : 0 <= u) :
    0 < 2 * Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) - 3 := by
  have hm : 1 <= (n : Real) + 1 := by
    have hn : 0 <= (n : Real) := by positivity
    linarith
  have hm2 : 1 <= ((n : Real) + 1) ^ 2 := by nlinarith
  have hexp : 1 <= Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpi := Real.pi_gt_three
  have hmul : Real.pi <=
      Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) := by
    calc
      Real.pi <= Real.pi * ((n : Real) + 1) ^ 2 := by
        exact le_mul_of_one_le_right Real.pi_pos.le hm2
      _ <= Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) := by
        exact le_mul_of_one_le_right (by positivity) hexp
  nlinarith

theorem deBruijnNewmanPhiDerivTerm_eq_term_mul_logSlope
    (n : Nat) {u : Real} (hu : 0 <= u) :
    deBruijnNewmanPhiDerivTerm n u =
      deBruijnNewmanPhiTerm n u * xiKernelTermLogSlope n u := by
  let m : Real := (n : Real) + 1
  let y : Real := Real.pi * m ^ 2 * Real.exp (4 * u)
  have hcore : 2 * y - 3 ≠ 0 := by
    dsimp only [y, m]
    exact ne_of_gt (by nlinarith [xiKernel_term_core_pos n hu])
  have he9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he13 : Real.exp (13 * u) = Real.exp (5 * u) * Real.exp (4 * u) ^ 2 := by
    rw [show 13 * u = 5 * u + 4 * u + 4 * u by ring, Real.exp_add, Real.exp_add,
      pow_two]
    ring
  let c : Real := Real.pi * m ^ 2 * Real.exp (5 * u) * Real.exp (-y)
  have hterm : deBruijnNewmanPhiTerm n u = c * (2 * y - 3) := by
    rw [deBruijnNewmanPhiTerm_eq]
    rw [he9]
    dsimp only [c, y, m]
    ring_nf
  have hderiv : deBruijnNewmanPhiDerivTerm n u =
      c * (-8 * y ^ 2 + 30 * y - 15) := by
    simp only [deBruijnNewmanPhiDerivTerm, xiKernelPowerTerm]
    rw [he9, he13]
    dsimp only [c, y, m]
    ring_nf
  have hslope : xiKernelTermLogSlope n u =
      5 + 8 * y / (2 * y - 3) - 4 * y := by
    rfl
  have hpoly : -8 * y ^ 2 + 30 * y - 15 =
      (2 * y - 3) * (5 + 8 * y / (2 * y - 3) - 4 * y) := by
    have hcancel : (2 * y - 3) * (8 * y / (2 * y - 3)) = 8 * y :=
      mul_div_cancel₀ (8 * y) hcore
    calc
      -8 * y ^ 2 + 30 * y - 15 =
          (2 * y - 3) * 5 + 8 * y - (2 * y - 3) * (4 * y) := by ring
      _ = (2 * y - 3) * 5 +
          (2 * y - 3) * (8 * y / (2 * y - 3)) - (2 * y - 3) * (4 * y) := by
        rw [hcancel]
      _ = (2 * y - 3) * (5 + 8 * y / (2 * y - 3) - 4 * y) := by ring
  rw [hderiv, hterm, hslope, hpoly]
  ring

theorem deBruijnNewmanPhiSecondDerivTerm_eq_term_mul_logData
    (n : Nat) {u : Real} (hu : 0 <= u) :
    deBruijnNewmanPhiSecondDerivTerm n u =
      deBruijnNewmanPhiTerm n u *
        (xiKernelTermLogSlope n u ^ 2 + xiKernelTermLogCurvature n u) := by
  let m : Real := (n : Real) + 1
  let y : Real := Real.pi * m ^ 2 * Real.exp (4 * u)
  have hcore : 2 * y - 3 ≠ 0 := by
    dsimp only [y, m]
    exact ne_of_gt (by nlinarith [xiKernel_term_core_pos n hu])
  have he9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he13 : Real.exp (13 * u) =
      Real.exp (5 * u) * Real.exp (4 * u) ^ 2 := by
    rw [show 13 * u = 5 * u + 4 * u + 4 * u by ring, Real.exp_add, Real.exp_add,
      pow_two]
    ring
  have he17 : Real.exp (17 * u) =
      Real.exp (5 * u) * Real.exp (4 * u) ^ 3 := by
    rw [show 17 * u = 5 * u + 4 * u + 4 * u + 4 * u by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, pow_succ, pow_two]
    ring
  let c : Real := Real.pi * m ^ 2 * Real.exp (5 * u) * Real.exp (-y)
  have hterm : deBruijnNewmanPhiTerm n u = c * (2 * y - 3) := by
    rw [deBruijnNewmanPhiTerm_eq]
    rw [he9]
    dsimp only [c, y, m]
    ring_nf
  have hsecond : deBruijnNewmanPhiSecondDerivTerm n u =
      c * (32 * y ^ 3 - 224 * y ^ 2 + 330 * y - 75) := by
    simp only [deBruijnNewmanPhiSecondDerivTerm, xiKernelPowerTerm]
    rw [he9, he13, he17]
    dsimp only [c, y, m]
    ring_nf
  have hslope : xiKernelTermLogSlope n u =
      5 + 8 * y / (2 * y - 3) - 4 * y := by
    rfl
  have hcurvature : xiKernelTermLogCurvature n u =
      -16 * y - 96 * y / (2 * y - 3) ^ 2 := by
    rfl
  have hpoly : 32 * y ^ 3 - 224 * y ^ 2 + 330 * y - 75 =
      (2 * y - 3) *
        ((5 + 8 * y / (2 * y - 3) - 4 * y) ^ 2 +
          (-16 * y - 96 * y / (2 * y - 3) ^ 2)) := by
    have hcore' : y * 2 - 3 ≠ 0 := by
      simpa only [mul_comm] using hcore
    field_simp [hcore']; ring_nf
  rw [hsecond, hterm, hslope, hcurvature, hpoly]
  ring

theorem xiKernelTermLogCurvature_neg
    (n : Nat) {u : Real} (_hu : 0 <= u) :
    xiKernelTermLogCurvature n u < 0 := by
  have hy : 0 < Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) := by
    positivity
  simp only [xiKernelTermLogCurvature]
  have hfirst : -16 *
      (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) < 0 := by
    nlinarith
  have hsecond : -96 *
      (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) /
        (2 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) - 3) ^ 2 <= 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith
    · exact sq_nonneg _
  rw [show
    -16 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) -
        96 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) /
          (2 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) - 3) ^ 2 =
      -16 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) +
        (-96 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) /
          (2 * (Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) - 3) ^ 2) by
    ring]
  exact add_neg_of_neg_of_nonpos hfirst hsecond

/-- The common Gaussian variable `pi * exp (4u)` used to compare all summands with the first. -/
def xiKernelBaseY (u : Real) : Real :=
  Real.pi * Real.exp (4 * u)

theorem xiKernelBaseY_gt_three {u : Real} (hu : 0 <= u) :
    3 < xiKernelBaseY u := by
  have hexp : 1 <= Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hmul : Real.pi <= Real.pi * Real.exp (4 * u) :=
    le_mul_of_one_le_right Real.pi_pos.le hexp
  dsimp only [xiKernelBaseY]
  linarith [Real.pi_gt_three]

/-- The exact ratio of the `n`th summand to the first summand on the nonnegative axis. -/
def xiKernelRelativeWeight (n : Nat) (u : Real) : Real :=
  let m : Real := (n : Real) + 1
  let y := xiKernelBaseY u
  m ^ 2 * (2 * m ^ 2 * y - 3) / (2 * y - 3) *
    Real.exp (-(m ^ 2 - 1) * y)

theorem deBruijnNewmanPhiTerm_eq_first_mul_relativeWeight
    (n : Nat) {u : Real} (hu : 0 <= u) :
    deBruijnNewmanPhiTerm n u =
      deBruijnNewmanPhiTerm 0 u * xiKernelRelativeWeight n u := by
  let m : Real := (n : Real) + 1
  let y : Real := xiKernelBaseY u
  have hden : 2 * y - 3 ≠ 0 := by
    exact ne_of_gt (by linarith [xiKernelBaseY_gt_three hu])
  have he9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-y) * Real.exp (-(m ^ 2 - 1) * y) =
      Real.exp (-(m ^ 2) * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [deBruijnNewmanPhiTerm_eq, deBruijnNewmanPhiTerm_eq]
  simp only [xiKernelRelativeWeight]
  rw [he9]
  norm_num only [Nat.cast_zero, zero_add, one_pow, mul_one]
  dsimp only [m, y] at hden hexp ⊢
  rw [show -Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) =
      -((n : Real) + 1) ^ 2 * xiKernelBaseY u by
    dsimp only [xiKernelBaseY]
    ring, show -Real.pi * Real.exp (4 * u) = -xiKernelBaseY u by
    dsimp only [xiKernelBaseY]
    ring, ← hexp]
  field_simp [hden]
  dsimp only [xiKernelBaseY]
  ring_nf

theorem xiKernelRelativeWeight_nonneg
    (n : Nat) {u : Real} (hu : 0 <= u) :
    0 <= xiKernelRelativeWeight n u := by
  rw [← mul_nonneg_iff_of_pos_left (deBruijnNewmanPhiTerm_pos 0 hu)]
  rw [← deBruijnNewmanPhiTerm_eq_first_mul_relativeWeight n hu]
  exact (deBruijnNewmanPhiTerm_pos n hu).le

theorem xiKernelRelativeWeight_le
    (n : Nat) {u : Real} (hu : 0 <= u) :
    xiKernelRelativeWeight n u <=
      2 * ((n : Real) + 1) ^ 4 *
        Real.exp (-(((n : Real) + 1) ^ 2 - 1) * xiKernelBaseY u) := by
  let m : Real := (n : Real) + 1
  let y : Real := xiKernelBaseY u
  have hm : 1 <= m := by
    dsimp only [m]
    have hn : 0 <= (n : Real) := by positivity
    linarith
  have hm0 : 0 <= m := zero_le_one.trans hm
  have hm2 : 1 <= m ^ 2 := by nlinarith
  have hy : 3 < y := xiKernelBaseY_gt_three hu
  have hden : 0 < 2 * y - 3 := by linarith
  have hratio : (2 * m ^ 2 * y - 3) / (2 * y - 3) <= 2 * m ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm2) (sub_nonneg.mpr hy.le)]
  simp only [xiKernelRelativeWeight]
  change
    m ^ 2 * (2 * m ^ 2 * y - 3) / (2 * y - 3) *
        Real.exp (-(m ^ 2 - 1) * y) <=
      2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y)
  have hleft : m ^ 2 * (2 * m ^ 2 * y - 3) / (2 * y - 3) <=
      2 * m ^ 4 := by
    rw [mul_div_assoc]
    calc
      m ^ 2 * ((2 * m ^ 2 * y - 3) / (2 * y - 3)) <=
          m ^ 2 * (2 * m ^ 2) := mul_le_mul_of_nonneg_left hratio (sq_nonneg m)
      _ = 2 * m ^ 4 := by ring
  exact mul_le_mul_of_nonneg_right hleft (Real.exp_pos _).le

theorem xiKernelTermLogSlope_sub_first
    (n : Nat) {u : Real} (hu : 0 <= u) :
    xiKernelTermLogSlope n u - xiKernelTermLogSlope 0 u =
      -4 * (((n : Real) + 1) ^ 2 - 1) * xiKernelBaseY u *
        (1 + 6 /
          ((2 * ((n : Real) + 1) ^ 2 * xiKernelBaseY u - 3) *
            (2 * xiKernelBaseY u - 3))) := by
  let m : Real := (n : Real) + 1
  let y : Real := xiKernelBaseY u
  have hm : 1 <= m := by
    dsimp only [m]
    have hn : 0 <= (n : Real) := by positivity
    linarith
  have hm2 : 1 <= m ^ 2 := by nlinarith
  have hy : 3 < y := xiKernelBaseY_gt_three hu
  have hden0 : 2 * y - 3 ≠ 0 := ne_of_gt (by linarith)
  have hdenm : 2 * m ^ 2 * y - 3 ≠ 0 := by
    apply ne_of_gt
    have hym : y <= m ^ 2 * y := by
      exact le_mul_of_one_le_left (by linarith) hm2
    nlinarith
  have halgebra :
      (5 + 8 * (m ^ 2 * y) / (2 * (m ^ 2 * y) - 3) - 4 * (m ^ 2 * y)) -
          (5 + 8 * y / (2 * y - 3) - 4 * y) =
        -4 * (m ^ 2 - 1) * y *
          (1 + 6 / ((2 * m ^ 2 * y - 3) * (2 * y - 3))) := by
    have hden0' : y * 2 - 3 ≠ 0 := by simpa only [mul_comm] using hden0
    have hdenm' : m ^ 2 * y * 2 - 3 ≠ 0 := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hdenm
    field_simp [hden0', hdenm']; ring_nf
  simp only [xiKernelTermLogSlope, Nat.cast_zero, zero_add, one_pow]
  rw [show Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) = m ^ 2 * y by
    dsimp only [m, y, xiKernelBaseY]
    ring, show Real.pi * 1 * Real.exp (4 * u) = y by
    dsimp only [y, xiKernelBaseY]
    ring]
  exact halgebra

theorem xiKernelTermLogSlope_sub_first_sq_le
    (n : Nat) {u : Real} (hu : 0 <= u) :
    (xiKernelTermLogSlope n u - xiKernelTermLogSlope 0 u) ^ 2 <=
      64 * (((n : Real) + 1) ^ 2 - 1) ^ 2 * xiKernelBaseY u ^ 2 := by
  let m : Real := (n : Real) + 1
  let y : Real := xiKernelBaseY u
  let d : Real := (2 * m ^ 2 * y - 3) * (2 * y - 3)
  let b : Real := 1 + 6 / d
  have hm : 1 <= m := by
    dsimp only [m]
    have hn : 0 <= (n : Real) := by positivity
    linarith
  have hm2 : 1 <= m ^ 2 := by nlinarith
  have hy : 3 < y := xiKernelBaseY_gt_three hu
  have hden0 : 3 < 2 * y - 3 := by linarith
  have hdenm : 3 < 2 * m ^ 2 * y - 3 := by
    have hym : y <= m ^ 2 * y :=
      le_mul_of_one_le_left (by linarith) hm2
    nlinarith
  have hd : 6 < d := by
    dsimp only [d]
    have hprod : 0 < (2 * m ^ 2 * y - 3) * (2 * y - 3) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hb0 : 0 <= b := by
    dsimp only [b]
    positivity
  have hb2 : b <= 2 := by
    dsimp only [b]
    have hfrac : 6 / d < 1 := (div_lt_one (by linarith)).mpr hd
    linarith
  have hbsq : b ^ 2 <= 4 := by nlinarith [sq_nonneg (b - 2)]
  rw [xiKernelTermLogSlope_sub_first n hu]
  change (-4 * (m ^ 2 - 1) * y * b) ^ 2 <=
      64 * (m ^ 2 - 1) ^ 2 * y ^ 2
  calc
    (-4 * (m ^ 2 - 1) * y * b) ^ 2 =
        (16 * (m ^ 2 - 1) ^ 2 * y ^ 2) * b ^ 2 := by ring
    _ <= (16 * (m ^ 2 - 1) ^ 2 * y ^ 2) * 4 := by
      exact mul_le_mul_of_nonneg_left hbsq (by positivity)
    _ = 64 * (m ^ 2 - 1) ^ 2 * y ^ 2 := by ring

private theorem nat_succ_le_two_pow (n : Nat) :
    n + 1 <= 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n.succ + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ n.succ := by rw [pow_succ]; ring

theorem xiKernelBaseY_mul_exp_neg_three_lt
    {u : Real} (hu : 0 <= u) :
    xiKernelBaseY u * Real.exp (-3 * xiKernelBaseY u) <
      (63 / 160000 : Real) := by
  let y : Real := xiKernelBaseY u
  have hpiY : Real.pi <= y := by
    dsimp only [y, xiKernelBaseY]
    have hexp : 1 <= Real.exp (4 * u) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    exact le_mul_of_one_le_right Real.pi_pos.le hexp
  have hdelta : 0 <= y - Real.pi := sub_nonneg.mpr hpiY
  have hy_le : y <= Real.pi * Real.exp (y - Real.pi) := by
    calc
      y = Real.pi + (y - Real.pi) := by ring
      _ <= Real.pi + Real.pi * (y - Real.pi) := by
        have hpi1 : 1 <= Real.pi := by linarith [Real.pi_gt_three]
        nlinarith [mul_le_mul_of_nonneg_right hpi1 hdelta]
      _ = Real.pi * (1 + (y - Real.pi)) := by ring
      _ <= Real.pi * Real.exp (y - Real.pi) := by
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        simpa only [add_comm] using Real.add_one_le_exp (y - Real.pi)
  have hyExp : y * Real.exp (-y) <=
      Real.pi * Real.exp (-Real.pi) := by
    calc
      y * Real.exp (-y) <=
          (Real.pi * Real.exp (y - Real.pi)) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right hy_le (Real.exp_pos _).le
      _ = Real.pi * Real.exp (-Real.pi) := by
        rw [show (Real.pi * Real.exp (y - Real.pi)) * Real.exp (-y) =
          Real.pi * (Real.exp (y - Real.pi) * Real.exp (-y)) by ring,
          ← Real.exp_add]
        congr 1
        ring_nf
  have hExpY : Real.exp (-y) < (1 / 20 : Real) := by
    have harg : -y <= -Real.pi := neg_le_neg hpiY
    exact (Real.exp_le_exp.mpr harg).trans_lt Real.rexp_neg_pi_lt_one_twentieth
  have hPiExp : Real.pi * Real.exp (-Real.pi) < (63 / 400 : Real) := by
    have hpi : Real.pi < (63 / 20 : Real) := by
      have hpi' := Real.pi_lt_d2
      norm_num at hpi' ⊢
      exact hpi'
    calc
      Real.pi * Real.exp (-Real.pi) <
          (63 / 20 : Real) * Real.exp (-Real.pi) := by
        exact mul_lt_mul_of_pos_right hpi (Real.exp_pos _)
      _ < (63 / 20 : Real) * (1 / 20 : Real) := by
        exact mul_lt_mul_of_pos_left Real.rexp_neg_pi_lt_one_twentieth (by norm_num)
      _ = (63 / 400 : Real) := by norm_num
  have hExpYSq : Real.exp (-y) ^ 2 < (1 / 20 : Real) ^ 2 := by
    exact pow_lt_pow_left₀ hExpY (Real.exp_pos _).le (by norm_num)
  change y * Real.exp (-3 * y) < (63 / 160000 : Real)
  calc
    y * Real.exp (-3 * y) =
        (y * Real.exp (-y)) * Real.exp (-y) ^ 2 := by
      rw [show -3 * y = -y + (-y + -y) by ring, Real.exp_add,
        Real.exp_add, pow_two]
      ring
    _ <= (Real.pi * Real.exp (-Real.pi)) * Real.exp (-y) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hyExp (sq_nonneg _)
    _ < (63 / 400 : Real) * Real.exp (-y) ^ 2 := by
      exact mul_lt_mul_of_pos_right hPiExp (sq_pos_of_pos (Real.exp_pos _))
    _ < (63 / 400 : Real) * (1 / 20 : Real) ^ 2 := by
      exact mul_lt_mul_of_pos_left hExpYSq (by norm_num)
    _ = (63 / 160000 : Real) := by norm_num

theorem xiKernelGaussianTailTerm_le_geometric
    (n : Nat) (hn : 1 <= n) {u : Real} (hu : 0 <= u) :
    xiKernelBaseY u * ((n : Real) + 1) ^ 8 *
        Real.exp (-(((n : Real) + 1) ^ 2 - 1) * xiKernelBaseY u) <=
      (63 / 625 : Real) * (4 / 125 : Real) ^ (n - 1) := by
  let m : Real := (n : Real) + 1
  let y : Real := xiKernelBaseY u
  have hy : 0 < y := by
    dsimp only [y, xiKernelBaseY]
    positivity
  have hmn : m <= (2 : Real) ^ n := by
    dsimp only [m]
    exact_mod_cast nat_succ_le_two_pow n
  have hm0 : 0 <= m := by
    dsimp only [m]
    positivity
  have hmPow : m ^ 8 <= (256 : Real) ^ n := by
    calc
      m ^ 8 <= ((2 : Real) ^ n) ^ 8 := pow_le_pow_left₀ hm0 hmn 8
      _ = (256 : Real) ^ n := by
        rw [show (256 : Real) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hdegree : 3 * (n : Real) <= m ^ 2 - 1 := by
    dsimp only [m]
    nlinarith [sq_nonneg ((n : Real) - 1)]
  have hExpDegree :
      Real.exp (-(m ^ 2 - 1) * y) <= Real.exp (-(3 * (n : Real)) * y) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hdegree) hy.le
  have hExpY : Real.exp (-y) <= (1 / 20 : Real) := by
    have hpiY : Real.pi <= y := by
      dsimp only [y]
      exact (show Real.pi <= xiKernelBaseY u by
        have hexp : 1 <= Real.exp (4 * u) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        exact le_mul_of_one_le_right Real.pi_pos.le hexp)
    exact ((Real.exp_le_exp.mpr (neg_le_neg hpiY)).trans
      Real.rexp_neg_pi_lt_one_twentieth.le)
  let k : Nat := n - 1
  have hnk : n = k + 1 := by
    dsimp only [k]
    exact (Nat.sub_add_cancel hn).symm
  have hExpRemain : Real.exp (-3 * (k : Real) * y) <=
      (1 / 8000 : Real) ^ k := by
    have hpow := pow_le_pow_left₀ (Real.exp_pos (-y)).le hExpY (3 * k)
    calc
      Real.exp (-3 * (k : Real) * y) = Real.exp (-y) ^ (3 * k) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ <= (1 / 20 : Real) ^ (3 * k) := hpow
      _ = (1 / 8000 : Real) ^ k := by
        rw [show (1 / 8000 : Real) = (1 / 20 : Real) ^ 3 by norm_num,
          ← pow_mul]
  change y * m ^ 8 * Real.exp (-(m ^ 2 - 1) * y) <=
      (63 / 625 : Real) * (4 / 125 : Real) ^ k
  calc
    y * m ^ 8 * Real.exp (-(m ^ 2 - 1) * y) <=
        y * (256 : Real) ^ n * Real.exp (-(3 * (n : Real)) * y) := by
      gcongr
    _ = (y * Real.exp (-3 * y)) * (256 : Real) ^ n *
        Real.exp (-3 * (k : Real) * y) := by
      rw [hnk]
      push_cast
      rw [show -(3 * ((k : Real) + 1)) * y = -3 * y + (-3 * (k : Real) * y) by ring,
        Real.exp_add]
      ring
    _ <= (63 / 160000 : Real) * (256 : Real) ^ n *
        (1 / 8000 : Real) ^ k := by
      gcongr
      exact (xiKernelBaseY_mul_exp_neg_three_lt hu).le
    _ = (63 / 625 : Real) * (4 / 125 : Real) ^ k := by
      rw [hnk, pow_succ]
      calc
        (63 / 160000 : Real) * ((256 : Real) ^ k * 256) *
            (1 / 8000 : Real) ^ k =
          ((63 / 160000 : Real) * 256) *
            ((256 : Real) ^ k * (1 / 8000 : Real) ^ k) := by ring
        _ = (63 / 625 : Real) *
            ((256 : Real) * (1 / 8000 : Real)) ^ k := by
          rw [mul_pow]
          norm_num
        _ = (63 / 625 : Real) * (4 / 125 : Real) ^ k := by norm_num

theorem xiKernelGaussianTail_tsum_lt
    {u : Real} (hu : 0 <= u) :
    (∑' k : Nat,
      xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
        Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)) <
      (1 / 8 : Real) := by
  let tail : Nat -> Real := fun k =>
    xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
      Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)
  let major : Nat -> Real := fun k =>
    (63 / 625 : Real) * (4 / 125 : Real) ^ k
  have hmajor : Summable major := by
    exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) <= 4 / 125)
      (by norm_num : (4 / 125 : Real) < 1)).mul_left (63 / 625 : Real)
  have hpoint : forall k : Nat, tail k <= major k := by
    intro k
    simpa only [tail, major, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
      Nat.add_sub_cancel] using
      xiKernelGaussianTailTerm_le_geometric (k + 1) (by omega) hu
  have htail : Summable tail := by
    apply hmajor.of_nonneg_of_le
    · intro k
      dsimp only [tail]
      have hy : 0 <= xiKernelBaseY u := by linarith [xiKernelBaseY_gt_three hu]
      exact mul_nonneg (mul_nonneg hy (by positivity)) (Real.exp_pos _).le
    · exact hpoint
  calc
    (∑' k : Nat,
        xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
          Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)) =
        ∑' k : Nat, tail k := by rfl
    _ <= ∑' k : Nat, major k := htail.tsum_le_tsum hpoint hmajor
    _ = (63 / 605 : Real) := by
      simp only [major, tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num : (0 : Real) <= 4 / 125)
          (by norm_num : (4 / 125 : Real) < 1)]
      norm_num
    _ < (1 / 8 : Real) := by norm_num

theorem summable_xiKernelGaussianTail {u : Real} (hu : 0 <= u) :
    Summable fun k : Nat =>
      xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
        Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u) := by
  let major : Nat -> Real := fun k =>
    (63 / 625 : Real) * (4 / 125 : Real) ^ k
  have hmajor : Summable major := by
    exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) <= 4 / 125)
      (by norm_num : (4 / 125 : Real) < 1)).mul_left (63 / 625 : Real)
  apply hmajor.of_nonneg_of_le
  · intro k
    have hy : 0 <= xiKernelBaseY u := by linarith [xiKernelBaseY_gt_three hu]
    exact mul_nonneg (mul_nonneg hy (by positivity)) (Real.exp_pos _).le
  · intro k
    simpa only [major, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
      Nat.add_sub_cancel] using
      xiKernelGaussianTailTerm_le_geometric (k + 1) (by omega) hu

theorem xiKernelRelativeSlopeTailTerm_le
    (k : Nat) {u : Real} (hu : 0 <= u) :
    xiKernelRelativeWeight (k + 1) u *
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2 <=
      128 * xiKernelBaseY u *
        (xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
          Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)) := by
  let m : Real := (k : Real) + 2
  let y : Real := xiKernelBaseY u
  have hm : 1 <= m := by
    dsimp only [m]
    have hk : 0 <= (k : Real) := by positivity
    linarith
  have hm2 : 1 <= m ^ 2 := by nlinarith
  have hdiff : (m ^ 2 - 1) ^ 2 <= m ^ 4 := by
    calc
      (m ^ 2 - 1) ^ 2 <= (m ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr hm2) (by linarith) 2
      _ = m ^ 4 := by ring
  have hw := xiKernelRelativeWeight_le (k + 1) hu
  have hs := xiKernelTermLogSlope_sub_first_sq_le (k + 1) hu
  have hw' : xiKernelRelativeWeight (k + 1) u <=
      2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y) := by
    simpa only [m, y, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hw
  have hs' :
      (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2 <=
        64 * (m ^ 2 - 1) ^ 2 * y ^ 2 := by
    simpa only [m, y, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hs
  calc
    xiKernelRelativeWeight (k + 1) u *
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2 <=
      (2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y)) *
        (64 * (m ^ 2 - 1) ^ 2 * y ^ 2) :=
      mul_le_mul hw' hs' (sq_nonneg _) (by positivity)
    _ = (128 * y ^ 2 * Real.exp (-(m ^ 2 - 1) * y)) *
        (m ^ 4 * (m ^ 2 - 1) ^ 2) := by ring
    _ <= (128 * y ^ 2 * Real.exp (-(m ^ 2 - 1) * y)) *
        (m ^ 4 * m ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdiff (by positivity)) (by positivity)
    _ = 128 * xiKernelBaseY u *
        (xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
          Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)) := by
      dsimp only [m, y]
      ring

theorem summable_xiKernelRelativeSlopeTail {u : Real} (hu : 0 <= u) :
    Summable fun k : Nat => xiKernelRelativeWeight (k + 1) u *
      (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2 := by
  have hmajor := (summable_xiKernelGaussianTail hu).mul_left
    (128 * xiKernelBaseY u)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg (xiKernelRelativeWeight_nonneg (k + 1) hu) (sq_nonneg _)
  · intro k
    exact xiKernelRelativeSlopeTailTerm_le k hu

theorem xiKernelRelativeSlopeTail_tsum_lt_neg_curvature
    {u : Real} (hu : 0 <= u) :
    (∑' k : Nat, xiKernelRelativeWeight (k + 1) u *
      (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2) <
      -xiKernelTermLogCurvature 0 u := by
  let gaussian : Nat -> Real := fun k =>
    xiKernelBaseY u * ((k : Real) + 2) ^ 8 *
      Real.exp (-(((k : Real) + 2) ^ 2 - 1) * xiKernelBaseY u)
  let varianceTail : Nat -> Real := fun k =>
    xiKernelRelativeWeight (k + 1) u *
      (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2
  let major : Nat -> Real := fun k => 128 * xiKernelBaseY u * gaussian k
  have hy : 0 < xiKernelBaseY u := by linarith [xiKernelBaseY_gt_three hu]
  have hpoint : forall k : Nat, varianceTail k <= major k := by
    intro k
    let m : Real := (k : Real) + 2
    let y : Real := xiKernelBaseY u
    have hm : 1 <= m := by
      dsimp only [m]
      have hk : 0 <= (k : Real) := by positivity
      linarith
    have hm2 : 1 <= m ^ 2 := by nlinarith
    have hdiff : (m ^ 2 - 1) ^ 2 <= m ^ 4 := by
      calc
        (m ^ 2 - 1) ^ 2 <= (m ^ 2) ^ 2 :=
          pow_le_pow_left₀ (sub_nonneg.mpr hm2) (by linarith) 2
        _ = m ^ 4 := by ring
    have hw := xiKernelRelativeWeight_le (k + 1) hu
    have hs := xiKernelTermLogSlope_sub_first_sq_le (k + 1) hu
    have hw' : xiKernelRelativeWeight (k + 1) u <=
        2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y) := by
      simpa only [m, y, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using hw
    have hs' :
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2 <=
          64 * (m ^ 2 - 1) ^ 2 * y ^ 2 := by
      simpa only [m, y, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using hs
    have hfirst : varianceTail k <=
        (2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y)) *
          (64 * (m ^ 2 - 1) ^ 2 * y ^ 2) := by
      dsimp only [varianceTail]
      exact mul_le_mul hw' hs'
        (sq_nonneg (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u))
        (by positivity : 0 <= 2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y))
    calc
      varianceTail k <=
          (2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y)) *
            (64 * (m ^ 2 - 1) ^ 2 * y ^ 2) := hfirst
      _ <= 128 * y *
          (y * m ^ 8 * Real.exp (-(m ^ 2 - 1) * y)) := by
        have hnonneg : 0 <=
            128 * y ^ 2 * Real.exp (-(m ^ 2 - 1) * y) := by positivity
        calc
          (2 * m ^ 4 * Real.exp (-(m ^ 2 - 1) * y)) *
              (64 * (m ^ 2 - 1) ^ 2 * y ^ 2) =
            (128 * y ^ 2 * Real.exp (-(m ^ 2 - 1) * y)) *
              (m ^ 4 * (m ^ 2 - 1) ^ 2) := by ring
          _ <= (128 * y ^ 2 * Real.exp (-(m ^ 2 - 1) * y)) *
              (m ^ 4 * m ^ 4) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hdiff (by positivity)) hnonneg
          _ = 128 * y *
              (y * m ^ 8 * Real.exp (-(m ^ 2 - 1) * y)) := by ring
      _ = major k := by
        dsimp only [major, gaussian, m, y]
  have hmajor : Summable major := by
    exact (summable_xiKernelGaussianTail hu).mul_left (128 * xiKernelBaseY u)
  have hvariance : Summable varianceTail := by
    apply hmajor.of_nonneg_of_le
    · intro k
      dsimp only [varianceTail]
      exact mul_nonneg (xiKernelRelativeWeight_nonneg (k + 1) hu) (sq_nonneg _)
    · exact hpoint
  have hmajorTsum : (∑' k : Nat, major k) < 16 * xiKernelBaseY u := by
    have htail : (∑' k : Nat, gaussian k) < (1 / 8 : Real) := by
      simpa only [gaussian] using xiKernelGaussianTail_tsum_lt hu
    calc
      (∑' k : Nat, major k) =
          128 * xiKernelBaseY u * (∑' k : Nat, gaussian k) := by
        simp only [major, tsum_mul_left]
      _ < 128 * xiKernelBaseY u * (1 / 8 : Real) :=
        mul_lt_mul_of_pos_left htail (by positivity)
      _ = 16 * xiKernelBaseY u := by ring
  have hcurvature : 16 * xiKernelBaseY u < -xiKernelTermLogCurvature 0 u := by
    have hden : 0 < 2 * xiKernelBaseY u - 3 := by
      linarith [xiKernelBaseY_gt_three hu]
    have hfrac : 0 < 96 * xiKernelBaseY u / (2 * xiKernelBaseY u - 3) ^ 2 := by
      positivity
    simp only [xiKernelTermLogCurvature, Nat.cast_zero, zero_add, one_pow, mul_one]
    rw [show Real.pi * Real.exp (4 * u) = xiKernelBaseY u by rfl]
    change 16 * xiKernelBaseY u <
      -(-16 * xiKernelBaseY u -
        96 * xiKernelBaseY u / (2 * xiKernelBaseY u - 3) ^ 2)
    linarith
  calc
    (∑' k : Nat, xiKernelRelativeWeight (k + 1) u *
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2) =
      ∑' k : Nat, varianceTail k := by rfl
    _ <= ∑' k : Nat, major k := hvariance.tsum_le_tsum hpoint hmajor
    _ < 16 * xiKernelBaseY u := hmajorTsum
    _ < -xiKernelTermLogCurvature 0 u := hcurvature

private theorem finite_weighted_logConcavity_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i0 : ι)
    (a b c : ι -> Real) (hi0 : i0 ∈ s)
    (ha0 : 0 < a i0) (ha : ∀ i ∈ s, 0 <= a i)
    (hc : ∀ i ∈ s.erase i0, c i <= 0) :
    (∑ i ∈ s, a i) * (∑ i ∈ s, a i * (b i ^ 2 + c i)) -
        (∑ i ∈ s, a i * b i) ^ 2 <=
      (∑ i ∈ s, a i) *
        ((∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2) + a i0 * c i0) := by
  let A : Real := ∑ i ∈ s, a i
  let B : Real := ∑ i ∈ s, a i * b i
  let S2 : Real := ∑ i ∈ s, a i * b i ^ 2
  let Cc : Real := ∑ i ∈ s, a i * c i
  let D : Real := ∑ i ∈ s, a i * (b i - b i0) ^ 2
  let E : Real := ∑ i ∈ s, a i * (b i - b i0)
  have hA0 : 0 < A := by
    have hsingle : a i0 <= ∑ i ∈ s, a i := by
      exact Finset.single_le_sum (fun i hi => ha i hi) hi0
    exact ha0.trans_le hsingle
  have hE : E = B - b i0 * A := by
    dsimp only [E, B, A]
    calc
      (∑ i ∈ s, a i * (b i - b i0)) =
          ∑ i ∈ s, (a i * b i - a i * b i0) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, a i * b i) - b i0 * (∑ i ∈ s, a i) := by
        rw [Finset.sum_sub_distrib]
        have hconst : (∑ i ∈ s, a i * b i0) = (∑ i ∈ s, a i) * b i0 := by
          rw [Finset.sum_mul]
        rw [hconst]
        ring
  have hD : D = S2 - 2 * b i0 * B + b i0 ^ 2 * A := by
    dsimp only [D, S2, B, A]
    calc
      (∑ i ∈ s, a i * (b i - b i0) ^ 2) =
          ∑ i ∈ s,
            (a i * b i ^ 2 - 2 * b i0 * (a i * b i) + b i0 ^ 2 * a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, a i * b i ^ 2) -
          2 * b i0 * (∑ i ∈ s, a i * b i) +
            b i0 ^ 2 * (∑ i ∈ s, a i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.mul_sum]
  have hvariance : A * S2 - B ^ 2 = A * D - E ^ 2 := by
    rw [hD, hE]
    ring
  have hvariance_le : A * S2 - B ^ 2 <= A * D := by
    rw [hvariance]
    nlinarith [sq_nonneg E]
  have hCc : Cc <= a i0 * c i0 := by
    have herase : (∑ i ∈ s.erase i0, a i * c i) <= 0 := by
      exact Finset.sum_nonpos fun i hi =>
        mul_nonpos_of_nonneg_of_nonpos (ha i (Finset.mem_of_mem_erase hi)) (hc i hi)
    dsimp only [Cc]
    rw [← s.sum_erase_add _ hi0]
    linarith
  have hDtail : D = ∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2 := by
    dsimp only [D]
    rw [← s.sum_erase_add _ hi0]
    simp
  have hsumData : (∑ i ∈ s, a i * (b i ^ 2 + c i)) = S2 + Cc := by
    dsimp only [S2, Cc]
    calc
      (∑ i ∈ s, a i * (b i ^ 2 + c i)) =
          ∑ i ∈ s, (a i * b i ^ 2 + a i * c i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, a i * b i ^ 2) + (∑ i ∈ s, a i * c i) :=
        Finset.sum_add_distrib
  change A * (∑ i ∈ s, a i * (b i ^ 2 + c i)) - B ^ 2 <=
    A * ((∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2) + a i0 * c i0)
  rw [hsumData]
  calc
    A * (S2 + Cc) - B ^ 2 = (A * S2 - B ^ 2) + A * Cc := by ring
    _ <= A * D + A * (a i0 * c i0) := by
      exact add_le_add hvariance_le (mul_le_mul_of_nonneg_left hCc hA0.le)
    _ = A * (D + a i0 * c i0) := by ring
    _ = A * ((∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2) +
        a i0 * c i0) := by rw [hDtail]

private theorem finite_weighted_logConcavity_of_tail
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i0 : ι)
    (a b c : ι -> Real) (hi0 : i0 ∈ s)
    (ha0 : 0 < a i0) (ha : ∀ i ∈ s, 0 <= a i)
    (hc : ∀ i ∈ s.erase i0, c i <= 0)
    (htail : (∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2) < -a i0 * c i0) :
    (∑ i ∈ s, a i) * (∑ i ∈ s, a i * (b i ^ 2 + c i)) -
        (∑ i ∈ s, a i * b i) ^ 2 < 0 := by
  have hbound := finite_weighted_logConcavity_bound s i0 a b c hi0 ha0 ha hc
  have hA0 : 0 < ∑ i ∈ s, a i := by
    have hsingle : a i0 <= ∑ i ∈ s, a i :=
      Finset.single_le_sum (fun i hi => ha i hi) hi0
    exact ha0.trans_le hsingle
  have hbracket :
      (∑ i ∈ s.erase i0, a i * (b i - b i0) ^ 2) + a i0 * c i0 < 0 := by
    linarith
  exact hbound.trans_lt (mul_neg_of_pos_of_neg hA0 hbracket)

theorem xiKernelFinitePartial_uniform_bound
    (N : Nat) {u : Real} (hu : 0 <= u) :
    (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiTerm n u) *
        (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiSecondDerivTerm n u) -
      (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiDerivTerm n u) ^ 2 <=
    deBruijnNewmanPhiTerm 0 u ^ 2 *
      ((∑' k : Nat, xiKernelRelativeWeight (k + 1) u *
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2) +
        xiKernelTermLogCurvature 0 u) := by
  let s : Finset Nat := Finset.range (N + 1)
  let a : Nat -> Real := fun n => deBruijnNewmanPhiTerm n u
  let b : Nat -> Real := fun n => xiKernelTermLogSlope n u
  let c : Nat -> Real := fun n => xiKernelTermLogCurvature n u
  let g : Nat -> Real := fun n => a n * (b n - b 0) ^ 2
  let v : Nat -> Real := fun k => xiKernelRelativeWeight (k + 1) u *
    (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2
  have hzero : 0 ∈ s := by simp [s]
  have ha0 : 0 < a 0 := by
    exact deBruijnNewmanPhiTerm_pos 0 hu
  have ha : ∀ n ∈ s, 0 <= a n := by
    intro n hn
    exact (deBruijnNewmanPhiTerm_pos n hu).le
  have hc : ∀ n ∈ s.erase 0, c n <= 0 := by
    intro n hn
    exact (xiKernelTermLogCurvature_neg n hu).le
  have hErase : (∑ n ∈ s.erase 0, g n) =
      ∑ k ∈ Finset.range N, g (k + 1) := by
    have herase := s.sum_erase_add g hzero
    have hsplit := Finset.sum_range_succ' g N
    dsimp only [s] at herase
    rw [hsplit] at herase
    linarith
  have hFactor : (∑ k ∈ Finset.range N, g (k + 1)) =
      a 0 * ∑ k ∈ Finset.range N, v k := by
    calc
      (∑ k ∈ Finset.range N, g (k + 1)) =
          ∑ k ∈ Finset.range N, a 0 * v k := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp only [g, v, a, b]
        rw [deBruijnNewmanPhiTerm_eq_first_mul_relativeWeight (k + 1) hu]
        ring
      _ = a 0 * ∑ k ∈ Finset.range N, v k := by
        rw [Finset.mul_sum]
  have hvSummable : Summable v := by
    simpa only [v] using summable_xiKernelRelativeSlopeTail hu
  have hvNonneg : ∀ k, 0 <= v k := by
    intro k
    dsimp only [v]
    exact mul_nonneg (xiKernelRelativeWeight_nonneg (k + 1) hu) (sq_nonneg _)
  have hvFinite : (∑ k ∈ Finset.range N, v k) <= ∑' k : Nat, v k :=
    hvSummable.sum_le_tsum (Finset.range N) (fun k hk => hvNonneg k)
  have hvTsum : (∑' k : Nat, v k) < -c 0 := by
    simpa only [v, c] using xiKernelRelativeSlopeTail_tsum_lt_neg_curvature hu
  have htail : (∑ n ∈ s.erase 0, a n * (b n - b 0) ^ 2) < -a 0 * c 0 := by
    rw [show (∑ n ∈ s.erase 0, a n * (b n - b 0) ^ 2) =
        ∑ n ∈ s.erase 0, g n by rfl, hErase, hFactor]
    have hvStrict : (∑ k ∈ Finset.range N, v k) < -c 0 := hvFinite.trans_lt hvTsum
    have hmul := mul_lt_mul_of_pos_left hvStrict ha0
    nlinarith
  have hfinite := finite_weighted_logConcavity_bound s 0 a b c hzero ha0 ha hc
  have hderiv : (∑ n ∈ s, a n * b n) =
      ∑ n ∈ s, deBruijnNewmanPhiDerivTerm n u := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [a, b]
    exact (deBruijnNewmanPhiDerivTerm_eq_term_mul_logSlope n hu).symm
  have hsecond : (∑ n ∈ s, a n * (b n ^ 2 + c n)) =
      ∑ n ∈ s, deBruijnNewmanPhiSecondDerivTerm n u := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [a, b, c]
    exact (deBruijnNewmanPhiSecondDerivTerm_eq_term_mul_logData n hu).symm
  rw [hderiv, hsecond] at hfinite
  have hA : a 0 <= ∑ n ∈ s, a n := by
    exact Finset.single_le_sum (fun n hn => ha n hn) hzero
  have htotalNeg : (∑' k : Nat, v k) + c 0 < 0 := by linarith
  have hfiniteToTotal :
      (∑ k ∈ Finset.range N, v k) + c 0 <= (∑' k : Nat, v k) + c 0 := by
    linarith
  have hboundTotal :
      (∑ n ∈ s, a n) *
          ((∑ n ∈ s.erase 0, a n * (b n - b 0) ^ 2) + a 0 * c 0) <=
        a 0 ^ 2 * ((∑' k : Nat, v k) + c 0) := by
    rw [show (∑ n ∈ s.erase 0, a n * (b n - b 0) ^ 2) =
        ∑ n ∈ s.erase 0, g n by rfl, hErase, hFactor]
    calc
      (∑ n ∈ s, a n) *
          (a 0 * (∑ k ∈ Finset.range N, v k) + a 0 * c 0) =
        ((∑ n ∈ s, a n) * a 0) *
          ((∑ k ∈ Finset.range N, v k) + c 0) := by ring
      _ <= ((∑ n ∈ s, a n) * a 0) * ((∑' k : Nat, v k) + c 0) := by
        exact mul_le_mul_of_nonneg_left hfiniteToTotal
          (mul_nonneg (Finset.sum_nonneg fun n hn => ha n hn) ha0.le)
      _ <= a 0 ^ 2 * ((∑' k : Nat, v k) + c 0) := by
        apply mul_le_mul_of_nonpos_right _ htotalNeg.le
        calc
          a 0 ^ 2 = a 0 * a 0 := by ring
          _ <= (∑ n ∈ s, a n) * a 0 :=
            mul_le_mul_of_nonneg_right hA ha0.le
  have hresult := hfinite.trans hboundTotal
  simpa only [s, a, v, c] using hresult

theorem xiKernelFinitePartial_strictLogConcavity
    (N : Nat) {u : Real} (hu : 0 <= u) :
    (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiTerm n u) *
        (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiSecondDerivTerm n u) -
      (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiDerivTerm n u) ^ 2 < 0 := by
  have hbound := xiKernelFinitePartial_uniform_bound N hu
  have htail := xiKernelRelativeSlopeTail_tsum_lt_neg_curvature hu
  have hterm := deBruijnNewmanPhiTerm_pos 0 hu
  have hnegative : deBruijnNewmanPhiTerm 0 u ^ 2 *
      ((∑' k : Nat, xiKernelRelativeWeight (k + 1) u *
        (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2) +
        xiKernelTermLogCurvature 0 u) < 0 := by
    apply mul_neg_of_pos_of_neg (sq_pos_of_pos hterm)
    linarith
  exact hbound.trans_lt hnegative

/-- A summable local majorant for one power-Gaussian family. -/
def xiKernelPowerBound (k : Nat) (r center : Real) (n : Nat) : Real :=
  Real.exp (r * (center + 1)) *
    HurwitzKernelBounds.f_nat k 1 (Real.exp (4 * (center - 1))) n

theorem summable_xiKernelPowerBound (k : Nat) (r center : Real) :
    Summable fun n : Nat => xiKernelPowerBound k r center n := by
  exact (HurwitzKernelBounds.summable_f_nat k 1
    (Real.exp_pos (4 * (center - 1)))).mul_left (Real.exp (r * (center + 1)))

theorem norm_xiKernelPowerTerm_le_bound
    (k : Nat) {r center v : Real} (hr : 0 <= r)
    (hv : v ∈ Ioo (center - 1) (center + 1)) (n : Nat) :
    ‖xiKernelPowerTerm k r n v‖ <= xiKernelPowerBound k r center n := by
  let m : Real := (n : Real) + 1
  have hm : 0 <= m ^ k := by positivity
  have hrExp : Real.exp (r * v) <= Real.exp (r * (center + 1)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hv.2.le hr
  have hscale : Real.exp (4 * (center - 1)) <= Real.exp (4 * v) := by
    apply Real.exp_le_exp.mpr
    linarith [hv.1]
  have hgauss :
      Real.exp (-Real.pi * m ^ 2 * Real.exp (4 * v)) <=
        Real.exp (-Real.pi * m ^ 2 * Real.exp (4 * (center - 1))) := by
    apply Real.exp_le_exp.mpr
    have hcoef : 0 <= Real.pi * m ^ 2 := by positivity
    simpa only [neg_mul, mul_assoc] using
      neg_le_neg (mul_le_mul_of_nonneg_left hscale hcoef)
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    simp only [xiKernelPowerTerm]
    positivity)]
  calc
    xiKernelPowerTerm k r n v <=
        m ^ k * Real.exp (r * (center + 1)) *
          Real.exp (-Real.pi * m ^ 2 * Real.exp (4 * (center - 1))) := by
      simp only [xiKernelPowerTerm, m]
      gcongr
    _ = xiKernelPowerBound k r center n := by
      simp only [xiKernelPowerBound, HurwitzKernelBounds.f_nat, m]
      ring

/-- Local majorant for the first-derivative summands. -/
def xiKernelPhiDerivBound (center : Real) (n : Nat) : Real :=
  ‖(-8 * Real.pi ^ 3 : Real)‖ * xiKernelPowerBound 6 13 center n +
    ‖(30 * Real.pi ^ 2 : Real)‖ * xiKernelPowerBound 4 9 center n +
    ‖(15 * Real.pi : Real)‖ * xiKernelPowerBound 2 5 center n

/-- Local majorant for the second-derivative summands. -/
def xiKernelPhiSecondDerivBound (center : Real) (n : Nat) : Real :=
  ‖(32 * Real.pi ^ 4 : Real)‖ * xiKernelPowerBound 8 17 center n +
    ‖(224 * Real.pi ^ 3 : Real)‖ * xiKernelPowerBound 6 13 center n +
    ‖(330 * Real.pi ^ 2 : Real)‖ * xiKernelPowerBound 4 9 center n +
    ‖(75 * Real.pi : Real)‖ * xiKernelPowerBound 2 5 center n

theorem summable_xiKernelPhiDerivBound (center : Real) :
    Summable (xiKernelPhiDerivBound center) := by
  exact (((summable_xiKernelPowerBound 6 13 center).mul_left ‖(-8 * Real.pi ^ 3 : Real)‖).add
    ((summable_xiKernelPowerBound 4 9 center).mul_left ‖(30 * Real.pi ^ 2 : Real)‖)).add
    ((summable_xiKernelPowerBound 2 5 center).mul_left ‖(15 * Real.pi : Real)‖)

theorem summable_xiKernelPhiSecondDerivBound (center : Real) :
    Summable (xiKernelPhiSecondDerivBound center) := by
  exact ((((summable_xiKernelPowerBound 8 17 center).mul_left
    ‖(32 * Real.pi ^ 4 : Real)‖).add
    ((summable_xiKernelPowerBound 6 13 center).mul_left
      ‖(224 * Real.pi ^ 3 : Real)‖)).add
    ((summable_xiKernelPowerBound 4 9 center).mul_left
      ‖(330 * Real.pi ^ 2 : Real)‖)).add
    ((summable_xiKernelPowerBound 2 5 center).mul_left ‖(75 * Real.pi : Real)‖)

theorem norm_deBruijnNewmanPhiDerivTerm_le_bound
    (center : Real) {v : Real} (hv : v ∈ Ioo (center - 1) (center + 1)) (n : Nat) :
    ‖deBruijnNewmanPhiDerivTerm n v‖ <= xiKernelPhiDerivBound center n := by
  calc
    ‖deBruijnNewmanPhiDerivTerm n v‖ <=
        (‖-8 * Real.pi ^ 3 * xiKernelPowerTerm 6 13 n v‖ +
          ‖30 * Real.pi ^ 2 * xiKernelPowerTerm 4 9 n v‖) +
          ‖15 * Real.pi * xiKernelPowerTerm 2 5 n v‖ := by
      rw [deBruijnNewmanPhiDerivTerm]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ =
        (‖(-8 * Real.pi ^ 3 : Real)‖ * ‖xiKernelPowerTerm 6 13 n v‖ +
          ‖(30 * Real.pi ^ 2 : Real)‖ * ‖xiKernelPowerTerm 4 9 n v‖) +
          ‖(15 * Real.pi : Real)‖ * ‖xiKernelPowerTerm 2 5 n v‖ := by
      simp only [norm_mul]
    _ <= xiKernelPhiDerivBound center n := by
      dsimp only [xiKernelPhiDerivBound]
      gcongr
      · exact norm_xiKernelPowerTerm_le_bound 6 (by norm_num) hv n
      · exact norm_xiKernelPowerTerm_le_bound 4 (by norm_num) hv n
      · exact norm_xiKernelPowerTerm_le_bound 2 (by norm_num) hv n

theorem norm_deBruijnNewmanPhiSecondDerivTerm_le_bound
    (center : Real) {v : Real} (hv : v ∈ Ioo (center - 1) (center + 1)) (n : Nat) :
    ‖deBruijnNewmanPhiSecondDerivTerm n v‖ <=
      xiKernelPhiSecondDerivBound center n := by
  calc
    ‖deBruijnNewmanPhiSecondDerivTerm n v‖ <=
        ((‖32 * Real.pi ^ 4 * xiKernelPowerTerm 8 17 n v‖ +
          ‖224 * Real.pi ^ 3 * xiKernelPowerTerm 6 13 n v‖) +
          ‖330 * Real.pi ^ 2 * xiKernelPowerTerm 4 9 n v‖) +
          ‖75 * Real.pi * xiKernelPowerTerm 2 5 n v‖ := by
      rw [deBruijnNewmanPhiSecondDerivTerm]
      exact (norm_sub_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ =
        ((‖(32 * Real.pi ^ 4 : Real)‖ * ‖xiKernelPowerTerm 8 17 n v‖ +
          ‖(224 * Real.pi ^ 3 : Real)‖ * ‖xiKernelPowerTerm 6 13 n v‖) +
          ‖(330 * Real.pi ^ 2 : Real)‖ * ‖xiKernelPowerTerm 4 9 n v‖) +
          ‖(75 * Real.pi : Real)‖ * ‖xiKernelPowerTerm 2 5 n v‖ := by
      simp only [norm_mul]
    _ <= xiKernelPhiSecondDerivBound center n := by
      dsimp only [xiKernelPhiSecondDerivBound]
      gcongr
      · exact norm_xiKernelPowerTerm_le_bound 8 (by norm_num) hv n
      · exact norm_xiKernelPowerTerm_le_bound 6 (by norm_num) hv n
      · exact norm_xiKernelPowerTerm_le_bound 4 (by norm_num) hv n
      · exact norm_xiKernelPowerTerm_le_bound 2 (by norm_num) hv n

theorem hasDerivAt_deBruijnNewmanPhi (u : Real) :
    HasDerivAt deBruijnNewmanPhi (deBruijnNewmanPhiDeriv u) u := by
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_xiKernelPhiDerivBound u) isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => hasDerivAt_deBruijnNewmanPhiTerm n v)
    (fun n v hv => norm_deBruijnNewmanPhiDerivTerm_le_bound u hv n)
    (show u ∈ Ioo (u - 1) (u + 1) by constructor <;> linarith)
    (summable_deBruijnNewmanPhiTerm u)
    (show u ∈ Ioo (u - 1) (u + 1) by constructor <;> linarith)
  simpa only [deBruijnNewmanPhi, deBruijnNewmanPhiDeriv] using! h

theorem hasDerivAt_deBruijnNewmanPhiDeriv (u : Real) :
    HasDerivAt deBruijnNewmanPhiDeriv (deBruijnNewmanPhiSecondDeriv u) u := by
  have h := hasDerivAt_tsum_of_isPreconnected
    (summable_xiKernelPhiSecondDerivBound u) isOpen_Ioo isPreconnected_Ioo
    (fun n v _ => hasDerivAt_deBruijnNewmanPhiDerivTerm n v)
    (fun n v hv => norm_deBruijnNewmanPhiSecondDerivTerm_le_bound u hv n)
    (show u ∈ Ioo (u - 1) (u + 1) by constructor <;> linarith)
    (summable_deBruijnNewmanPhiDerivTerm u)
    (show u ∈ Ioo (u - 1) (u + 1) by constructor <;> linarith)
  simpa only [deBruijnNewmanPhiDeriv, deBruijnNewmanPhiSecondDeriv] using! h

/-- The exact source-normalized Xi kernel is strictly log-concave on the nonnegative axis. -/
theorem deBruijnNewmanPhiSecond_mul_phi_sub_deriv_sq_neg
    {u : Real} (hu : 0 <= u) :
    deBruijnNewmanPhiSecondDeriv u * deBruijnNewmanPhi u -
      deBruijnNewmanPhiDeriv u ^ 2 < 0 := by
  let bound : Real := deBruijnNewmanPhiTerm 0 u ^ 2 *
    ((∑' k : Nat, xiKernelRelativeWeight (k + 1) u *
      (xiKernelTermLogSlope (k + 1) u - xiKernelTermLogSlope 0 u) ^ 2) +
      xiKernelTermLogCurvature 0 u)
  have hPhi : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiTerm n u)
      atTop (𝓝 (deBruijnNewmanPhi u)) := by
    have h := (summable_deBruijnNewmanPhiTerm u).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    simpa only [deBruijnNewmanPhi, Function.comp_def] using h
  have hDeriv : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiDerivTerm n u)
      atTop (𝓝 (deBruijnNewmanPhiDeriv u)) := by
    have h := (summable_deBruijnNewmanPhiDerivTerm u).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    simpa only [deBruijnNewmanPhiDeriv, Function.comp_def] using h
  have hSecond : Tendsto
      (fun N : Nat => ∑ n ∈ Finset.range (N + 1),
        deBruijnNewmanPhiSecondDerivTerm n u)
      atTop (𝓝 (deBruijnNewmanPhiSecondDeriv u)) := by
    have h := (summable_deBruijnNewmanPhiSecondDerivTerm u).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    simpa only [deBruijnNewmanPhiSecondDeriv, Function.comp_def] using h
  have hLimit : Tendsto
      (fun N : Nat =>
        (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiTerm n u) *
            (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiSecondDerivTerm n u) -
          (∑ n ∈ Finset.range (N + 1), deBruijnNewmanPhiDerivTerm n u) ^ 2)
      atTop
      (𝓝 (deBruijnNewmanPhi u * deBruijnNewmanPhiSecondDeriv u -
        deBruijnNewmanPhiDeriv u ^ 2)) :=
    (hPhi.mul hSecond).sub (hDeriv.pow 2)
  have hBound : deBruijnNewmanPhi u * deBruijnNewmanPhiSecondDeriv u -
      deBruijnNewmanPhiDeriv u ^ 2 <= bound := by
    apply le_of_tendsto' hLimit
    intro N
    exact xiKernelFinitePartial_uniform_bound N hu
  have hBoundNeg : bound < 0 := by
    have htail := xiKernelRelativeSlopeTail_tsum_lt_neg_curvature hu
    have hterm := deBruijnNewmanPhiTerm_pos 0 hu
    dsimp only [bound]
    apply mul_neg_of_pos_of_neg (sq_pos_of_pos hterm)
    linarith
  nlinarith

end

end LeanLab.Riemann
