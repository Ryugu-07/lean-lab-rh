import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# The Conrey--Li RKHS shift producer

This file reconstructs the upper-half-plane stage of Conrey--Li's Theorem 2. It keeps the
second Hardy-RKHS analytic-continuation stage outside the endpoint.
-/

namespace LeanLab

namespace Riemann

open Complex
open ComplexConjugate
open scoped UpperHalfPlane

noncomputable section

/-- Translation by `i` preserves the open upper half-plane. -/
def conreyLiUpperShift (w : ℍ) : ℍ :=
  ⟨(w : ℂ) + I, by simpa using add_pos w.im_pos (by norm_num : (0 : ℝ) < 1)⟩

@[simp]
theorem coe_conreyLiUpperShift (w : ℍ) :
    (conreyLiUpperShift w : ℂ) = (w : ℂ) + I :=
  rfl

@[simp]
theorem conreyLiUpperShift_im (w : ℍ) :
    (conreyLiUpperShift w).im = w.im + 1 := by
  simp [conreyLiUpperShift]

/-- The source-normalized kernel in Conrey--Li Theorem 2. -/
def conreyLiKernel (W : ℂ → ℂ) (w z : ℂ) : ℂ :=
  W z * conj (W w) / (2 * (Real.pi : ℂ) * I * (conj w - z))

/-- The shifted quotient whose real part is forced by the RKHS positivity premise. -/
def conreyLiUpperShiftRatio (W : ℂ → ℂ) (w : ℍ) : ℂ :=
  W w / W (conreyLiUpperShift w)

/-- The Cayley transform used in the second stage of Conrey--Li Theorem 2. -/
def conreyLiCayley (W : ℂ → ℂ) (w : ℍ) : ℂ :=
  (W w - W (conreyLiUpperShift w)) /
    (W w + W (conreyLiUpperShift w))

/-- The first shifted-kernel sum in the proof of Conrey--Li Theorem 2. -/
def conreyLiFirstShiftKernelSum {ι : Type*} (W : ℂ → ℂ)
    (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) : ℂ :=
  ∑ a ∈ s, ∑ b ∈ s,
    c a * conj (c b) *
      conreyLiKernel W (w a) (conreyLiUpperShift (w b))

/-- The symmetrized shifted-kernel quadratic form from Conrey--Li Theorem 2. -/
def conreyLiShiftedKernelQuadratic {ι : Type*} (W : ℂ → ℂ)
    (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) : ℂ :=
  ∑ a ∈ s, ∑ b ∈ s,
    c a * conj (c b) *
      (conreyLiKernel W (w a) (conreyLiUpperShift (w b)) +
        conreyLiKernel W (conreyLiUpperShift (w a)) (w b))

theorem conj_conreyLiKernel (W : ℂ → ℂ) (w z : ℂ) :
    conj (conreyLiKernel W w z) = conreyLiKernel W z w := by
  simp only [conreyLiKernel, map_div₀, map_mul, map_ofNat, conj_ofReal,
    map_sub, Complex.conj_I, starRingEnd_self_apply]
  congr 1
  · ring
  · have hsub : w - conj z = -(conj z - w) := by ring
    rw [hsub]
    ring

theorem conreyLiShiftedKernelQuadratic_eq_add_conj
    {ι : Type*} (W : ℂ → ℂ) (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) :
    conreyLiShiftedKernelQuadratic W s w c =
      conreyLiFirstShiftKernelSum W s w c +
        conj (conreyLiFirstShiftKernelSum W s w c) := by
  simp only [conreyLiShiftedKernelQuadratic, conreyLiFirstShiftKernelSum,
    mul_add, Finset.sum_add_distrib, map_sum, map_mul,
    starRingEnd_self_apply]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [conj_conreyLiKernel]
  ring

theorem conreyLiShiftedKernelQuadratic_re_eq_two_mul
    {ι : Type*} (W : ℂ → ℂ) (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) :
    (conreyLiShiftedKernelQuadratic W s w c).re =
      2 * (conreyLiFirstShiftKernelSum W s w c).re := by
  rw [conreyLiShiftedKernelQuadratic_eq_add_conj]
  simp only [add_re, conj_re]
  ring

theorem conreyLiShiftedKernelQuadratic_im_eq_zero
    {ι : Type*} (W : ℂ → ℂ) (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) :
    (conreyLiShiftedKernelQuadratic W s w c).im = 0 := by
  rw [conreyLiShiftedKernelQuadratic_eq_add_conj]
  simp

theorem conreyLi_shiftedKernel_denominator (w : ℍ) :
    2 * (Real.pi : ℂ) * I *
        (conj (w : ℂ) - (conreyLiUpperShift w : ℂ)) =
      ((2 * Real.pi * (2 * w.im + 1) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [conreyLiUpperShift, mul_re]
    ring
  · simp [conreyLiUpperShift, mul_im]

theorem conreyLi_shiftedDenominator_pos (w : ℍ) :
    0 < 2 * Real.pi * (2 * w.im + 1) := by
  positivity

theorem conreyLi_shiftedKernel_re_eq
    (W : ℂ → ℂ) (w : ℍ) (hWshift : W (conreyLiUpperShift w) ≠ 0) :
    (conreyLiKernel W w (conreyLiUpperShift w)).re =
      (Complex.normSq (W (conreyLiUpperShift w)) /
          (2 * Real.pi * (2 * w.im + 1))) *
        (conreyLiUpperShiftRatio W w).re := by
  rw [conreyLiKernel, conreyLi_shiftedKernel_denominator]
  simp only [conreyLiUpperShiftRatio, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  have hden : 2 * Real.pi * (2 * w.im + 1) ≠ 0 :=
    (conreyLi_shiftedDenominator_pos w).ne'
  have hnorm : Complex.normSq (W (conreyLiUpperShift w)) ≠ 0 :=
    (Complex.normSq_pos.mpr hWshift).ne'
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [Complex.normSq_apply]
  rw [Complex.normSq_apply] at hnorm
  have hnormpow :
      (W (conreyLiUpperShift w)).re ^ 2 +
          (W (conreyLiUpperShift w)).im ^ 2 ≠ 0 := by
    simpa [pow_two] using hnorm
  field_simp [hden, hnormpow]
  ring

theorem conreyLi_ratio_re_nonneg_of_kernel_re_nonneg
    (W : ℂ → ℂ) (w : ℍ) (hWshift : W (conreyLiUpperShift w) ≠ 0)
    (hkernel : 0 ≤ (conreyLiKernel W w (conreyLiUpperShift w)).re) :
    0 ≤ (conreyLiUpperShiftRatio W w).re := by
  rw [conreyLi_shiftedKernel_re_eq W w hWshift] at hkernel
  have hfactor :
      0 < Complex.normSq (W (conreyLiUpperShift w)) /
        (2 * Real.pi * (2 * w.im + 1)) := by
    exact div_pos (Complex.normSq_pos.mpr hWshift)
      (conreyLi_shiftedDenominator_pos w)
  exact nonneg_of_mul_nonneg_right hkernel hfactor

theorem conreyLi_cayley_denominator_ne_zero {r : ℂ} (hr : 0 ≤ r.re) :
    r + 1 ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  simp at hre
  linarith

theorem conreyLi_norm_sub_one_le_norm_add_one {r : ℂ} (hr : 0 ≤ r.re) :
    ‖r - 1‖ ≤ ‖r + 1‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [sq, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im]
  nlinarith

theorem conreyLi_norm_cayley_le_one {r : ℂ} (hr : 0 ≤ r.re) :
    ‖(r - 1) / (r + 1)‖ ≤ 1 := by
  rw [norm_div]
  rw [div_le_one (norm_pos_iff.mpr (conreyLi_cayley_denominator_ne_zero hr))]
  exact conreyLi_norm_sub_one_le_norm_add_one hr

theorem conreyLiCayley_eq_ratioCayley
    (W : ℂ → ℂ) (w : ℍ) (hWshift : W (conreyLiUpperShift w) ≠ 0) :
    conreyLiCayley W w =
      (conreyLiUpperShiftRatio W w - 1) /
        (conreyLiUpperShiftRatio W w + 1) := by
  simp only [conreyLiCayley, conreyLiUpperShiftRatio]
  field_simp

theorem norm_conreyLiCayley_le_one
    (W : ℂ → ℂ) (w : ℍ) (hWshift : W (conreyLiUpperShift w) ≠ 0)
    (hratio : 0 ≤ (conreyLiUpperShiftRatio W w).re) :
    ‖conreyLiCayley W w‖ ≤ 1 := by
  rw [conreyLiCayley_eq_ratioCayley W w hWshift]
  exact conreyLi_norm_cayley_le_one hratio

section RKHS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H ℍ ℂ]

/-- A finite linear combination of scalar RKHS kernel vectors. -/
def conreyLiKernelCombination {ι : Type*} (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H ℍ ℂ] (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) : H :=
  ∑ a ∈ s, c a • RKHS.kerFun H (w a) 1

theorem inner_conreyLiKernelCombination_shift_eq_conj
    {ι : Type*} (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) :
    inner ℂ (conreyLiKernelCombination H s w c)
        (T (conreyLiKernelCombination H s w c)) =
      conj (conreyLiFirstShiftKernelSum W s w c) := by
  have hT :
      T (conreyLiKernelCombination H s w c) =
        ∑ a ∈ s, c a • RKHS.kerFun H (conreyLiUpperShift (w a)) 1 := by
    simp [conreyLiKernelCombination, hshift]
  rw [hT]
  simp_rw [conreyLiKernelCombination, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, RKHS.inner_kerFun,
    RKHS.kerFun_apply, hkernel]
  simp [conreyLiFirstShiftKernelSum, mul_comm, mul_left_comm]

theorem conreyLiShiftedKernelQuadratic_re_nonneg_of_rkhs_shift
    {ι : Type*} (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (hpositive : ∀ f : H, 0 ≤ (inner ℂ f (T f)).re)
    (s : Finset ι) (w : ι → ℍ) (c : ι → ℂ) :
    0 ≤ (conreyLiShiftedKernelQuadratic W s w c).re := by
  rw [conreyLiShiftedKernelQuadratic_re_eq_two_mul]
  have h := hpositive (conreyLiKernelCombination H s w c)
  rw [inner_conreyLiKernelCombination_shift_eq_conj
    W T hkernel hshift s w c] at h
  simp only [conj_re] at h
  positivity

theorem conreyLiKernel_re_nonneg_of_rkhs_shift
    (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (hpositive : ∀ f : H, 0 ≤ (inner ℂ f (T f)).re)
    (w : ℍ) :
    0 ≤ (conreyLiKernel W w (conreyLiUpperShift w)).re := by
  have h := hpositive (RKHS.kerFun H w 1)
  rw [hshift w, RKHS.inner_kerFun, RKHS.kerFun_apply,
    hkernel w (conreyLiUpperShift w)] at h
  simpa using h

theorem conreyLiUpperShiftRatio_re_nonneg_of_rkhs_shift
    (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (hpositive : ∀ f : H, 0 ≤ (inner ℂ f (T f)).re)
    (hW : ∀ w : ℍ, W w ≠ 0)
    (w : ℍ) :
    0 ≤ (conreyLiUpperShiftRatio W w).re := by
  apply conreyLi_ratio_re_nonneg_of_kernel_re_nonneg W w
    (hW (conreyLiUpperShift w))
  exact conreyLiKernel_re_nonneg_of_rkhs_shift W T hkernel hshift hpositive w

theorem norm_conreyLiCayley_le_one_of_rkhs_shift
    (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (hpositive : ∀ f : H, 0 ≤ (inner ℂ f (T f)).re)
    (hW : ∀ w : ℍ, W w ≠ 0)
    (w : ℍ) :
    ‖conreyLiCayley W w‖ ≤ 1 := by
  apply norm_conreyLiCayley_le_one W w (hW (conreyLiUpperShift w))
  exact conreyLiUpperShiftRatio_re_nonneg_of_rkhs_shift
    W T hkernel hshift hpositive hW w

/-- The compiled upper-half-plane output of the Conrey--Li RKHS shift argument. -/
structure ConreyLiRKHSShiftCertificate (W : ℂ → ℂ) : Prop where
  shiftedKernel_nonneg :
    ∀ (n : ℕ) (w : Fin n → ℍ) (c : Fin n → ℂ),
      0 ≤ (conreyLiShiftedKernelQuadratic W Finset.univ w c).re
  ratio_nonneg :
    ∀ w : ℍ, 0 ≤ (conreyLiUpperShiftRatio W w).re
  cayley_le_one :
    ∀ w : ℍ, ‖conreyLiCayley W w‖ ≤ 1

theorem conreyLiRKHSShift_endpoint
    (W : ℂ → ℂ) (T : H →ₗ[ℂ] H)
    (hkernel : ∀ w z : ℍ,
      RKHS.kernel H z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun H w 1) = RKHS.kerFun H (conreyLiUpperShift w) 1)
    (hpositive : ∀ f : H, 0 ≤ (inner ℂ f (T f)).re)
    (hW : ∀ w : ℍ, W w ≠ 0) :
    ConreyLiRKHSShiftCertificate W where
  shiftedKernel_nonneg _n w c :=
    conreyLiShiftedKernelQuadratic_re_nonneg_of_rkhs_shift
      W T hkernel hshift hpositive Finset.univ w c
  ratio_nonneg w :=
    conreyLiUpperShiftRatio_re_nonneg_of_rkhs_shift
      W T hkernel hshift hpositive hW w
  cayley_le_one w :=
    norm_conreyLiCayley_le_one_of_rkhs_shift
      W T hkernel hshift hpositive hW w

end RKHS

end

end Riemann

end LeanLab
