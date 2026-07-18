import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelXio
import LeanLab.Riemann.WeilExplicitIntegrand
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.Connected

set_option linter.style.header false

/-!
# Analytic continuation of the Titchmarsh Riemann--Siegel identity

This module completes the constant matching on the initial half-plane and proves analyticity of
the fixed diagonal contour integral. The identity theorem on `C \\ Z` then extends Polymath's
`(xio)` identity to every noninteger complex parameter.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

def deBruijnNewmanRiemannSiegelIsNoninteger (s : ℂ) : Prop :=
  ∀ n : ℤ, s ≠ (n : ℂ)

theorem deBruijnNewmanTitchmarshPhiDirection_cpow (s : ℂ) :
    deBruijnNewmanTitchmarshPhiDirection ^ s =
      Complex.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) * s) := by
  let z : ℂ := ((Real.pi / 4 : ℝ) : ℂ) * Complex.I
  have hzLower : -(Real.pi : ℝ) < z.im := by
    dsimp only [z]
    simp
    nlinarith [Real.pi_pos]
  have hzUpper : z.im ≤ Real.pi := by
    dsimp only [z]
    simp
    nlinarith [Real.pi_pos]
  have hlog : Complex.log (Complex.exp z) = z :=
    Complex.log_exp hzLower hzUpper
  rw [deBruijnNewmanTitchmarshPhiDirection,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), hlog]

theorem deBruijnNewmanTitchmarshMellinRayDirection_cpow (s : ℂ) :
    deBruijnNewmanTitchmarshMellinRayDirection ^ s =
      Complex.exp (-((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) * s)) := by
  let z : ℂ := -(((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
  have hzLower : -(Real.pi : ℝ) < z.im := by
    dsimp only [z]
    simp
    nlinarith [Real.pi_pos]
  have hzUpper : z.im ≤ Real.pi := by
    dsimp only [z]
    simp
    nlinarith [Real.pi_pos]
  have hlog : Complex.log (Complex.exp z) = z :=
    Complex.log_exp hzLower hzUpper
  rw [deBruijnNewmanTitchmarshMellinRayDirection,
    deBruijnNewmanTitchmarshPhiDirection]
  change (starRingEnd ℂ
      (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) ^ s = _
  rw [← Complex.exp_conj]
  simp only [map_mul, conj_ofReal, conj_I, mul_neg]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), hlog]
  congr 1
  dsimp only [z]
  ring

theorem deBruijnNewmanTitchmarsh_phase_cpow (s : ℂ) :
    (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
        deBruijnNewmanTitchmarshPhiDirection ^ s =
      (2 * Complex.cos ((Real.pi : ℂ) * s / 2)) *
        deBruijnNewmanTitchmarshMellinRayDirection ^ s := by
  let z : ℂ := (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) * s
  rw [show deBruijnNewmanTitchmarshPhiDirection ^ s = Complex.exp z by
    dsimp only [z]
    exact deBruijnNewmanTitchmarshPhiDirection_cpow s]
  rw [show deBruijnNewmanTitchmarshMellinRayDirection ^ s = Complex.exp (-z) by
    dsimp only [z]
    exact deBruijnNewmanTitchmarshMellinRayDirection_cpow s]
  have hpi : ((Real.pi : ℂ) * Complex.I) * s = 4 * z := by
    dsimp only [z]
    push_cast
    ring
  have hcos : ((Real.pi : ℂ) * s / 2) * Complex.I = 2 * z := by
    dsimp only [z]
    push_cast
    ring
  have hcosNeg : -((Real.pi : ℂ) * s / 2) * Complex.I = -(2 * z) := by
    rw [neg_mul, hcos]
  rw [hpi, Complex.two_cos, hcos, hcosNeg]
  calc
    (1 + Complex.exp (-(4 * z))) * Complex.exp z =
        Complex.exp z + Complex.exp (-3 * z) := by
      rw [add_mul, one_mul, ← Complex.exp_add]
      congr 1
      ring
    _ = (Complex.exp (2 * z) + Complex.exp (-(2 * z))) *
        Complex.exp (-z) := by
      rw [add_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1 <;> ring

theorem deBruijnNewmanRiemannSiegelCos_ne_zero_of_isNoninteger {s : ℂ} (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  rw [Complex.cos_ne_zero_iff]
  intro k hk
  apply hs (2 * k + 1)
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi] at hk
  calc
    s = 2 * (k : ℂ) + 1 := hk
    _ = ((2 * k + 1 : ℤ) : ℂ) := by
      push_cast
      ring

theorem deBruijnNewmanRiemannSiegel_gamma_core {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) * Complex.Gamma (s / 2) =
      2 * Complex.Gamma s * (Real.pi : ℂ) ^ ((s - 1) / 2) *
        Complex.Gamma ((1 - s) / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 :=
    deBruijnNewmanRiemannSiegelCos_ne_zero_of_isNoninteger hs
  have hplusRe : 0 < (((1 + s) / 2 : ℂ).re) := by
    norm_num [div_re]
    linarith
  have hplus : Complex.Gamma ((1 + s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hplusRe
  have href :
      Complex.Gamma ((1 - s) / 2) * Complex.Gamma ((1 + s) / 2) =
        (Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ) * s / 2) := by
    calc
      Complex.Gamma ((1 - s) / 2) * Complex.Gamma ((1 + s) / 2) =
          Complex.Gamma ((1 - s) / 2) *
            Complex.Gamma (1 - ((1 - s) / 2)) := by
              congr 2
              ring
      _ = (Real.pi : ℂ) /
          Complex.sin ((Real.pi : ℂ) * ((1 - s) / 2)) :=
        Complex.Gamma_mul_Gamma_one_sub _
      _ = (Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ) * s / 2) := by
        congr 1
        rw [show (Real.pi : ℂ) * ((1 - s) / 2) =
            (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring]
        exact Complex.sin_pi_div_two_sub _
  have hrefMul :
      Complex.Gamma ((1 - s) / 2) * Complex.Gamma ((1 + s) / 2) *
          Complex.cos ((Real.pi : ℂ) * s / 2) = (Real.pi : ℂ) := by
    rw [href]
    exact div_mul_cancel₀ _ hcos
  have hdup :
      Complex.Gamma (s / 2) * Complex.Gamma ((1 + s) / 2) =
        Complex.Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) := by
    calc
      Complex.Gamma (s / 2) * Complex.Gamma ((1 + s) / 2) =
          Complex.Gamma (s / 2) * Complex.Gamma (s / 2 + 1 / 2) := by
            congr 2
            ring
      _ = Complex.Gamma (2 * (s / 2)) *
          (2 : ℂ) ^ (1 - 2 * (s / 2)) * (Real.sqrt Real.pi : ℂ) :=
        Complex.Gamma_mul_Gamma_add_half _
      _ = Complex.Gamma s * (2 : ℂ) ^ (1 - s) *
          (Real.sqrt Real.pi : ℂ) := by ring_nf
  have htwoPowers : (2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s) = 2 := by
    rw [← Complex.cpow_add _ _ htwo]
    convert Complex.cpow_one (2 : ℂ) using 1 <;> ring
  have hsqrtPi : (Real.sqrt Real.pi : ℂ) =
      (Real.pi : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hpiPowers :
      (Real.pi : ℂ) ^ (s / 2) * (Real.sqrt Real.pi : ℂ) =
        (Real.pi : ℂ) ^ ((s - 1) / 2) * (Real.pi : ℂ) := by
    calc
      (Real.pi : ℂ) ^ (s / 2) * (Real.sqrt Real.pi : ℂ) =
          (Real.pi : ℂ) ^ (s / 2) * (Real.pi : ℂ) ^ ((1 : ℂ) / 2) := by
            rw [hsqrtPi]
      _ = (Real.pi : ℂ) ^ (s / 2 + (1 : ℂ) / 2) :=
        (Complex.cpow_add _ _ hpi).symm
      _ = (Real.pi : ℂ) ^ ((s - 1) / 2 + 1) := by
        congr 1
        ring
      _ = (Real.pi : ℂ) ^ ((s - 1) / 2) * (Real.pi : ℂ) ^ (1 : ℂ) :=
        Complex.cpow_add _ _ hpi
      _ = (Real.pi : ℂ) ^ ((s - 1) / 2) * (Real.pi : ℂ) := by
        rw [Complex.cpow_one]
  apply mul_right_cancel₀ hplus
  calc
    ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) * Complex.Gamma (s / 2)) *
          Complex.Gamma ((1 + s) / 2) =
        (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
          (Complex.Gamma (s / 2) * Complex.Gamma ((1 + s) / 2)) := by ring
    _ = (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
          (Complex.Gamma s * (2 : ℂ) ^ (1 - s) *
            (Real.sqrt Real.pi : ℂ)) := by rw [hdup]
    _ = ((2 : ℂ) ^ s * (2 : ℂ) ^ (1 - s)) * Complex.Gamma s *
          ((Real.pi : ℂ) ^ (s / 2) * (Real.sqrt Real.pi : ℂ)) := by ring
    _ = 2 * Complex.Gamma s *
          ((Real.pi : ℂ) ^ ((s - 1) / 2) * (Real.pi : ℂ)) := by
      rw [htwoPowers, hpiPowers]
    _ = 2 * Complex.Gamma s * (Real.pi : ℂ) ^ ((s - 1) / 2) *
          (Complex.Gamma ((1 - s) / 2) *
            Complex.Gamma ((1 + s) / 2) *
              Complex.cos ((Real.pi : ℂ) * s / 2)) := by
      rw [hrefMul]
      ring
    _ = (2 * Complex.Gamma s * (Real.pi : ℂ) ^ ((s - 1) / 2) *
          Complex.Gamma ((1 - s) / 2) *
            Complex.cos ((Real.pi : ℂ) * s / 2)) *
          Complex.Gamma ((1 + s) / 2) := by ring

theorem deBruijnNewmanRiemannSiegel_cpow_scale (s : ℂ) :
    (Real.pi : ℂ) ^ (-s / 2) *
        ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) =
      (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have htwoPi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hsplit : (((2 * Real.pi : ℝ) : ℂ)) ^ (s - 1) =
      (2 : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (s - 1) := by
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) Real.pi_pos.le _
  have htwoPowers : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
    calc
      (2 : ℂ) ^ (s - 1) * 2 =
          (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (2 : ℂ) ^ ((s - 1) + 1) :=
        (Complex.cpow_add _ _ htwo).symm
      _ = (2 : ℂ) ^ s := by congr 1 <;> ring
  have hpiPowers :
      (Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s - 1) *
          (Real.pi : ℂ) = (Real.pi : ℂ) ^ (s / 2) := by
    calc
      (Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s - 1) *
          (Real.pi : ℂ) =
        (Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s - 1) *
          (Real.pi : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (Real.pi : ℂ) ^ ((-s / 2) + (s - 1)) *
          (Real.pi : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_add]
        exact hpi
      _ = (Real.pi : ℂ) ^ ((-s / 2) + (s - 1) + 1) :=
        (Complex.cpow_add _ _ hpi).symm
      _ = (Real.pi : ℂ) ^ (s / 2) := by congr 1 <;> ring
  apply mul_right_cancel₀ htwoPi
  calc
    ((Real.pi : ℂ) ^ (-s / 2) * (((2 * Real.pi : ℝ) : ℂ) ^ (s - 1))) *
          (((2 * Real.pi : ℝ) : ℂ)) =
        ((2 : ℂ) ^ (s - 1) * 2) *
          ((Real.pi : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (s - 1) *
            (Real.pi : ℂ)) := by
      rw [hsplit]
      push_cast
      ring
    _ = (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) := by
      rw [htwoPowers, hpiPowers]
    _ = ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
            (((2 * Real.pi : ℝ) : ℂ)) := by
      field_simp [htwoPi]

theorem deBruijnNewmanRiemannSiegel_gamma_coefficient {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) =
      Complex.Gamma s * (Real.pi : ℂ) ^ (-(1 - s) / 2) *
        Complex.Gamma ((1 - s) / 2) *
          (2 * Complex.cos ((Real.pi : ℂ) * s / 2)) *
            (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by
  have hcore := deBruijnNewmanRiemannSiegel_gamma_core hsRe hs
  have hscale := deBruijnNewmanRiemannSiegel_cpow_scale s
  calc
    (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
          ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) =
        ((Real.pi : ℂ) ^ (-s / 2) *
          ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1)) *
            Complex.Gamma (s / 2) := by ring
    _ = ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹)) * Complex.Gamma (s / 2) := by
      rw [hscale]
    _ = ((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s / 2) *
          Complex.Gamma (s / 2)) * (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by ring
    _ = (2 * Complex.Gamma s * (Real.pi : ℂ) ^ ((s - 1) / 2) *
          Complex.Gamma ((1 - s) / 2) *
            Complex.cos ((Real.pi : ℂ) * s / 2)) *
              (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by rw [hcore]
    _ = Complex.Gamma s * (Real.pi : ℂ) ^ (-(1 - s) / 2) *
          Complex.Gamma ((1 - s) / 2) *
            (2 * Complex.cos ((Real.pi : ℂ) * s / 2)) *
              (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by
      have hexp : -(1 - s) / 2 = (s - 1) / 2 := by ring
      rw [hexp]
      ring

theorem deBruijnNewmanRiemannSiegel_prefactor_coefficient {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    deBruijnNewmanRiemannSiegelPrefactor s *
        (((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ s) =
      Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
        ((1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
          deBruijnNewmanTitchmarshPhiDirection ^ s *
            (((2 * Real.pi : ℝ) : ℂ)⁻¹)) := by
  have hphase := deBruijnNewmanTitchmarsh_phase_cpow s
  have hcoef := deBruijnNewmanRiemannSiegel_gamma_coefficient hsRe hs
  rw [hphase]
  unfold deBruijnNewmanRiemannSiegelPrefactor
  calc
    (1 / 8) * (s * (s - 1) / 2) * (Real.pi : ℂ) ^ (-s / 2) *
          Complex.Gamma (s / 2) *
            (((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
              deBruijnNewmanTitchmarshMellinRayDirection ^ s) =
        ((1 / 8) * (s * (s - 1) / 2)) *
          ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
            ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1)) *
              deBruijnNewmanTitchmarshMellinRayDirection ^ s := by ring
    _ = ((1 / 8) * (s * (s - 1) / 2)) *
          (Complex.Gamma s * (Real.pi : ℂ) ^ (-(1 - s) / 2) *
            Complex.Gamma ((1 - s) / 2) *
              (2 * Complex.cos ((Real.pi : ℂ) * s / 2)) *
                (((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
              deBruijnNewmanTitchmarshMellinRayDirection ^ s := by rw [hcoef]
    _ = Complex.Gamma s *
          ((1 / 8) * ((1 - s) * ((1 - s) - 1) / 2) *
            (Real.pi : ℂ) ^ (-(1 - s) / 2) *
              Complex.Gamma ((1 - s) / 2)) *
            ((2 * Complex.cos ((Real.pi : ℂ) * s / 2)) *
              deBruijnNewmanTitchmarshMellinRayDirection ^ s *
                (((2 * Real.pi : ℝ) : ℂ)⁻¹)) := by ring

theorem deBruijnNewmanRiemannSiegel_remainder_scaled {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    deBruijnNewmanRiemannSiegelPrefactor s *
        (∫ r : ℝ in Ioi 0,
          deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
      Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
        deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  let A : ℂ :=
    (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
      deBruijnNewmanTitchmarshPhiDirection ^ s *
        (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  let B : ℂ :=
    ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
      deBruijnNewmanTitchmarshMellinRayDirection ^ s
  have hrem : A *
      (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
        B * deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
    dsimp only [A, B]
    convert
      deBruijnNewmanTitchmarshMellinRemainderRayIntegral_phase_scaled_eq_raw
        hsRe using 1 <;> ring
  have hcoef :
      deBruijnNewmanRiemannSiegelPrefactor s * B =
        Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) * A := by
    dsimp only [A, B]
    exact deBruijnNewmanRiemannSiegel_prefactor_coefficient hsRe hs
  have htwoPi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hray : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hB : B ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl htwoPi)
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hray)
  apply mul_right_cancel₀ hB
  calc
    (deBruijnNewmanRiemannSiegelPrefactor s *
          (∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r)) * B =
        (deBruijnNewmanRiemannSiegelPrefactor s * B) *
          (∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by ring
    _ = (Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) * A) *
          (∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by rw [hcoef]
    _ = (Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s)) *
          (A * ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by ring
    _ = (Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s)) *
          (B * deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s)) := by rw [hrem]
    _ = (Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s)) * B := by ring

theorem deBruijnNewmanRiemannSiegel_raw_halfPlane {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    deBruijnNewmanRiemannSiegelPrefactor s * riemannZeta s =
      deBruijnNewmanRiemannSiegelPrefactor s *
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelRawIntegral 0) s +
        deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  have htwo := deBruijnNewmanTitchmarshMellin_two_contours
    (show 1 < s.re by linarith)
  have hscaled := deBruijnNewmanRiemannSiegel_remainder_scaled hsRe hs
  have hgamma : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hzeta :
      Complex.Gamma s * riemannZeta s =
        Complex.Gamma s *
            deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelRawIntegral 0) s +
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r := by
    linear_combination -htwo
  apply mul_left_cancel₀ hgamma
  calc
    Complex.Gamma s *
          (deBruijnNewmanRiemannSiegelPrefactor s * riemannZeta s) =
        deBruijnNewmanRiemannSiegelPrefactor s *
          (Complex.Gamma s * riemannZeta s) := by ring
    _ = deBruijnNewmanRiemannSiegelPrefactor s *
          (Complex.Gamma s *
              deBruijnNewmanRiemannSiegelReflect
                (deBruijnNewmanRiemannSiegelRawIntegral 0) s +
            ∫ r : ℝ in Ioi 0,
              deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by
      rw [hzeta]
    _ = Complex.Gamma s *
          (deBruijnNewmanRiemannSiegelPrefactor s *
            deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelRawIntegral 0) s) +
        deBruijnNewmanRiemannSiegelPrefactor s *
          (∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by ring
    _ = Complex.Gamma s *
          (deBruijnNewmanRiemannSiegelPrefactor s *
            deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelRawIntegral 0) s) +
        Complex.Gamma s * deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by rw [hscaled]
    _ = Complex.Gamma s *
          (deBruijnNewmanRiemannSiegelPrefactor s *
              deBruijnNewmanRiemannSiegelReflect
                (deBruijnNewmanRiemannSiegelRawIntegral 0) s +
            deBruijnNewmanRiemannSiegelPrefactor (1 - s) *
              deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s)) := by ring

theorem deBruijnNewmanRiemannSiegel_xi_halfPlane {s : ℂ} (hs : 1 < s.re) :
    (1 / 8) * riemannXi s =
      deBruijnNewmanRiemannSiegelPrefactor s * riemannZeta s := by
  rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta hs]
  rw [Complex.Gammaℝ_def]
  unfold deBruijnNewmanRiemannSiegelPrefactor
  ring

theorem deBruijnNewmanRiemannSiegel_prefactor_reflect (s : ℂ) :
    deBruijnNewmanRiemannSiegelReflect
        deBruijnNewmanRiemannSiegelPrefactor s =
      deBruijnNewmanRiemannSiegelPrefactor s := by
  have harg : Complex.arg (Real.pi : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  have hcpow := Complex.conj_cpow (Real.pi : ℂ) (-s / 2) harg
  simp only [conj_ofReal, map_neg, map_div₀, map_ofNat] at hcpow
  unfold deBruijnNewmanRiemannSiegelReflect
  unfold deBruijnNewmanRiemannSiegelPrefactor
  simp only [map_mul, map_div₀, map_sub, map_one, map_ofNat, conj_conj,
    ]
  rw [← Complex.Gamma_conj]
  simp only [map_div₀, map_ofNat, conj_conj]
  rw [← hcpow]

theorem deBruijnNewmanRiemannSiegelR0N_reflect (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0N N) s =
      deBruijnNewmanRiemannSiegelPrefactor s *
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelRawIntegral N) s := by
  unfold deBruijnNewmanRiemannSiegelReflect
  unfold deBruijnNewmanRiemannSiegelR0N
  rw [map_mul]
  change deBruijnNewmanRiemannSiegelReflect
      deBruijnNewmanRiemannSiegelPrefactor s * _ = _
  rw [deBruijnNewmanRiemannSiegel_prefactor_reflect]

theorem deBruijnNewmanRiemannSiegel_xio_swapped_halfPlane {s : ℂ} (hsRe : 2 < s.re) (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      deBruijnNewmanRiemannSiegelR0N 0 (1 - s) +
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0N 0) s := by
  rw [deBruijnNewmanRiemannSiegel_xi_halfPlane (show 1 < s.re by linarith)]
  rw [deBruijnNewmanRiemannSiegel_raw_halfPlane hsRe hs]
  rw [deBruijnNewmanRiemannSiegelR0N_reflect]
  unfold deBruijnNewmanRiemannSiegelR0N
  ring

def deBruijnNewmanRiemannSiegelLineIntegrandDerivative (N : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  -Complex.log (deBruijnNewmanRiemannSiegelLine N v) *
    deBruijnNewmanRiemannSiegelLineIntegrand N s v

theorem deBruijnNewmanRiemannSiegelLineIntegrand_hasDerivAt (N : ℕ) (s : ℂ) (v : ℝ) :
    HasDerivAt (fun z : ℂ =>
      deBruijnNewmanRiemannSiegelLineIntegrand N z v)
      (deBruijnNewmanRiemannSiegelLineIntegrandDerivative N s v) s := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hw : w ≠ 0 := Complex.slitPlane_ne_zero
    (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)
  have hlinear := (hasDerivAt_id s).neg.mul_const (Complex.log w)
  have hexp := hlinear.cexp
  unfold deBruijnNewmanRiemannSiegelLineIntegrandDerivative
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
  unfold deBruijnNewmanRiemannSiegelKernel
  unfold deBruijnNewmanRiemannSiegelNumerator
  let C : ℂ := Complex.exp (Complex.I * Real.pi * w ^ 2) /
    deBruijnNewmanRiemannSiegelDenominator w *
      deBruijnNewmanRiemannSiegelDirection
  have hmain : HasDerivAt
      (fun z : ℂ => w ^ (-z) * C)
      (-Complex.log w * (w ^ (-s) * C)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hw]
    simpa only [Pi.neg_apply, id_eq, one_mul, neg_mul, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hexp.mul_const C
  convert hmain using 1
  · funext z
    dsimp only [C, w]
    ring
  · dsimp only [C, w]
    ring

theorem norm_log_deBruijnNewmanRiemannSiegelLine_le (N : ℕ) (v : ℝ) :
    ‖Complex.log (deBruijnNewmanRiemannSiegelLine N v)‖ ≤
      N + 1 / 2 + |v| + 4 + Real.pi := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hnorm := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
  rw [Complex.log_re, Complex.log_im] at hnorm
  have hre := abs_log_norm_deBruijnNewmanRiemannSiegelLine_le N v
  have him := Complex.abs_arg_le_pi w
  exact hnorm.trans (add_le_add hre him)

def deBruijnNewmanRiemannSiegelLocalParameter (s : ℂ) : ℂ :=
  ⟨|s.re| + 1, |s.im| + 1⟩

@[simp] theorem deBruijnNewmanRiemannSiegelLocalParameter_re (s : ℂ) :
    (deBruijnNewmanRiemannSiegelLocalParameter s).re = |s.re| + 1 := rfl

@[simp] theorem deBruijnNewmanRiemannSiegelLocalParameter_im (s : ℂ) :
    (deBruijnNewmanRiemannSiegelLocalParameter s).im = |s.im| + 1 := rfl

theorem deBruijnNewmanRiemannSiegel_abs_re_le_localParameter {s x : ℂ} (hx : x ∈ Metric.ball s 1) :
    |x.re| ≤ |s.re| + 1 := by
  have hdist : ‖x - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hre : |x.re - s.re| ≤ ‖x - s‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (x - s)
  calc
    |x.re| = |s.re + (x.re - s.re)| := by congr 1 <;> ring
    _ ≤ |s.re| + |x.re - s.re| := abs_add_le _ _
    _ ≤ |s.re| + 1 := by linarith

theorem deBruijnNewmanRiemannSiegel_abs_im_le_localParameter {s x : ℂ} (hx : x ∈ Metric.ball s 1) :
    |x.im| ≤ |s.im| + 1 := by
  have hdist : ‖x - s‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have him : |x.im - s.im| ≤ ‖x - s‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (x - s)
  calc
    |x.im| = |s.im + (x.im - s.im)| := by congr 1 <;> ring
    _ ≤ |s.im| + |x.im - s.im| := abs_add_le _ _
    _ ≤ |s.im| + 1 := by linarith

theorem deBruijnNewmanRiemannSiegelMajorant_le_localParameter (N : ℕ) {s x : ℂ}
    (hx : x ∈ Metric.ball s 1) (v : ℝ) :
    deBruijnNewmanRiemannSiegelMajorant N x v ≤
      deBruijnNewmanRiemannSiegelMajorant N (deBruijnNewmanRiemannSiegelLocalParameter s) v := by
  have hre := deBruijnNewmanRiemannSiegel_abs_re_le_localParameter hx
  have him := deBruijnNewmanRiemannSiegel_abs_im_le_localParameter hx
  have hlocalRe : |(deBruijnNewmanRiemannSiegelLocalParameter s).re| = |s.re| + 1 := by
    rw [deBruijnNewmanRiemannSiegelLocalParameter_re, abs_of_nonneg]
    positivity
  have hlocalIm : |(deBruijnNewmanRiemannSiegelLocalParameter s).im| = |s.im| + 1 := by
    rw [deBruijnNewmanRiemannSiegelLocalParameter_im, abs_of_nonneg]
    positivity
  have hlinear :
      deBruijnNewmanRiemannSiegelLinearRate N x ≤
        deBruijnNewmanRiemannSiegelLinearRate N (deBruijnNewmanRiemannSiegelLocalParameter s) := by
    unfold deBruijnNewmanRiemannSiegelLinearRate
    rw [hlocalRe]
    linarith
  have hlinearNonneg : 0 ≤ deBruijnNewmanRiemannSiegelLinearRate N x := by
    unfold deBruijnNewmanRiemannSiegelLinearRate
    positivity
  have hlocalLinearNonneg :
      0 ≤ deBruijnNewmanRiemannSiegelLinearRate N (deBruijnNewmanRiemannSiegelLocalParameter s) := by
    unfold deBruijnNewmanRiemannSiegelLinearRate
    positivity
  have hsq : deBruijnNewmanRiemannSiegelLinearRate N x ^ 2 ≤
      deBruijnNewmanRiemannSiegelLinearRate N (deBruijnNewmanRiemannSiegelLocalParameter s) ^ 2 := by
    exact (sq_le_sq₀ hlinearNonneg hlocalLinearNonneg).mpr hlinear
  have hbase : 0 ≤ (N : ℝ) + 1 / 2 + 4 := by positivity
  have hreMul : |x.re| * ((N : ℝ) + 1 / 2 + 4) ≤
      (|s.re| + 1) * ((N : ℝ) + 1 / 2 + 4) :=
    mul_le_mul_of_nonneg_right hre hbase
  have himMul : |x.im| * Real.pi ≤ (|s.im| + 1) * Real.pi :=
    mul_le_mul_of_nonneg_right him Real.pi_pos.le
  have hconst :
      deBruijnNewmanRiemannSiegelMajorantConstant N x ≤
        deBruijnNewmanRiemannSiegelMajorantConstant N (deBruijnNewmanRiemannSiegelLocalParameter s) := by
    unfold deBruijnNewmanRiemannSiegelMajorantConstant
    rw [hlocalRe, hlocalIm]
    have hpi : 0 < 2 * Real.pi := by positivity
    have hsqDiv := (div_le_div_iff_of_pos_right hpi).mpr hsq
    linarith
  unfold deBruijnNewmanRiemannSiegelMajorant
  gcongr

def deBruijnNewmanRiemannSiegelDerivativeMajorant (N : ℕ) (s : ℂ) (v : ℝ) : ℝ :=
  (N + 1 / 2 + |v| + 4 + Real.pi) *
    deBruijnNewmanRiemannSiegelMajorant N (deBruijnNewmanRiemannSiegelLocalParameter s) v

theorem norm_deBruijnNewmanRiemannSiegelLineIntegrandDerivative_le_majorant
    (N : ℕ) {s x : ℂ} (hx : x ∈ Metric.ball s 1) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrandDerivative N x v‖ ≤ deBruijnNewmanRiemannSiegelDerivativeMajorant N s v := by
  have hlog := norm_log_deBruijnNewmanRiemannSiegelLine_le N v
  have hline := (norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_majorant N x v).trans
    (deBruijnNewmanRiemannSiegelMajorant_le_localParameter N hx v)
  unfold deBruijnNewmanRiemannSiegelLineIntegrandDerivative deBruijnNewmanRiemannSiegelDerivativeMajorant
  rw [norm_mul, norm_neg]
  calc
    ‖Complex.log (deBruijnNewmanRiemannSiegelLine N v)‖ *
          ‖deBruijnNewmanRiemannSiegelLineIntegrand N x v‖ ≤
        (N + 1 / 2 + |v| + 4 + Real.pi) *
          ‖deBruijnNewmanRiemannSiegelLineIntegrand N x v‖ :=
      mul_le_mul_of_nonneg_right hlog (norm_nonneg _)
    _ ≤ (N + 1 / 2 + |v| + 4 + Real.pi) *
          deBruijnNewmanRiemannSiegelMajorant N (deBruijnNewmanRiemannSiegelLocalParameter s) v := by
      apply mul_le_mul_of_nonneg_left hline
      positivity

theorem integrable_deBruijnNewmanRiemannSiegelDerivativeMajorant (N : ℕ) (s : ℂ) :
    Integrable (deBruijnNewmanRiemannSiegelDerivativeMajorant N s) := by
  let a : ℝ := Real.pi / 2
  let K : ℝ := (1 / 2) *
    Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant N (deBruijnNewmanRiemannSiegelLocalParameter s))
  let C : ℝ := N + 1 / 2 + 4 + Real.pi
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hgauss : Integrable (fun v : ℝ => Real.exp (-a * v ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have habs : Integrable (fun v : ℝ => |v| * Real.exp (-a * v ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)] using
        (integrable_mul_exp_neg_mul_sq ha).norm
  have hsum := (habs.const_mul K).add (hgauss.const_mul (C * K))
  have hfun : deBruijnNewmanRiemannSiegelDerivativeMajorant N s =
      (fun v : ℝ => K * (|v| * Real.exp (-a * v ^ 2)) +
        C * K * Real.exp (-a * v ^ 2)) := by
    funext v
    unfold deBruijnNewmanRiemannSiegelDerivativeMajorant deBruijnNewmanRiemannSiegelMajorant
    dsimp only [a, K, C]
    ring
  rw [hfun]
  exact hsum

theorem continuous_deBruijnNewmanRiemannSiegelLineIntegrandDerivative (N : ℕ) (s : ℂ) :
    Continuous (deBruijnNewmanRiemannSiegelLineIntegrandDerivative N s) := by
  have hline : Continuous (deBruijnNewmanRiemannSiegelLine N) := by
    unfold deBruijnNewmanRiemannSiegelLine
    fun_prop
  have hlog : Continuous (fun v : ℝ =>
      Complex.log (deBruijnNewmanRiemannSiegelLine N v)) := by
    rw [continuous_iff_continuousAt]
    intro v
    exact hline.continuousAt.clog
      (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)
  unfold deBruijnNewmanRiemannSiegelLineIntegrandDerivative
  exact hlog.neg.mul
    (continuous_deBruijnNewmanRiemannSiegelLineIntegrand N s)

theorem deBruijnNewmanRiemannSiegelRawIntegral_hasDerivAt (N : ℕ) (s : ℂ) :
    HasDerivAt (deBruijnNewmanRiemannSiegelRawIntegral N)
      (∫ v : ℝ, deBruijnNewmanRiemannSiegelLineIntegrandDerivative N s v) s := by
  let F : ℂ → ℝ → ℂ := fun z v =>
    deBruijnNewmanRiemannSiegelLineIntegrand N z v
  let F' : ℂ → ℝ → ℂ := fun z v => deBruijnNewmanRiemannSiegelLineIntegrandDerivative N z v
  let bound : ℝ → ℝ := deBruijnNewmanRiemannSiegelDerivativeMajorant N s
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := bound)
    (s := Metric.ball s 1) (x₀ := s)
    (Metric.ball_mem_nhds s zero_lt_one)
    (Filter.Eventually.of_forall fun z =>
      (continuous_deBruijnNewmanRiemannSiegelLineIntegrand N z).aestronglyMeasurable)
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N s)
    (continuous_deBruijnNewmanRiemannSiegelLineIntegrandDerivative N s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v z hz =>
      norm_deBruijnNewmanRiemannSiegelLineIntegrandDerivative_le_majorant N hz v)
    (integrable_deBruijnNewmanRiemannSiegelDerivativeMajorant N s)
    (Filter.Eventually.of_forall fun v z _ => deBruijnNewmanRiemannSiegelLineIntegrand_hasDerivAt N z v)
  unfold deBruijnNewmanRiemannSiegelRawIntegral
  exact hmain.2

theorem differentiable_deBruijnNewmanRiemannSiegelRawIntegral (N : ℕ) :
    Differentiable ℂ (deBruijnNewmanRiemannSiegelRawIntegral N) :=
  fun s => (deBruijnNewmanRiemannSiegelRawIntegral_hasDerivAt N s).differentiableAt

def deBruijnNewmanRiemannSiegelComplexIntegerSet : Set ℂ :=
  Set.range (fun n : ℤ => (n : ℂ))

def deBruijnNewmanRiemannSiegelNonintegerDomain : Set ℂ :=
  deBruijnNewmanRiemannSiegelComplexIntegerSetᶜ

theorem mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff {s : ℂ} :
    s ∈ deBruijnNewmanRiemannSiegelNonintegerDomain ↔ deBruijnNewmanRiemannSiegelIsNoninteger s := by
  simp only [deBruijnNewmanRiemannSiegelNonintegerDomain, deBruijnNewmanRiemannSiegelComplexIntegerSet, mem_compl_iff, mem_range, not_exists]
  exact forall_congr' fun n => not_congr eq_comm

theorem isClosed_deBruijnNewmanRiemannSiegelComplexIntegerSet : IsClosed deBruijnNewmanRiemannSiegelComplexIntegerSet := by
  have hclosed : IsClosedEmbedding (fun n : ℤ => ((n : ℝ) : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  simpa only [deBruijnNewmanRiemannSiegelComplexIntegerSet, Int.cast_ofNat, Complex.ofReal_intCast] using
    hclosed.isClosed_range

theorem isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain : IsOpen deBruijnNewmanRiemannSiegelNonintegerDomain := by
  exact isClosed_deBruijnNewmanRiemannSiegelComplexIntegerSet.isOpen_compl

theorem isPreconnected_deBruijnNewmanRiemannSiegelNonintegerDomain : IsPreconnected deBruijnNewmanRiemannSiegelNonintegerDomain := by
  have hcount : deBruijnNewmanRiemannSiegelComplexIntegerSet.Countable := Set.countable_range _
  exact (hcount.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

theorem differentiableAt_deBruijnNewmanRiemannSiegelPrefactor_of_isNoninteger {s : ℂ} (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    DifferentiableAt ℂ deBruijnNewmanRiemannSiegelPrefactor s := by
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s).const_cpow
      (Or.inl hpi)
  have hgammaPole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    apply hs (-2 * (m : ℤ))
    calc
      s = -2 * (m : ℂ) := by linear_combination 2 * hm
      _ = ((-2 * (m : ℤ) : ℤ) : ℂ) := by
        push_cast
        ring
  have hgammaAt : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ hgammaPole
  have hgamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hgammaAt.comp s (by fun_prop)
  have hpoly : DifferentiableAt ℂ
      (fun z : ℂ => (1 / 8) * (z * (z - 1) / 2)) s := by fun_prop
  unfold deBruijnNewmanRiemannSiegelPrefactor
  exact (hpoly.mul hpow).mul hgamma

theorem differentiableOn_deBruijnNewmanRiemannSiegelPrefactor_nonintegerDomain :
    DifferentiableOn ℂ deBruijnNewmanRiemannSiegelPrefactor deBruijnNewmanRiemannSiegelNonintegerDomain := by
  intro s hs
  exact (differentiableAt_deBruijnNewmanRiemannSiegelPrefactor_of_isNoninteger
    (mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff.mp hs)).differentiableWithinAt

theorem differentiable_deBruijnNewmanRiemannSiegelReflectRawIntegral (N : ℕ) :
    Differentiable ℂ (deBruijnNewmanRiemannSiegelReflect
      (deBruijnNewmanRiemannSiegelRawIntegral N)) := by
  intro s
  unfold deBruijnNewmanRiemannSiegelReflect
  change DifferentiableAt ℂ
    (conj ∘ deBruijnNewmanRiemannSiegelRawIntegral N ∘ conj) s
  exact differentiableAt_conj_conj_iff.mpr
    (differentiable_deBruijnNewmanRiemannSiegelRawIntegral N (conj s))

theorem differentiableOn_deBruijnNewmanRiemannSiegelR0N_nonintegerDomain (N : ℕ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelR0N N) deBruijnNewmanRiemannSiegelNonintegerDomain := by
  unfold deBruijnNewmanRiemannSiegelR0N
  exact differentiableOn_deBruijnNewmanRiemannSiegelPrefactor_nonintegerDomain.mul
    (differentiable_deBruijnNewmanRiemannSiegelRawIntegral N).differentiableOn

theorem one_sub_mem_deBruijnNewmanRiemannSiegelNonintegerDomain {s : ℂ} (hs : s ∈ deBruijnNewmanRiemannSiegelNonintegerDomain) :
    1 - s ∈ deBruijnNewmanRiemannSiegelNonintegerDomain := by
  rw [mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff] at hs ⊢
  intro n hn
  apply hs (1 - n)
  calc
    s = 1 - (n : ℂ) := by linear_combination -hn
    _ = ((1 - n : ℤ) : ℂ) := by push_cast; rfl

theorem differentiableOn_deBruijnNewmanRiemannSiegelR0N_one_sub_nonintegerDomain (N : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ => deBruijnNewmanRiemannSiegelR0N N (1 - s))
      deBruijnNewmanRiemannSiegelNonintegerDomain := by
  intro s hs
  have htarget := one_sub_mem_deBruijnNewmanRiemannSiegelNonintegerDomain hs
  have hR := (differentiableOn_deBruijnNewmanRiemannSiegelR0N_nonintegerDomain N (1 - s) htarget).differentiableAt
    (isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain.mem_nhds htarget)
  exact (hR.comp s (by fun_prop)).differentiableWithinAt

theorem differentiableOn_deBruijnNewmanRiemannSiegelReflectR0N_nonintegerDomain (N : ℕ) :
    DifferentiableOn ℂ
      (deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0N N)) deBruijnNewmanRiemannSiegelNonintegerDomain := by
  have heq : deBruijnNewmanRiemannSiegelReflect
      (deBruijnNewmanRiemannSiegelR0N N) =
      fun z => deBruijnNewmanRiemannSiegelPrefactor z *
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelRawIntegral N) z := by
    funext z
    exact deBruijnNewmanRiemannSiegelR0N_reflect N z
  rw [heq]
  intro s hs
  exact (differentiableOn_deBruijnNewmanRiemannSiegelPrefactor_nonintegerDomain s hs).mul
    (differentiable_deBruijnNewmanRiemannSiegelReflectRawIntegral N s).differentiableWithinAt

def deBruijnNewmanRiemannSiegelXioLeft (s : ℂ) : ℂ :=
  (1 / 8) * riemannXi s

def deBruijnNewmanRiemannSiegelXioRightSwapped (s : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelR0N 0 (1 - s) +
    deBruijnNewmanRiemannSiegelReflect
      (deBruijnNewmanRiemannSiegelR0N 0) s

theorem analyticOnNhd_deBruijnNewmanRiemannSiegelXioLeft_nonintegerDomain :
    AnalyticOnNhd ℂ deBruijnNewmanRiemannSiegelXioLeft deBruijnNewmanRiemannSiegelNonintegerDomain := by
  apply (analyticOnNhd_iff_differentiableOn isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain).mpr
  unfold deBruijnNewmanRiemannSiegelXioLeft
  exact ((differentiable_const (c := (1 / 8 : ℂ))).mul
    differentiable_riemannXi).differentiableOn

theorem analyticOnNhd_deBruijnNewmanRiemannSiegelXioRightSwapped_nonintegerDomain :
    AnalyticOnNhd ℂ deBruijnNewmanRiemannSiegelXioRightSwapped deBruijnNewmanRiemannSiegelNonintegerDomain := by
  apply (analyticOnNhd_iff_differentiableOn isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain).mpr
  unfold deBruijnNewmanRiemannSiegelXioRightSwapped
  exact (differentiableOn_deBruijnNewmanRiemannSiegelR0N_one_sub_nonintegerDomain 0).add
    (differentiableOn_deBruijnNewmanRiemannSiegelReflectR0N_nonintegerDomain 0)

theorem deBruijnNewmanRiemannSiegel_xio_swapped {s : ℂ} (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      deBruijnNewmanRiemannSiegelR0N 0 (1 - s) +
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0N 0) s := by
  let z0 : ℂ := 3 + Complex.I
  have hz0 : z0 ∈ deBruijnNewmanRiemannSiegelNonintegerDomain := by
    rw [mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff]
    intro n hn
    have him := congrArg Complex.im hn
    dsimp only [z0] at him
    simp at him
  have hre : {z : ℂ | 2 < z.re} ∈ 𝓝 z0 := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    dsimp only [z0]
    norm_num
  have hdomain : deBruijnNewmanRiemannSiegelNonintegerDomain ∈ 𝓝 z0 :=
    isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain.mem_nhds hz0
  have hevent : deBruijnNewmanRiemannSiegelXioLeft =ᶠ[𝓝 z0] deBruijnNewmanRiemannSiegelXioRightSwapped := by
    filter_upwards [hre, hdomain] with z hzRe hzDomain
    unfold deBruijnNewmanRiemannSiegelXioLeft deBruijnNewmanRiemannSiegelXioRightSwapped
    exact deBruijnNewmanRiemannSiegel_xio_swapped_halfPlane hzRe (mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff.mp hzDomain)
  have heq :=
    analyticOnNhd_deBruijnNewmanRiemannSiegelXioLeft_nonintegerDomain.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_deBruijnNewmanRiemannSiegelXioRightSwapped_nonintegerDomain
      isPreconnected_deBruijnNewmanRiemannSiegelNonintegerDomain hz0 hevent
  exact heq (mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff.mpr hs)

theorem deBruijnNewmanRiemannSiegel_xio {s : ℂ} (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      deBruijnNewmanRiemannSiegelR0N 0 s +
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0N 0) (1 - s) := by
  have hsDomain : s ∈ deBruijnNewmanRiemannSiegelNonintegerDomain := mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff.mpr hs
  have hOneSub := mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff.mp (one_sub_mem_deBruijnNewmanRiemannSiegelNonintegerDomain hsDomain)
  have h := deBruijnNewmanRiemannSiegel_xio_swapped (s := 1 - s) hOneSub
  rw [riemannXi_one_sub] at h
  convert h using 1 <;> ring

end

end LeanLab.Riemann
