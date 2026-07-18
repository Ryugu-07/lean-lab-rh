import LeanLab.Riemann.DeBruijnNewmanTableRowCertificates
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option linter.style.header false

/-!
# Polymath effective Riemann--Siegel normalization

This module formalizes the source normalization from Polymath Theorem 1.3 and the exact
nonvanishing consumer from Corollary 1.4. It does not assert the effective approximation or any
numerical error bound.
-/

open Complex
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The argument of `M_t` used to normalize `H_t(x+iy)`. -/
def deBruijnNewmanPolymathBArgument (x y : ℝ) : ℂ :=
  (((1 + y : ℝ) : ℂ) - (x : ℂ) * I) / 2

/-- The reflected argument in the numerator of the source phase `gamma`. -/
def deBruijnNewmanPolymathReflectedArgument (x y : ℝ) : ℂ :=
  (((1 - y : ℝ) : ℂ) + (x : ℂ) * I) / 2

/-- The upper-half-plane companion used in the source correction `kappa`. -/
def deBruijnNewmanPolymathUpperArgument (x y : ℝ) : ℂ :=
  (((1 + y : ℝ) : ℂ) + (x : ℂ) * I) / 2

/-- The source branch `log M_0`, equation (logM) in Polymath. -/
def deBruijnNewmanPolymathLogM0 (s : ℂ) : ℂ :=
  Complex.log s + Complex.log (s - 1) -
      s / 2 * (Real.log Real.pi : ℂ) +
    Complex.log (((Real.sqrt (2 * Real.pi) / 16 : ℝ) : ℂ)) +
      (s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2

/-- The explicit logarithmic derivative `alpha` in the first line of equation (alpha-form). -/
def deBruijnNewmanPolymathAlpha (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
    Complex.log (s / 2) / 2 - 1 / (2 * s)

/-- The Stirling normalizer `M_0`, equation (M-def) in Polymath. -/
def deBruijnNewmanPolymathM0 (s : ℂ) : ℂ :=
  (1 / 8 : ℂ) * (s * (s - 1) / 2) *
      Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) *
    (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)

/-- The deformed Stirling normalizer `M_t`, equation (Mt-def) in Polymath. -/
def deBruijnNewmanPolymathM (t : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (((t : ℂ) / 4) * deBruijnNewmanPolymathAlpha s ^ 2) *
    deBruijnNewmanPolymathM0 s

/-- The nowhere-zero normalizer `B_t(x+iy)`, equation (bo-def) in Polymath. -/
def deBruijnNewmanPolymathB (t x y : ℝ) : ℂ :=
  deBruijnNewmanPolymathM t (deBruijnNewmanPolymathBArgument x y)

/-- The coefficient `b_n^t = exp((t/4) log^2 n)`. -/
def deBruijnNewmanPolymathBWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (t / 4 * Real.log n ^ 2)

/-- The Riemann--Siegel cutoff from equation (N-def-main). -/
def deBruijnNewmanPolymathN (t x : ℝ) : ℕ :=
  ⌊Real.sqrt (x / (4 * Real.pi) + t / 16)⌋₊

/-- The source phase ratio `gamma`. -/
def deBruijnNewmanPolymathGamma (t x y : ℝ) : ℂ :=
  deBruijnNewmanPolymathM t (deBruijnNewmanPolymathReflectedArgument x y) /
    deBruijnNewmanPolymathB t x y

/-- The shifted Dirichlet exponent `s_*`. -/
def deBruijnNewmanPolymathSStar (t x y : ℝ) : ℂ :=
  deBruijnNewmanPolymathBArgument x y +
    ((t : ℂ) / 2) *
      deBruijnNewmanPolymathAlpha (deBruijnNewmanPolymathBArgument x y)

/-- The correction exponent `kappa`. -/
def deBruijnNewmanPolymathKappa (t x y : ℝ) : ℂ :=
  ((t : ℂ) / 2) *
    (deBruijnNewmanPolymathAlpha (deBruijnNewmanPolymathReflectedArgument x y) -
      deBruijnNewmanPolymathAlpha (deBruijnNewmanPolymathUpperArgument x y))

/-- A positive natural number raised to a complex exponent in the source convention. -/
def deBruijnNewmanPolymathNatPow (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log n : ℂ))

/-- The finite Dirichlet polynomial `f_t`, equation (ft-def) in Polymath. -/
def deBruijnNewmanPolymathF (t x y : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 (deBruijnNewmanPolymathN t x),
      (deBruijnNewmanPolymathBWeight t n : ℂ) /
        deBruijnNewmanPolymathNatPow n (deBruijnNewmanPolymathSStar t x y)) +
    deBruijnNewmanPolymathGamma t x y *
      ∑ n ∈ Finset.Icc 1 (deBruijnNewmanPolymathN t x),
        (deBruijnNewmanPolymathNatPow n (y : ℂ) *
            (deBruijnNewmanPolymathBWeight t n : ℂ)) /
          deBruijnNewmanPolymathNatPow n
            (starRingEnd ℂ (deBruijnNewmanPolymathSStar t x y) +
              deBruijnNewmanPolymathKappa t x y)

/-- The parameter region in Polymath Theorem 1.3. -/
def deBruijnNewmanPolymathEffectiveRegion (t x y : ℝ) : Prop :=
  0 < t ∧ t ≤ 1 / 2 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 200 ≤ x

/-- The explicit upper bound for `e_A+e_B` in Polymath Theorem 1.3. -/
def deBruijnNewmanPolymathEABUpper (t x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (deBruijnNewmanPolymathN t x),
    (1 + ‖deBruijnNewmanPolymathGamma t x y‖ *
          (deBruijnNewmanPolymathN t x : ℝ) ^
            ‖deBruijnNewmanPolymathKappa t x y‖ *
          (n : ℝ) ^ y) *
      deBruijnNewmanPolymathBWeight t n /
        (n : ℝ) ^ (deBruijnNewmanPolymathSStar t x y).re *
      (Real.exp
          ((t ^ 2 / 16 *
                Real.log (x / (4 * Real.pi * (n : ℝ) ^ 2)) ^ 2 + 313 / 500) /
            (x - 333 / 50)) - 1)

/-- The explicit upper bound for `e_{C,0}` in Polymath Theorem 1.3. -/
def deBruijnNewmanPolymathEC0Upper (t x y : ℝ) : ℝ :=
  (x / (4 * Real.pi)) ^ (-(1 + y) / 4) *
    Real.exp
      (-t / 16 * Real.log (x / (4 * Real.pi)) ^ 2 +
        (31 / 25) * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) /
          ((deBruijnNewmanPolymathN t x : ℝ) - 1 / 8) +
        (3 * ‖((Real.log (x / (4 * Real.pi)) : ℝ) : ℂ) +
              (Real.pi / 2 : ℝ) * I‖ + 261 / 25) /
          (x - 12))

/-- The explicit total error exposed to proof-producing numerical certificates. -/
def deBruijnNewmanPolymathEffectiveUpperError (t x y : ℝ) : ℝ :=
  deBruijnNewmanPolymathEABUpper t x y +
    deBruijnNewmanPolymathEC0Upper t x y

/-- The deterministic conclusion of the effective Riemann--Siegel theorem before it is proved. -/
def deBruijnNewmanPolymathExplicitApproximation (t x y : ℝ) : Prop :=
  ‖deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) /
        deBruijnNewmanPolymathB t x y -
      deBruijnNewmanPolymathF t x y‖ ≤
    deBruijnNewmanPolymathEffectiveUpperError t x y

/-- A kernel-checkable pointwise certificate using the theorem's displayed upper bounds. -/
def deBruijnNewmanPolymathExplicitCertificate (t x y : ℝ) : Prop :=
  deBruijnNewmanPolymathExplicitApproximation t x y ∧
    deBruijnNewmanPolymathEffectiveUpperError t x y <
      ‖deBruijnNewmanPolymathF t x y‖

/-- The source branch has the advertised logarithmic derivative on the strict lower half-plane. -/
theorem deBruijnNewmanPolymathLogM0_hasDerivAt
    {s : ℂ} (hs : s.im < 0) :
    HasDerivAt deBruijnNewmanPolymathLogM0
      (deBruijnNewmanPolymathAlpha s) s := by
  have hsSlit : s ∈ Complex.slitPlane := Or.inr hs.ne
  have hsSubSlit : s - 1 ∈ Complex.slitPlane := by
    right
    simpa using hs.ne
  have hsHalfSlit : s / 2 ∈ Complex.slitPlane := by
    right
    have him : (s / 2).im = s.im / 2 := by simp
    rw [him]
    exact div_ne_zero hs.ne (by norm_num)
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hlogS := Complex.hasDerivAt_log hsSlit
  have hlogSub := ((hasDerivAt_id s).sub_const 1).clog hsSubSlit
  have hlogHalf := hhalf.clog hsHalfSlit
  have hpi := hhalf.mul_const (Real.log Real.pi : ℂ)
  have hconst : HasDerivAt
      (fun _ : ℂ => Complex.log (((Real.sqrt (2 * Real.pi) / 16 : ℝ) : ℂ))) 0 s :=
    hasDerivAt_const s _
  have hlinear := hhalf.sub_const (1 / 2 : ℂ)
  have hproduct := hlinear.mul hlogHalf
  have h := ((((hlogS.add hlogSub).sub hpi).add hconst).add hproduct).sub hhalf
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hsSlit
  have hs1 : s - 1 ≠ 0 := Complex.slitPlane_ne_zero hsSubSlit
  have hcoeff :
      s⁻¹ + 1 / (s - 1) - 1 / 2 * (Real.log Real.pi : ℂ) + 0 +
            (1 / 2 * Complex.log (s / 2) +
              (s / 2 - 1 / 2) * (1 / 2 / (s / 2))) - 1 / 2 =
        deBruijnNewmanPolymathAlpha s := by
    simp only [deBruijnNewmanPolymathAlpha]
    field_simp [hs0, hs1]
    ring
  simp only [id_eq] at h
  rw [hcoeff] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  rfl

/-- The two displayed formulas in equation (alpha-form) agree on the lower half-plane. -/
theorem deBruijnNewmanPolymathAlpha_eq_compact
    {s : ℂ} (hs : s.im < 0) :
    deBruijnNewmanPolymathAlpha s =
      1 / (2 * s) + 1 / (s - 1) +
        Complex.log (s / (2 * Real.pi)) / 2 := by
  have hs0 : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hhalf0 : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
  have hpi : 0 < (1 / Real.pi : ℝ) := one_div_pos.mpr Real.pi_pos
  have hlog := Complex.log_ofReal_mul hpi hhalf0
  have harg : ((1 / Real.pi : ℝ) : ℂ) * (s / 2) = s / (2 * Real.pi) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg] at hlog
  have hlogInv : Real.log (1 / Real.pi) = -Real.log Real.pi := by
    rw [one_div, Real.log_inv]
  rw [hlogInv] at hlog
  push_cast at hlog
  rw [deBruijnNewmanPolymathAlpha, hlog]
  field_simp [hs0]
  ring

/-- The explicit `log M_0` branch exponentiates to the source normalizer on the lower half-plane. -/
theorem deBruijnNewmanPolymath_exp_logM0_eq_M0
    {s : ℂ} (hs : s.im < 0) :
    Complex.exp (deBruijnNewmanPolymathLogM0 s) =
      deBruijnNewmanPolymathM0 s := by
  have hs0 : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hcpos : 0 < Real.sqrt (2 * Real.pi) / 16 := by positivity
  have hc : (((Real.sqrt (2 * Real.pi) / 16 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcpos.ne'
  simp only [deBruijnNewmanPolymathLogM0, deBruijnNewmanPolymathM0,
    Complex.exp_add, Complex.exp_sub, Complex.exp_log hs0, Complex.exp_log hs1,
    Complex.exp_log hc]
  field_simp [Complex.exp_ne_zero]
  rw [← Complex.exp_add]
  simp
  ring

/-- `M_0` is nonzero away from its two explicit polynomial zeros. -/
theorem deBruijnNewmanPolymathM0_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deBruijnNewmanPolymathM0 s ≠ 0 := by
  have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsqrt : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr <| ne_of_gt <| Real.sqrt_pos.2 <| by positivity
  simp only [deBruijnNewmanPolymathM0]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (div_ne_zero (mul_ne_zero hs0 hsSub) (by norm_num)))
        (Complex.exp_ne_zero _))
      hsqrt)
    (Complex.exp_ne_zero _)

/-- The deformed normalizer has no new zeros. -/
theorem deBruijnNewmanPolymathM_ne_zero
    {t : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deBruijnNewmanPolymathM t s ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (deBruijnNewmanPolymathM0_ne_zero hs0 hs1)

/-- `B_t(x+iy)` is nonzero throughout the positive-`x` source region. -/
theorem deBruijnNewmanPolymathB_ne_zero
    {t x y : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathB t x y ≠ 0 := by
  have hs0 : deBruijnNewmanPolymathBArgument x y ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [deBruijnNewmanPolymathBArgument] at him
    linarith
  have hs1 : deBruijnNewmanPolymathBArgument x y ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [deBruijnNewmanPolymathBArgument] at him
    linarith
  exact deBruijnNewmanPolymathM_ne_zero hs0 hs1

/-- The exact normalized approximation proposition before inserting explicit source errors. -/
def deBruijnNewmanPolymathEffectiveApproximation
    (t x y eA eB eC0 : ℝ) : Prop :=
  0 ≤ eA ∧ 0 ≤ eB ∧ 0 ≤ eC0 ∧
    ‖deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) /
        deBruijnNewmanPolymathB t x y -
      deBruijnNewmanPolymathF t x y‖ ≤ eA + eB + eC0

/-- A pointwise proof object for the nonvanishing test in Polymath Corollary 1.4. -/
def deBruijnNewmanPolymathEffectiveCertificate (t x y : ℝ) : Prop :=
  ∃ eA eB eC0 : ℝ,
    deBruijnNewmanPolymathEffectiveApproximation t x y eA eB eC0 ∧
      eA + eB + eC0 < ‖deBruijnNewmanPolymathF t x y‖

/-- Polymath Corollary 1.4 in the exact project normalization. -/
theorem deBruijnNewmanH_ne_zero_of_polymathEffectiveApproximation
    {t x y eA eB eC0 : ℝ}
    (hx : 0 < x)
    (happrox : deBruijnNewmanPolymathEffectiveApproximation t x y eA eB eC0)
    (hstrict : eA + eB + eC0 < ‖deBruijnNewmanPolymathF t x y‖) :
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  have hBne : deBruijnNewmanPolymathB t x y ≠ 0 :=
    deBruijnNewmanPolymathB_ne_zero (t := t) (y := y) hx
  intro hzero
  have hbound := happrox.2.2.2
  have hdivZeroIff :
      deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) /
          deBruijnNewmanPolymathB t x y = 0 ↔
        deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) = 0 := by
    rw [div_eq_zero_iff]
    simp only [hBne, or_false]
  have hquotZero :
      deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) /
          deBruijnNewmanPolymathB t x y = 0 :=
    hdivZeroIff.mpr hzero
  rw [hquotZero, zero_sub, norm_neg] at hbound
  exact (not_lt_of_ge hbound) hstrict

/-- The second-row final region lies inside the parameter region of Theorem 1.3. -/
theorem deBruijnNewmanPolymath_table_row_final_mem_effectiveRegion
    {x y : ℝ}
    (hx : ((5 : ℝ) * 10 ^ 12 + 194858) +
        Real.sqrt (1 - ((16733 : ℝ) / 100000) ^ 2) ≤ x)
    (hy0 : ((16733 : ℝ) / 100000) ≤ y)
    (hy1 : y ≤ Real.sqrt (1 - 2 * ((93 : ℝ) / 500))) :
    deBruijnNewmanPolymathEffectiveRegion ((93 : ℝ) / 500) x y := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have hy0pos : 0 < ((16733 : ℝ) / 100000) := by norm_num
    linarith
  · have hrad : 0 ≤ 1 - 2 * ((93 : ℝ) / 500) := by norm_num
    have hsquare := Real.sq_sqrt hrad
    have hroot := Real.sqrt_nonneg (1 - 2 * ((93 : ℝ) / 500))
    nlinarith
  · have hroot := Real.sqrt_nonneg (1 - ((16733 : ℝ) / 100000) ^ 2)
    have hX : 200 < (5 : ℝ) * 10 ^ 12 + 194858 := by norm_num
    linarith

/-- The displayed Theorem 1.3 upper error implies pointwise nonvanishing when it is below
`|f_t|`. -/
theorem deBruijnNewmanH_ne_zero_of_polymathExplicitCertificate
    {t x y : ℝ}
    (hx : 0 < x)
    (hcert : deBruijnNewmanPolymathExplicitCertificate t x y) :
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  have hBne : deBruijnNewmanPolymathB t x y ≠ 0 :=
    deBruijnNewmanPolymathB_ne_zero (t := t) (y := y) hx
  intro hzero
  have hbound := hcert.1
  have hdivZeroIff :
      deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) /
          deBruijnNewmanPolymathB t x y = 0 ↔
        deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) = 0 := by
    rw [div_eq_zero_iff]
    simp only [hBne, or_false]
  have hquotZero := hdivZeroIff.mpr hzero
  simp only [deBruijnNewmanPolymathExplicitApproximation] at hbound
  rw [hquotZero, zero_sub, norm_neg] at hbound
  exact (not_lt_of_ge hbound) hcert.2

/-- Explicit pointwise Theorem 1.3 certificates imply the full unbounded final region. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree_of_explicitCertificates
    {t0 X y0 : ℝ}
    (hX : 0 < X + Real.sqrt (1 - y0 ^ 2))
    (hcert : ∀ x y : ℝ,
      X + Real.sqrt (1 - y0 ^ 2) ≤ x →
      y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
      deBruijnNewmanPolymathExplicitCertificate t0 x y) :
    deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0 := by
  intro x y hx hy0 hy1
  exact deBruijnNewmanH_ne_zero_of_polymathExplicitCertificate
    (hX.trans_le hx) (hcert x y hx hy0 hy1)

/-- Exact second-row final-region consumer using only the displayed Theorem 1.3 upper error. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree_table_row_of_explicitCertificates
    (hcert : ∀ x y : ℝ,
      ((5 : ℝ) * 10 ^ 12 + 194858) +
          Real.sqrt (1 - ((16733 : ℝ) / 100000) ^ 2) ≤ x →
      ((16733 : ℝ) / 100000) ≤ y →
      y ≤ Real.sqrt (1 - 2 * ((93 : ℝ) / 500)) →
      deBruijnNewmanPolymathExplicitCertificate ((93 : ℝ) / 500) x y) :
    deBruijnNewmanPolymathFinalRegionZeroFree
      ((93 : ℝ) / 500) ((5 : ℝ) * 10 ^ 12 + 194858) ((16733 : ℝ) / 100000) := by
  apply deBruijnNewmanPolymathFinalRegionZeroFree_of_explicitCertificates
  · have hsqrt := Real.sqrt_nonneg (1 - ((16733 : ℝ) / 100000) ^ 2)
    norm_num at hsqrt ⊢
    linarith
  · exact hcert

/-- Pointwise effective certificates imply the full unbounded final region. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree_of_effectiveCertificates
    {t0 X y0 : ℝ}
    (hX : 0 < X + Real.sqrt (1 - y0 ^ 2))
    (hcert : ∀ x y : ℝ,
      X + Real.sqrt (1 - y0 ^ 2) ≤ x →
      y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
      deBruijnNewmanPolymathEffectiveCertificate t0 x y) :
    deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0 := by
  intro x y hx hy0 hy1
  obtain ⟨eA, eB, eC0, happrox, hstrict⟩ := hcert x y hx hy0 hy1
  exact deBruijnNewmanH_ne_zero_of_polymathEffectiveApproximation
    (hX.trans_le hx) happrox hstrict

/-- Exact second-row final-region consumer for future proof-producing certificates. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree_table_row_of_effectiveCertificates
    (hcert : ∀ x y : ℝ,
      ((5 : ℝ) * 10 ^ 12 + 194858) +
          Real.sqrt (1 - ((16733 : ℝ) / 100000) ^ 2) ≤ x →
      ((16733 : ℝ) / 100000) ≤ y →
      y ≤ Real.sqrt (1 - 2 * ((93 : ℝ) / 500)) →
      deBruijnNewmanPolymathEffectiveCertificate ((93 : ℝ) / 500) x y) :
    deBruijnNewmanPolymathFinalRegionZeroFree
      ((93 : ℝ) / 500) ((5 : ℝ) * 10 ^ 12 + 194858) ((16733 : ℝ) / 100000) := by
  apply deBruijnNewmanPolymathFinalRegionZeroFree_of_effectiveCertificates
  · have hsqrt := Real.sqrt_nonneg (1 - ((16733 : ℝ) / 100000) ^ 2)
    norm_num at hsqrt ⊢
    linarith
  · exact hcert

end

end LeanLab.Riemann
