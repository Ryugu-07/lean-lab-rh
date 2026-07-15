import LeanLab.Riemann.BurnolLowerBound
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# Exact Baez-Duarte Gram geometry

This file is the single proof batch preregistered as `CAMPAIGN-20260715-GRAM-01`. It studies the
actual positive-natural kernels in `L2(0,infinity)`. No statement here asserts target closure or the
Riemann hypothesis.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real

namespace LeanLab.Riemann

/-- The exact positive-natural kernel normalized to remove its elementary dilation scale. -/
def baezDuarteNormalizedComplexKernelL2
    (n : baezDuartePositiveNatIndex) : positiveHalfLineComplexL2 :=
  (((Real.sqrt ((n : Nat) : Real) : Real) : Complex)) •
    baezDuarteComplexKernelL2 n

/-- The deliberately sparse integer ratio used in the registered lower-frame candidate. -/
def sparseGramBase : Nat :=
  2 ^ 24

theorem sparseGramBase_pos : 0 < sparseGramBase := by
  norm_num [sparseGramBase]

/-- The positive-natural index `(2^24)^j`. -/
def sparseGramIndex (j : Nat) : baezDuartePositiveNatIndex :=
  ⟨sparseGramBase ^ j, pow_pos sparseGramBase_pos _⟩

theorem baezDuarteComplexKernelL2_coeFn
    (n : baezDuartePositiveNatIndex) :
    baezDuarteComplexKernelL2 n
      =ᵐ[volume.restrict (Ioi (0 : Real))]
        fun x => (fractionalPartKernel (((n : Nat) : Real)⁻¹) x : Complex) := by
  filter_upwards [baezDuarteOfRealLp_coeFn (baezDuarteKernelL2 n),
    baezDuarteKernelL2_coeFn n] with x hcomplex hreal
  exact hcomplex.trans (congrArg Complex.ofReal hreal)

theorem baezDuarteNormalizedComplexKernelL2_coeFn
    (n : baezDuartePositiveNatIndex) :
    baezDuarteNormalizedComplexKernelL2 n
      =ᵐ[volume.restrict (Ioi (0 : Real))]
        fun x => ((Real.sqrt ((n : Nat) : Real) : Real) : Complex) *
          (fractionalPartKernel (((n : Nat) : Real)⁻¹) x : Complex) := by
  refine (Lp.coeFn_smul
    (((Real.sqrt ((n : Nat) : Real) : Real) : Complex))
      (baezDuarteComplexKernelL2 n)).trans ?_
  exact (baezDuarteComplexKernelL2_coeFn n).const_smul _

/-- The physical real Gram integral for two source-aligned positive-natural kernels. -/
def baezDuarteKernelGram
    (m n : baezDuartePositiveNatIndex) : Real :=
  ∫ x : Real,
    fractionalPartKernel (((m : Nat) : Real)⁻¹) x *
      fractionalPartKernel (((n : Nat) : Real)⁻¹) x ∂
        (volume.restrict (Ioi (0 : Real)))

theorem inner_baezDuarteComplexKernelL2_eq_gram
    (m n : baezDuartePositiveNatIndex) :
  ⟪baezDuarteComplexKernelL2 m,
        baezDuarteComplexKernelL2 n⟫_Complex =
      (baezDuarteKernelGram m n : Complex) := by
  rw [L2.inner_def, baezDuarteKernelGram, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [baezDuarteComplexKernelL2_coeFn m,
    baezDuarteComplexKernelL2_coeFn n] with x hm hn
  simp [hm, hn, RCLike.inner_apply, mul_comm]

theorem fractionalPartKernel_le_div
    {a x : Real} (ha : 0 <= a) (hx : 0 < x) :
    fractionalPartKernel a x <= a / x := by
  rw [fractionalPartKernel]
  calc
    Int.fract (a / x) <=
        Int.fract (a / x) + (Int.floor (a / x) : Real) := by
      apply le_add_of_nonneg_right
      exact_mod_cast Int.floor_nonneg.mpr (div_nonneg ha hx.le)
    _ = a / x := Int.fract_add_floor (a / x)

theorem one_half_le_fract_of_mem_three_halves_two
    {y : Real} (hy1 : (3 : Real) / 2 <= y) (hy2 : y < 2) :
    (1 : Real) / 2 <= Int.fract y := by
  rw [<- Int.fract_sub_one y, Int.fract_eq_self.mpr]
  · linarith
  · constructor <;> linarith

theorem one_half_le_baezDuarteKernel_on_interval
    (n : baezDuartePositiveNatIndex) {x : Real}
    (hx1 : 1 / (2 * ((n : Nat) : Real)) < x)
    (hx2 : x < 2 / (3 * ((n : Nat) : Real))) :
    (1 : Real) / 2 <=
      fractionalPartKernel (((n : Nat) : Real)⁻¹) x := by
  have hn : 0 < ((n : Nat) : Real) := by exact_mod_cast n.property
  have hx : 0 < x := by
    exact lt_trans (by positivity : 0 < 1 / (2 * ((n : Nat) : Real))) hx1
  rw [baezDuarteKernel_source_formula]
  apply one_half_le_fract_of_mem_three_halves_two
  · apply le_of_lt
    apply (lt_div_iff₀ (mul_pos hn hx)).2
    have h := (lt_div_iff₀ (by positivity :
      0 < 3 * ((n : Nat) : Real))).mp hx2
    nlinarith
  · apply (div_lt_iff₀ (mul_pos hn hx)).2
    have h := (div_lt_iff₀ (by positivity :
      0 < 2 * ((n : Nat) : Real))).mp hx1
    nlinarith

theorem inner_baezDuarteNormalizedComplexKernelL2_eq_gram
    (m n : baezDuartePositiveNatIndex) :
    ⟪baezDuarteNormalizedComplexKernelL2 m,
        baezDuarteNormalizedComplexKernelL2 n⟫_Complex =
      (Real.sqrt ((m : Nat) : Real) *
        Real.sqrt ((n : Nat) : Real) * baezDuarteKernelGram m n : Real) := by
  rw [baezDuarteNormalizedComplexKernelL2, inner_smul_left,
    baezDuarteNormalizedComplexKernelL2, inner_smul_right,
    inner_baezDuarteComplexKernelL2_eq_gram]
  simp [mul_assoc]

theorem baezDuarteNormalizedKernel_diagonal_lower
    (n : baezDuartePositiveNatIndex) :
    (1 : Real) / 24 <= Real.sqrt ((n : Nat) : Real) *
      Real.sqrt ((n : Nat) : Real) * baezDuarteKernelGram n n := by
  let N : Real := ((n : Nat) : Real)
  let a : Real := 1 / (2 * N)
  let b : Real := 2 / (3 * N)
  let k : Real -> Real := fractionalPartKernel N⁻¹
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast n.property
  have hab : a < b := by
    dsimp [a, b]
    exact (div_lt_div_iff₀ (by positivity : 0 < 2 * N)
      (by positivity : 0 < 3 * N)).2 (by nlinarith)
  have hkMem : MemLp k (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
    dsimp [k, N]
    exact fractionalPartKernel_memLp_two_positiveHalfLine
      (baezDuarte_reciprocal_mem_restricted n).1
      (baezDuarte_reciprocal_mem_restricted n).2
  have hkSq : Integrable (fun x : Real => k x * k x)
      (volume.restrict (Ioi (0 : Real))) := by
    simpa only [pow_two] using
      (memLp_two_iff_integrable_sq hkMem.1).mp hkMem
  have hscaled : Integrable (fun x : Real => N * (k x * k x))
      (volume.restrict (Ioi (0 : Real))) := hkSq.const_mul N
  have hscaledInterval : IntegrableOn (fun x : Real => N * (k x * k x))
      (Ioo a b) volume := by
    exact hscaled.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact lt_trans (by positivity : 0 < a) hx.1) le_rfl)
  have hconstant : IntegrableOn (fun _ : Real => N / 4) (Ioo a b) volume :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hinterval :
      (∫ _ : Real in Ioo a b, N / 4) <=
        ∫ x : Real in Ioo a b, N * (k x * k x) := by
    apply setIntegral_mono_on hconstant hscaledInterval measurableSet_Ioo
    intro x hx
    have hkLower : (1 : Real) / 2 <= k x := by
      apply one_half_le_baezDuarteKernel_on_interval n
      · simpa [a, N] using hx.1
      · simpa [b, N] using hx.2
    have hk0 : 0 <= k x := fractionalPartKernel_nonneg _ _
    have hsq : (1 : Real) / 4 <= k x * k x := by nlinarith
    calc
      N / 4 = N * ((1 : Real) / 4) := by ring
      _ <= N * (k x * k x) := mul_le_mul_of_nonneg_left hsq hN.le
  have hsubset : Ioo a b <= Ioi (0 : Real) := by
    intro x hx
    exact lt_trans (by positivity : 0 < a) hx.1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : Real))]
      fun x : Real => N * (k x * k x) := by
    exact ae_of_all _ fun x => mul_nonneg hN.le (mul_self_nonneg (k x))
  have htoFull :
      (∫ x : Real in Ioo a b, N * (k x * k x)) <=
        ∫ x : Real in Ioi (0 : Real), N * (k x * k x) := by
    exact setIntegral_mono_set hscaled hnonneg (ae_of_all volume hsubset)
  have hconstantValue :
      (∫ _ : Real in Ioo a b, N / 4) = (1 : Real) / 24 := by
    rw [setIntegral_const]
    change (volume (Ioo a b)).toReal * (N / 4) = (1 : Real) / 24
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    dsimp [a, b]
    field_simp
    ring
  rw [Real.mul_self_sqrt hN.le, baezDuarteKernelGram,
    <- integral_const_mul]
  change (1 : Real) / 24 <=
    ∫ x : Real in Ioi (0 : Real), N * (k x * k x)
  rw [<- hconstantValue]
  exact hinterval.trans htoFull

theorem integral_fractionalPartKernel_mul_le
    {a b : Real} (ha : 0 < a) (ha1 : a <= 1)
    (hb : 0 < b) (hb1 : b <= 1) (hab : a <= b) :
    (∫ x : Real in Ioi (0 : Real),
        fractionalPartKernel a x * fractionalPartKernel b x) <=
      a * (2 + Real.log (b / a)) := by
  let f : Real -> Real := fun x =>
    fractionalPartKernel a x * fractionalPartKernel b x
  have hfa := fractionalPartKernel_memLp_two_positiveHalfLine ha ha1
  have hfb := fractionalPartKernel_memLp_two_positiveHalfLine hb hb1
  have hf : Integrable f (volume.restrict (Ioi (0 : Real))) := by
    exact hfa.integrable_mul hfb
  have hleft : IntegrableOn f (Ioc (0 : Real) a) volume :=
    hf.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact hx.1) le_rfl)
  have hrest : IntegrableOn f (Ioi a) volume :=
    hf.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact lt_trans ha hx) le_rfl)
  have hmiddle : IntegrableOn f (Ioc a b) volume :=
    hf.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact lt_trans ha hx.1) le_rfl)
  have htail : IntegrableOn f (Ioi b) volume :=
    hf.mono_measure (Measure.restrict_mono (by
      intro x hx
      exact lt_trans hb hx) le_rfl)
  have hsplitLeft :=
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hrest
  rw [Ioc_union_Ioi_eq_Ioi ha.le] at hsplitLeft
  have hsplitRest :=
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hmiddle htail
  rw [Ioc_union_Ioi_eq_Ioi hab] at hsplitRest
  have hleftBound : (∫ x : Real in Ioc (0 : Real) a, f x) <= a := by
    have hone : IntegrableOn (fun _ : Real => (1 : Real))
        (Ioc (0 : Real) a) volume := integrableOn_const measure_Ioc_lt_top.ne
    calc
      (∫ x : Real in Ioc (0 : Real) a, f x) <=
          ∫ _ : Real in Ioc (0 : Real) a, 1 := by
        apply setIntegral_mono_on hleft hone measurableSet_Ioc
        intro x hx
        dsimp [f]
        have hA0 := fractionalPartKernel_nonneg a x
        have hA1 := fractionalPartKernel_lt_one a x
        have hB0 := fractionalPartKernel_nonneg b x
        have hB1 := fractionalPartKernel_lt_one b x
        nlinarith
      _ = ∫ _ : Real in (0 : Real)..a, 1 := by
        rw [intervalIntegral.integral_of_le ha.le]
      _ = a := by simp
  have hinv : IntervalIntegrable (fun x : Real => a / x) volume a b := by
    have hbase : IntervalIntegrable (fun x : Real => 1 / x) volume a b := by
      simpa only [one_div] using (intervalIntegrable_inv_iff.2
        (Or.inr (notMem_uIcc_of_lt ha hb)))
    simpa only [div_eq_mul_inv, one_mul] using hbase.const_mul a
  have hmiddleBound : (∫ x : Real in Ioc a b, f x) <=
      a * Real.log (b / a) := by
    calc
      (∫ x : Real in Ioc a b, f x) <=
          ∫ x : Real in Ioc a b, a / x := by
        apply setIntegral_mono_on hmiddle hinv.1 measurableSet_Ioc
        intro x hx
        dsimp [f]
        have hx0 : 0 < x := lt_trans ha hx.1
        calc
          fractionalPartKernel a x * fractionalPartKernel b x <=
              fractionalPartKernel a x * 1 :=
            mul_le_mul_of_nonneg_left
              (fractionalPartKernel_lt_one b x).le
              (fractionalPartKernel_nonneg a x)
          _ <= a / x := by
            simpa using fractionalPartKernel_le_div ha.le hx0
      _ = ∫ x : Real in a..b, a / x := by
        rw [intervalIntegral.integral_of_le hab]
      _ = a * Real.log (b / a) := by
        rw [show (fun x : Real => a / x) =
          fun x : Real => a * (1 / x) by funext x; ring,
          intervalIntegral.integral_const_mul,
          integral_one_div_of_pos ha hb]
  have hpow : IntegrableOn (fun x : Real => x ^ (-2 : Real))
      (Ioi b) volume := integrableOn_Ioi_rpow_of_lt (by norm_num) hb
  have htailMajorant : IntegrableOn
      (fun x : Real => a * b * x ^ (-2 : Real)) (Ioi b) volume :=
    hpow.const_mul (a * b)
  have htailBound : (∫ x : Real in Ioi b, f x) <= a := by
    calc
      (∫ x : Real in Ioi b, f x) <=
          ∫ x : Real in Ioi b, a * b * x ^ (-2 : Real) := by
        apply setIntegral_mono_on htail htailMajorant measurableSet_Ioi
        intro x hx
        have hx0 : 0 < x := lt_trans hb hx
        have hA := fractionalPartKernel_le_div ha.le hx0
        have hB := fractionalPartKernel_le_div hb.le hx0
        have hrpow : x ^ (-2 : Real) = (x ^ (2 : Nat))⁻¹ := by
          rw [show (-2 : Real) = -(2 : Real) by norm_num,
            Real.rpow_neg hx0.le]
          exact congrArg Inv.inv (Real.rpow_natCast x 2)
        calc
          f x <= (a / x) * (b / x) := by
            dsimp [f]
            exact mul_le_mul hA hB (fractionalPartKernel_nonneg b x)
              (div_nonneg ha.le hx0.le)
          _ = a * b / x ^ (2 : Nat) := by field_simp [hx0.ne']
          _ = a * b * (x ^ (2 : Nat))⁻¹ := by rw [div_eq_mul_inv]
          _ = a * b * x ^ (-2 : Real) := by rw [hrpow]
      _ = a := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (a := (-2 : Real)) (by norm_num) hb]
        rw [show (-2 : Real) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp
  rw [hsplitLeft, hsplitRest]
  linarith

theorem baezDuarteKernelGram_nonneg
    (m n : baezDuartePositiveNatIndex) :
    0 <= baezDuarteKernelGram m n := by
  rw [baezDuarteKernelGram]
  apply integral_nonneg
  intro x
  exact mul_nonneg
    (fractionalPartKernel_nonneg _ _)
    (fractionalPartKernel_nonneg _ _)

theorem baezDuarteKernelGram_le_of_le
    (m n : baezDuartePositiveNatIndex) (hmn : (m : Nat) <= (n : Nat)) :
    baezDuarteKernelGram m n <=
      (((n : Nat) : Real)⁻¹) *
        (2 + Real.log ((((m : Nat) : Real)⁻¹) /
          (((n : Nat) : Real)⁻¹))) := by
  have hm : 0 < ((m : Nat) : Real) := by exact_mod_cast m.property
  have hn : 0 < ((n : Nat) : Real) := by exact_mod_cast n.property
  have hmOne : (1 : Real) <= ((m : Nat) : Real) := by
    exact_mod_cast m.property
  have hnOne : (1 : Real) <= ((n : Nat) : Real) := by
    exact_mod_cast n.property
  have hrecip := integral_fractionalPartKernel_mul_le
    (inv_pos.mpr hn) (inv_le_one_of_one_le₀ hnOne)
    (inv_pos.mpr hm) (inv_le_one_of_one_le₀ hmOne)
    ((inv_le_inv₀ hn hm).2 (by exact_mod_cast hmn))
  rw [baezDuarteKernelGram]
  simpa only [mul_comm] using hrecip

theorem norm_baezDuarteNormalizedComplexKernelL2_sq_lower
    (n : baezDuartePositiveNatIndex) :
    (1 : Real) / 24 <= ‖baezDuarteNormalizedComplexKernelL2 n‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := Complex),
    inner_baezDuarteNormalizedComplexKernelL2_eq_gram]
  simpa using baezDuarteNormalizedKernel_diagonal_lower n

theorem sparseGramBase_eq_halfBase_sq :
    sparseGramBase = 4096 ^ 2 := by
  norm_num [sparseGramBase]

theorem log_sparseGramBase_le_24 :
    Real.log (sparseGramBase : Real) <= 24 := by
  rw [sparseGramBase]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (16777216 : Real) = (2 : Real) ^ 24 by norm_num,
    Real.log_pow]
  have hlogTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem sqrt_sparseGramIndex (j : Nat) :
    Real.sqrt (((sparseGramIndex j : Nat) : Real)) = (4096 : Real) ^ j := by
  rw [sparseGramIndex]
  simp only [Nat.cast_pow]
  have hp : ((4096 : Real) ^ 2) ^ j = ((4096 : Real) ^ j) ^ 2 :=
    (pow_mul' (4096 : Real) j 2).symm.trans (pow_mul (4096 : Real) j 2)
  rw [show ((sparseGramBase : Nat) : Real) = (4096 : Real) ^ 2 by
    norm_num [sparseGramBase], hp]
  exact Real.sqrt_sq_eq_abs ((4096 : Real) ^ j) |>.trans
    (abs_of_nonneg (pow_nonneg (by norm_num) _))

theorem log_sparseGramBase_pow_le (d : Nat) :
    Real.log ((sparseGramBase : Real) ^ d) <= 24 * d := by
  rw [Real.log_pow]
  have hd : (0 : Real) <= d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left log_sparseGramBase_le_24 hd]

theorem sparseGramIndex_cast (j : Nat) :
    (((sparseGramIndex j : Nat) : Real)) = (sparseGramBase : Real) ^ j := by
  simp [sparseGramIndex]

theorem sparseGram_reciprocal_ratio (i d : Nat) :
    ((((sparseGramIndex i : Nat) : Real))⁻¹ /
        (((sparseGramIndex (i + d) : Nat) : Real))⁻¹) =
      (sparseGramBase : Real) ^ d := by
  have hB : (sparseGramBase : Real) ≠ 0 := by
    exact_mod_cast sparseGramBase_pos.ne'
  rw [sparseGramIndex_cast, sparseGramIndex_cast, pow_add]
  field_simp [pow_ne_zero _ hB]

theorem sparseGram_normalization_scale (i d : Nat) :
    Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
        Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) *
        (((sparseGramIndex (i + d) : Nat) : Real))⁻¹ =
      1 / (4096 : Real) ^ d := by
  have hIndexSq : (((sparseGramIndex (i + d) : Nat) : Real)) =
      (((4096 : Real) ^ i * (4096 : Real) ^ d) ^ 2) := by
    calc
      (((sparseGramIndex (i + d) : Nat) : Real)) =
          Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) ^ 2 := by
        symm
        apply Real.sq_sqrt
        positivity
      _ = ((4096 : Real) ^ (i + d)) ^ 2 := by rw [sqrt_sparseGramIndex]
      _ = (((4096 : Real) ^ i * (4096 : Real) ^ d) ^ 2) := by
        rw [pow_add]
  rw [sqrt_sparseGramIndex, sqrt_sparseGramIndex, hIndexSq, pow_add]
  field_simp [pow_ne_zero _ (by norm_num : (4096 : Real) ≠ 0)]

theorem sparseNormalizedGram_le (i d : Nat) :
    Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
        Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) *
        baezDuarteKernelGram (sparseGramIndex i) (sparseGramIndex (i + d)) <=
      (2 + 24 * d) / (4096 : Real) ^ d := by
  have hIndexLe : (sparseGramIndex i : Nat) <=
      (sparseGramIndex (i + d) : Nat) := by
    exact Nat.pow_le_pow_right sparseGramBase_pos (Nat.le_add_right i d)
  have hGram := baezDuarteKernelGram_le_of_le
    (sparseGramIndex i) (sparseGramIndex (i + d)) hIndexLe
  have hSqrt : 0 <= Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
      Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
          Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) *
          baezDuarteKernelGram (sparseGramIndex i) (sparseGramIndex (i + d)) <=
        (Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
          Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real))) *
          ((((sparseGramIndex (i + d) : Nat) : Real))⁻¹ *
            (2 + Real.log
              ((((sparseGramIndex i : Nat) : Real))⁻¹ /
                (((sparseGramIndex (i + d) : Nat) : Real))⁻¹))) := by
      exact mul_le_mul_of_nonneg_left hGram hSqrt
    _ = (1 / (4096 : Real) ^ d) *
          (2 + Real.log ((sparseGramBase : Real) ^ d)) := by
      rw [sparseGram_reciprocal_ratio]
      rw [<- mul_assoc, sparseGram_normalization_scale]
    _ <= (1 / (4096 : Real) ^ d) * (2 + 24 * d) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [log_sparseGramBase_pow_le d]
      · positivity
    _ = (2 + 24 * d) / (4096 : Real) ^ d := by ring

theorem norm_inner_sparseGram_add_le (i d : Nat) :
    ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex (i + d))⟫_Complex‖ <=
      (2 + 24 * d) / (4096 : Real) ^ d := by
  have hCoeff : 0 <=
      Real.sqrt (((sparseGramIndex i : Nat) : Real)) *
        Real.sqrt (((sparseGramIndex (i + d) : Nat) : Real)) *
        baezDuarteKernelGram (sparseGramIndex i) (sparseGramIndex (i + d)) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (baezDuarteKernelGram_nonneg _ _)
  rw [inner_baezDuarteNormalizedComplexKernelL2_eq_gram,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCoeff]
  exact sparseNormalizedGram_le i d

theorem norm_inner_sparseGram_lt_le {i j : Nat} (hij : i < j) :
    ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ <=
      (2 + 24 * ((j - i : Nat) : Real)) /
        (4096 : Real) ^ (j - i) := by
  simpa [Nat.add_sub_of_le hij.le] using
    norm_inner_sparseGram_add_le i (j - i)

theorem sparseEnvelope_le_geometric (k : Nat) :
    (2 + 24 * ((k + 1 : Nat) : Real)) / (4096 : Real) ^ (k + 1) <=
      (1 / 150 : Real) * (1 / 100 : Real) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hpow : 0 < (4096 : Real) ^ (k + 1) := by positivity
      have hstep :
          (2 + 24 * ((k + 2 : Nat) : Real)) /
              (4096 : Real) ^ (k + 2) <=
            (1 / 100 : Real) *
              ((2 + 24 * ((k + 1 : Nat) : Real)) /
                (4096 : Real) ^ (k + 1)) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        apply (div_le_iff₀ (mul_pos hpow (by norm_num))).2
        field_simp [ne_of_gt hpow]
        ring_nf
        norm_num
        have hk0 : (0 : Real) <= k := by positivity
        nlinarith
      calc
        (2 + 24 * ((k + 2 : Nat) : Real)) /
              (4096 : Real) ^ (k + 2) <=
            (1 / 100 : Real) *
              ((2 + 24 * ((k + 1 : Nat) : Real)) /
                (4096 : Real) ^ (k + 1)) := hstep
        _ <= (1 / 100 : Real) *
              ((1 / 150 : Real) * (1 / 100 : Real) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 150 : Real) * (1 / 100 : Real) ^ (k + 1) := by
          rw [pow_succ]
          ring

theorem norm_inner_sparseGram_ne_le {i j : Nat} (hij : i ≠ j) :
    ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ <=
      (1 / 150 : Real) * (1 / 100 : Real) ^ (Nat.dist i j - 1) := by
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hd : 0 < j - i := Nat.sub_pos_of_lt hij'
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.2 hd.ne')
    have hki : j - i = k + 1 := by omega
    have hupper := norm_inner_sparseGram_lt_le hij'
    rw [hki] at hupper
    rw [Nat.dist_eq_sub_of_le hij'.le, hki]
    simpa [one_div, inv_pow] using hupper.trans (sparseEnvelope_le_geometric k)
  · have hsymm :
        ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ =
          ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)⟫_Complex‖ := by
      exact norm_inner_symm _ _
    rw [hsymm, Nat.dist_comm]
    have hd : 0 < i - j := Nat.sub_pos_of_lt hji'
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.2 hd.ne')
    have hki : i - j = k + 1 := by omega
    have hupper := norm_inner_sparseGram_lt_le hji'
    rw [hki] at hupper
    rw [Nat.dist_eq_sub_of_le hji'.le, hki]
    simpa [one_div, inv_pow] using hupper.trans (sparseEnvelope_le_geometric k)

theorem sum_sparseGeometric_left_le (s : Finset Nat) (i : Nat) :
    (∑ j ∈ s.filter (fun j => j < i),
        (1 / 100 : Real) ^ (Nat.dist i j - 1)) <= 100 / 99 := by
  let t := s.filter (fun j => j < i)
  let phi : Nat -> Nat := fun j => i - j - 1
  have hinj : Set.InjOn phi (t : Set Nat) := by
    intro x hx y hy hxy
    have hx' : x ∈ s ∧ x < i := by simpa [t] using hx
    have hy' : y ∈ s ∧ y < i := by simpa [t] using hy
    have hxi : x < i := hx'.2
    have hyi : y < i := hy'.2
    dsimp [phi] at hxy
    omega
  have hgeom : Summable (fun k : Nat => (1 / 100 : Real) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc
    (∑ j ∈ s.filter (fun j => j < i),
        (1 / 100 : Real) ^ (Nat.dist i j - 1)) =
        ∑ j ∈ t, (1 / 100 : Real) ^ phi j := by
      apply Finset.sum_congr
      · rfl
      · intro j hj
        have hj' : j ∈ s ∧ j < i := by simpa [t] using hj
        have hji : j < i := hj'.2
        rw [Nat.dist_eq_sub_of_le_right hji.le]
    _ = ∑ k ∈ t.image phi, (1 / 100 : Real) ^ k := by
      exact (Finset.sum_image (f := fun k : Nat => (1 / 100 : Real) ^ k) hinj).symm
    _ <= ∑' k : Nat, (1 / 100 : Real) ^ k := by
      exact hgeom.sum_le_tsum _ (fun _ _ => by positivity)
    _ = 100 / 99 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem sum_sparseGeometric_right_le (s : Finset Nat) (i : Nat) :
    (∑ j ∈ s.filter (fun j => i < j),
        (1 / 100 : Real) ^ (Nat.dist i j - 1)) <= 100 / 99 := by
  let t := s.filter (fun j => i < j)
  let phi : Nat -> Nat := fun j => j - i - 1
  have hinj : Set.InjOn phi (t : Set Nat) := by
    intro x hx y hy hxy
    have hx' : x ∈ s ∧ i < x := by simpa [t] using hx
    have hy' : y ∈ s ∧ i < y := by simpa [t] using hy
    have hix : i < x := hx'.2
    have hiy : i < y := hy'.2
    dsimp [phi] at hxy
    omega
  have hgeom : Summable (fun k : Nat => (1 / 100 : Real) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc
    (∑ j ∈ s.filter (fun j => i < j),
        (1 / 100 : Real) ^ (Nat.dist i j - 1)) =
        ∑ j ∈ t, (1 / 100 : Real) ^ phi j := by
      apply Finset.sum_congr
      · rfl
      · intro j hj
        have hj' : j ∈ s ∧ i < j := by simpa [t] using hj
        have hij : i < j := hj'.2
        rw [Nat.dist_eq_sub_of_le hij.le]
    _ = ∑ k ∈ t.image phi, (1 / 100 : Real) ^ k := by
      exact (Finset.sum_image (f := fun k : Nat => (1 / 100 : Real) ^ k) hinj).symm
    _ <= ∑' k : Nat, (1 / 100 : Real) ^ k := by
      exact hgeom.sum_le_tsum _ (fun _ _ => by positivity)
    _ = 100 / 99 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem sum_sparseGeometric_ne_le (s : Finset Nat) (i : Nat) :
    (∑ j ∈ s.filter (fun j => j ≠ i),
        (1 / 100 : Real) ^ (Nat.dist i j - 1)) <= 200 / 99 := by
  have hunion : s.filter (fun j => j ≠ i) =
      s.filter (fun j => j < i) ∪ s.filter (fun j => i < j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hjs, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hjs, hlt⟩
      · exact Or.inr ⟨hjs, hgt⟩
    · rintro (⟨hjs, hlt⟩ | ⟨hjs, hgt⟩)
      · exact ⟨hjs, ne_of_lt hlt⟩
      · exact ⟨hjs, (ne_of_lt hgt).symm⟩
  have hdisjoint : Disjoint (s.filter (fun j => j < i))
      (s.filter (fun j => i < j)) := by
    rw [Finset.disjoint_left]
    intro j hjLeft hjRight
    simp only [Finset.mem_filter] at hjLeft hjRight
    omega
  rw [hunion, Finset.sum_union hdisjoint]
  nlinarith [sum_sparseGeometric_left_le s i,
    sum_sparseGeometric_right_le s i]

theorem sum_norm_inner_sparseGram_offDiag_le
    (s : Finset Nat) (i : Nat) :
    (∑ j ∈ s.filter (fun j => j ≠ i),
      ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖) <=
        (4 : Real) / 297 := by
  calc
    (∑ j ∈ s.filter (fun j => j ≠ i),
      ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖) <=
        ∑ j ∈ s.filter (fun j => j ≠ i),
          (1 / 150 : Real) * (1 / 100 : Real) ^ (Nat.dist i j - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_inner_sparseGram_ne_le (Finset.mem_filter.mp hj).2.symm
    _ = (1 / 150 : Real) *
        (∑ j ∈ s.filter (fun j => j ≠ i),
          (1 / 100 : Real) ^ (Nat.dist i j - 1)) := by
      rw [Finset.mul_sum]
    _ <= (1 / 150 : Real) * (200 / 99) := by
      exact mul_le_mul_of_nonneg_left (sum_sparseGeometric_ne_le s i) (by norm_num)
    _ = (4 : Real) / 297 := by norm_num

def sparseGramCombination (c : Nat →₀ Complex) : positiveHalfLineComplexL2 :=
  ∑ j ∈ c.support,
    c j • baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)

theorem norm_sparseGramCombination_sq_eq (c : Nat →₀ Complex) :
    ‖sparseGramCombination c‖ ^ 2 =
      ∑ i ∈ c.support, ∑ j ∈ c.support,
        (starRingEnd Complex (c i) * c j *
          ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re := by
  rw [norm_sq_eq_re_inner (𝕜 := Complex)]
  simp only [sparseGramCombination, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, map_sum, mul_assoc]
  simp_rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg Complex.re
  ring

theorem sparseGram_diagonal_term_lower (c : Nat →₀ Complex) (i : Nat) :
    (1 / 24 : Real) * ‖c i‖ ^ 2 <=
      (starRingEnd Complex (c i) * c i *
        ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)⟫_Complex).re := by
  have hdiag := norm_baezDuarteNormalizedComplexKernelL2_sq_lower
    (sparseGramIndex i)
  calc
    (1 / 24 : Real) * ‖c i‖ ^ 2 <=
        ‖baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)‖ ^ 2 *
          ‖c i‖ ^ 2 := mul_le_mul_of_nonneg_right hdiag (sq_nonneg _)
    _ = (starRingEnd Complex (c i) * c i *
        ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)⟫_Complex).re := by
      rw [inner_self_eq_norm_sq_to_K, RCLike.conj_mul]
      rw [← RCLike.ofReal_pow, ← RCLike.ofReal_pow,
        ← RCLike.ofReal_mul]
      change ‖baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)‖ ^ 2 *
        ‖c i‖ ^ 2 = ‖c i‖ ^ 2 *
          ‖baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i)‖ ^ 2
      ring

theorem sparseGram_offDiagonal_term_lower
    (c : Nat →₀ Complex) (i j : Nat) :
    -((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) *
        ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ <=
      (starRingEnd Complex (c i) * c j *
        ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
          baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re := by
  let z : Complex := starRingEnd Complex (c i) * c j *
    ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
      baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex
  have hyoung : ‖c i‖ * ‖c j‖ <= (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
  have hinner0 : 0 <=
      ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ := norm_nonneg _
  have hnorm : ‖z‖ <= ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) *
      ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖ := by
    dsimp [z]
    rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
    exact mul_le_mul_of_nonneg_right hyoung hinner0
  have hre : -‖z‖ <= z.re := by
    linarith [Complex.abs_re_le_norm z, neg_le_abs z.re]
  dsimp [z] at hre
  simpa [neg_mul] using (neg_le_neg hnorm).trans hre

def sparseGramInnerNorm (i j : Nat) : Real :=
  ‖⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
      baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex‖

theorem sparseGramInnerNorm_symm (i j : Nat) :
    sparseGramInnerNorm i j = sparseGramInnerNorm j i :=
  norm_inner_symm _ _

theorem sparseGram_offDiagonal_weight_swap (c : Nat →₀ Complex) :
    (∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
        ‖c j‖ ^ 2 * sparseGramInnerNorm i j) =
      ∑ i ∈ c.support, ‖c i‖ ^ 2 *
        (∑ j ∈ c.support.filter (fun j => j ≠ i),
          sparseGramInnerNorm i j) := by
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji, sparseGramInnerNorm_symm]

theorem sparseGram_offDiagonal_young_sum_le (c : Nat →₀ Complex) :
    (∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
        ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j) <=
      (4 / 297 : Real) * ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
  let first : Real := ∑ i ∈ c.support, ‖c i‖ ^ 2 *
    (∑ j ∈ c.support.filter (fun j => j ≠ i), sparseGramInnerNorm i j)
  let second : Real := ∑ i ∈ c.support,
    ∑ j ∈ c.support.filter (fun j => j ≠ i),
      ‖c j‖ ^ 2 * sparseGramInnerNorm i j
  have hexpand :
      (∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
        ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j) =
        (first + second) / 2 := by
    dsimp [first, second]
    simp_rw [div_eq_mul_inv, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul]
    ring_nf
  have hswap : second = first := by
    dsimp [first, second]
    exact sparseGram_offDiagonal_weight_swap c
  have hfirst : first <= (4 / 297 : Real) *
      ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
    dsimp [first]
    calc
      (∑ i ∈ c.support, ‖c i‖ ^ 2 *
        (∑ j ∈ c.support.filter (fun j => j ≠ i), sparseGramInnerNorm i j)) <=
          ∑ i ∈ c.support, ‖c i‖ ^ 2 * (4 / 297 : Real) := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa [sparseGramInnerNorm] using
          sum_norm_inner_sparseGram_offDiag_le c.support i
      _ = (4 / 297 : Real) * ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hexpand, hswap]
  linarith

theorem sparseGram_row_lower (c : Nat →₀ Complex) {i : Nat}
    (hi : i ∈ c.support) :
    (1 / 24 : Real) * ‖c i‖ ^ 2 -
        (∑ j ∈ c.support.filter (fun j => j ≠ i),
          ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j) <=
      ∑ j ∈ c.support,
        (starRingEnd Complex (c i) * c j *
          ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re := by
  let q : Nat -> Real := fun j =>
    (starRingEnd Complex (c i) * c j *
      ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
        baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re
  let a : Nat -> Real := fun j =>
    ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j
  have hdiag : (1 / 24 : Real) * ‖c i‖ ^ 2 <= q i := by
    exact sparseGram_diagonal_term_lower c i
  have hoff : -(∑ j ∈ c.support.filter (fun j => j ≠ i), a j) <=
      ∑ j ∈ c.support.filter (fun j => j ≠ i), q j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    simpa [a, q, sparseGramInnerNorm] using sparseGram_offDiagonal_term_lower c i j
  have hsplit : q i +
      (∑ j ∈ c.support.filter (fun j => j ≠ i), q j) =
        ∑ j ∈ c.support, q j := by
    rw [Finset.filter_ne']
    exact Finset.add_sum_erase c.support q hi
  calc
    (1 / 24 : Real) * ‖c i‖ ^ 2 -
          (∑ j ∈ c.support.filter (fun j => j ≠ i), a j) =
        (1 / 24 : Real) * ‖c i‖ ^ 2 +
          -(∑ j ∈ c.support.filter (fun j => j ≠ i), a j) := by ring
    _ <= q i + (∑ j ∈ c.support.filter (fun j => j ≠ i), q j) :=
      add_le_add hdiag hoff
    _ = ∑ j ∈ c.support, q j := hsplit

theorem sparseGram_double_sum_lower (c : Nat →₀ Complex) :
    (1 / 24 : Real) * (∑ i ∈ c.support, ‖c i‖ ^ 2) -
        (∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
          ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j) <=
      ∑ i ∈ c.support, ∑ j ∈ c.support,
        (starRingEnd Complex (c i) * c j *
          ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re := by
  calc
    (1 / 24 : Real) * (∑ i ∈ c.support, ‖c i‖ ^ 2) -
          (∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
            ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j) =
        ∑ i ∈ c.support,
          ((1 / 24 : Real) * ‖c i‖ ^ 2 -
            (∑ j ∈ c.support.filter (fun j => j ≠ i),
              ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j)) := by
      simp_rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ <= ∑ i ∈ c.support, ∑ j ∈ c.support,
        (starRingEnd Complex (c i) * c j *
          ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex i),
            baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j)⟫_Complex).re := by
      apply Finset.sum_le_sum
      intro i hi
      exact sparseGram_row_lower c hi

/-- The registered explicit lower-frame bound for the sparse normalized Baez-Duarte family. -/
theorem sparseGram_lower_frame_bound (c : Nat →₀ Complex) :
    (1 / 40 : Real) * (∑ i ∈ c.support, ‖c i‖ ^ 2) <=
      ‖sparseGramCombination c‖ ^ 2 := by
  let coeffSq : Real := ∑ i ∈ c.support, ‖c i‖ ^ 2
  let young : Real :=
    ∑ i ∈ c.support, ∑ j ∈ c.support.filter (fun j => j ≠ i),
      ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * sparseGramInnerNorm i j
  have hcoeff0 : 0 <= coeffSq := by
    dsimp [coeffSq]
    positivity
  have hyoung : young <= (4 / 297 : Real) * coeffSq := by
    dsimp [young, coeffSq]
    exact sparseGram_offDiagonal_young_sum_le c
  have hdouble : (1 / 24 : Real) * coeffSq - young <=
      ‖sparseGramCombination c‖ ^ 2 := by
    rw [norm_sparseGramCombination_sq_eq]
    dsimp [coeffSq, young]
    exact sparseGram_double_sum_lower c
  have hconstant : (1 / 40 : Real) <= 1 / 24 - 4 / 297 := by norm_num
  have hscaled := mul_le_mul_of_nonneg_right hconstant hcoeff0
  change (1 / 40 : Real) * coeffSq <= ‖sparseGramCombination c‖ ^ 2
  calc
    (1 / 40 : Real) * coeffSq <=
        (1 / 24 - 4 / 297 : Real) * coeffSq := hscaled
    _ <= (1 / 24 : Real) * coeffSq - young := by nlinarith
    _ <= ‖sparseGramCombination c‖ ^ 2 := hdouble

/-! The following typed witness records why finite Gram positivity alone contains no information
about a separately chosen target. -/

def finiteGramWitnessVector : Fin 1 -> EuclideanSpace Real (Fin 2) :=
  fun _ => EuclideanSpace.single 0 1

def finiteGramWitnessTarget : EuclideanSpace Real (Fin 2) :=
  EuclideanSpace.single 1 1

theorem finiteGramWitness_linearIndependent :
    LinearIndependent Real finiteGramWitnessVector := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  fin_cases i
  have hcoord := congrArg (fun v : EuclideanSpace Real (Fin 2) => v 0) hc
  simpa [finiteGramWitnessVector] using hcoord

theorem finiteGramWitness_posDef :
    (Matrix.gram Real finiteGramWitnessVector).PosDef :=
  Matrix.posDef_gram_of_linearIndependent finiteGramWitness_linearIndependent

theorem finiteGramWitness_target_orthogonal (i : Fin 1) :
    ⟪finiteGramWitnessVector i, finiteGramWitnessTarget⟫_Real = 0 := by
  fin_cases i
  simp [finiteGramWitnessVector, finiteGramWitnessTarget,
    EuclideanSpace.inner_single_left]

theorem norm_finiteGramWitnessTarget :
    ‖finiteGramWitnessTarget‖ = 1 := by
  simp [finiteGramWitnessTarget]

end LeanLab.Riemann
