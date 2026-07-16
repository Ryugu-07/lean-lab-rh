import LeanLab.Riemann.DeBruijnNewmanForward
import Mathlib.Analysis.Calculus.Deriv.Star

set_option linter.style.header false

/-!
# De Bruijn strip contraction and the classical half-time upper bound

This module proves the quantitative contraction of the zero strip for the source-normalized
de Bruijn-Newman heat family on `0 <= t <= 1/2`, and hence proves that every zero at time
`t = 1/2` is real.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

/-- The source-normalized heat family is real entire. -/
theorem deBruijnNewmanH_conj (t : ℝ) (z : ℂ) :
    deBruijnNewmanH t (conj z) = conj (deBruijnNewmanH t z) := by
  rw [deBruijnNewmanH, deBruijnNewmanH, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  rw [show conj z * (u : ℂ) = conj (z * (u : ℂ)) by simp,
    Complex.cos_conj]
  rw [map_mul]
  congr 1
  exact (conj_ofReal _).symm

private theorem iteratedDeriv_conj
    {F : ℂ → ℂ} (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n F (conj z) = conj (iteratedDeriv n F z) := by
  induction n generalizing z with
  | zero => simpa only [iteratedDeriv_zero] using hconj z
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have hfun : (conj ∘ iteratedDeriv n F ∘ conj) = iteratedDeriv n F := by
        funext w
        simpa [Function.comp_apply] using (hn (conj w)).symm
      have hderiv :
          (conj ∘ deriv (iteratedDeriv n F) ∘ conj) = deriv (iteratedDeriv n F) := by
        rw [← deriv_conj_conj, hfun]
      have := congrFun hderiv (conj z)
      simpa [Function.comp_apply] using this.symm

theorem analyticOrderNatAt_conj_eq
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z)) (z : ℂ) :
    analyticOrderNatAt F (conj z) = analyticOrderNatAt F z := by
  let n := analyticOrderNatAt F z
  have htop : ∀ w : ℂ, analyticOrderAt F w ≠ ⊤ :=
    Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero hF hnot
  have hcast : (n : ℕ∞) = analyticOrderAt F z := by
    simpa only [n] using Nat.cast_analyticOrderNatAt (htop z)
  have horder : analyticOrderAt F z = (n : ℕ∞) := hcast.symm
  have hcharacter :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf := hF.analyticAt z)).mp horder
  have hcharacter_conj :
      (∀ k < n, iteratedDeriv k F (conj z) = 0) ∧
        iteratedDeriv n F (conj z) ≠ 0 := by
    constructor
    · intro k hk
      rw [iteratedDeriv_conj hconj]
      simp [hcharacter.1 k hk]
    · rw [iteratedDeriv_conj hconj]
      simpa using hcharacter.2
  have horder_conj : analyticOrderAt F (conj z) = (n : ℕ∞) :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (hf := hF.analyticAt (conj z))).mpr hcharacter_conj
  have hcast_conj :
      ((analyticOrderNatAt F (conj z) : ℕ) : ℕ∞) = analyticOrderAt F (conj z) :=
    Nat.cast_analyticOrderNatAt (htop (conj z))
  rw [horder_conj] at hcast_conj
  exact_mod_cast hcast_conj

private theorem divisor_conj_eq
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z)) (z : ℂ) :
    MeromorphicOn.divisor F (Set.univ : Set ℂ) (conj z) =
      MeromorphicOn.divisor F (Set.univ : Set ℂ) z := by
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hF,
    Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hF,
    analyticOrderNatAt_conj_eq hF hnot hconj]

private def divisorZeroIndexConj
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) := by
  let hdiv := divisor_conj_eq hF hnot hconj p.1.1
  refine ⟨⟨conj p.1.1, Fin.cast (congrArg Int.toNat hdiv).symm p.1.2⟩, ?_⟩
  simp

@[simp]
private theorem divisorZeroIndexConj_val
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    Complex.Hadamard.divisorZeroIndex₀_val (divisorZeroIndexConj hF hnot hconj p) =
      conj (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rfl

private theorem divisorZeroIndexConj_involutive
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z)) :
    Function.Involutive (divisorZeroIndexConj hF hnot hconj) := by
  intro p
  apply Subtype.ext
  apply Sigma.ext
  · simp [divisorZeroIndexConj]
  · rw [Fin.heq_ext_iff]
    · simp [divisorZeroIndexConj]
    · simp [divisorZeroIndexConj]

private def divisorZeroIndexConjEquiv
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z)) :
    Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ≃
      Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) where
  toFun := divisorZeroIndexConj hF hnot hconj
  invFun := divisorZeroIndexConj hF hnot hconj
  left_inv := divisorZeroIndexConj_involutive hF hnot hconj
  right_inv := divisorZeroIndexConj_involutive hF hnot hconj

@[simp]
private theorem divisorZeroIndexConjEquiv_val
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hnot : ∃ z : ℂ, F z ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    Complex.Hadamard.divisorZeroIndex₀_val
        (divisorZeroIndexConjEquiv hF hnot hconj p) =
      conj (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  rfl

theorem norm_weierstrassFactor_pair_sub_I_lt_add_I
    {r z : ℂ} (hr0 : r ≠ 0) {muSq a : ℝ}
    (hrstrip : r.im ^ 2 ≤ muSq) (ha : 0 < a) (hz : 0 < z.im)
    (hzstrip : muSq - a ^ 2 < z.im ^ 2) :
    ‖Complex.weierstrassFactor 1 ((z - I * (a : ℂ)) / r) *
        Complex.weierstrassFactor 1 ((z - I * (a : ℂ)) / conj r)‖ <
      ‖Complex.weierstrassFactor 1 ((z + I * (a : ℂ)) / r) *
        Complex.weierstrassFactor 1 ((z + I * (a : ℂ)) / conj r)‖ := by
  let wm : ℂ := z - I * (a : ℂ)
  let wp : ℂ := z + I * (a : ℂ)
  have hrnorm : 0 < Complex.normSq r := Complex.normSq_pos.mpr hr0
  have hrc0 : conj r ≠ 0 := by simpa using hr0
  have him : r.im ^ 2 < z.im ^ 2 + a ^ 2 := by nlinarith
  have hnum :
      Complex.normSq (r - wm) * Complex.normSq (conj r - wm) <
        Complex.normSq (r - wp) * Complex.normSq (conj r - wp) := by
    have hinner :
        0 < (r.re - z.re) ^ 2 + z.im ^ 2 + a ^ 2 - r.im ^ 2 := by
      nlinarith [sq_nonneg (r.re - z.re)]
    have hgap :
        0 < 8 * a * z.im *
          ((r.re - z.re) ^ 2 + z.im ^ 2 + a ^ 2 - r.im ^ 2) := by
      positivity
    simp only [wm, wp, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, zero_mul, one_mul, zero_sub]
    ring_nf
    nlinarith
  have hsq :
      Complex.normSq (1 - wm / r) * Complex.normSq (1 - wm / conj r) <
        Complex.normSq (1 - wp / r) * Complex.normSq (1 - wp / conj r) := by
    rw [show 1 - wm / r = (r - wm) / r by field_simp [hr0],
      show 1 - wm / conj r = (conj r - wm) / conj r by field_simp [hrc0],
      show 1 - wp / r = (r - wp) / r by field_simp [hr0],
      show 1 - wp / conj r = (conj r - wp) / conj r by field_simp [hrc0],
      Complex.normSq_div, Complex.normSq_div, Complex.normSq_div, Complex.normSq_div,
      Complex.normSq_conj]
    calc
      Complex.normSq (r - wm) / Complex.normSq r *
          (Complex.normSq (conj r - wm) / Complex.normSq r) =
        (Complex.normSq (r - wm) * Complex.normSq (conj r - wm)) /
          (Complex.normSq r * Complex.normSq r) := by ring
      _ < (Complex.normSq (r - wp) * Complex.normSq (conj r - wp)) /
          (Complex.normSq r * Complex.normSq r) :=
        div_lt_div_of_pos_right hnum (mul_pos hrnorm hrnorm)
      _ = Complex.normSq (r - wp) / Complex.normSq r *
          (Complex.normSq (conj r - wp) / Complex.normSq r) := by ring
  have hlinear :
      ‖1 - wm / r‖ * ‖1 - wm / conj r‖ <
        ‖1 - wp / r‖ * ‖1 - wp / conj r‖ := by
    simp only [Complex.normSq_eq_norm_sq] at hsq
    have hleft : 0 ≤ ‖1 - wm / r‖ * ‖1 - wm / conj r‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hright : 0 ≤ ‖1 - wp / r‖ * ‖1 - wp / conj r‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hleft_sq :
        (‖1 - wm / r‖ * ‖1 - wm / conj r‖) ^ 2 =
          ‖1 - wm / r‖ ^ 2 * ‖1 - wm / conj r‖ ^ 2 := by ring
    have hright_sq :
        (‖1 - wp / r‖ * ‖1 - wp / conj r‖) ^ 2 =
          ‖1 - wp / r‖ ^ 2 * ‖1 - wp / conj r‖ ^ 2 := by ring
    rw [← hleft_sq, ← hright_sq] at hsq
    nlinarith
  have hexp :
      ‖Complex.exp (Complex.partialLogSum 1 (wm / r))‖ *
          ‖Complex.exp (Complex.partialLogSum 1 (wm / conj r))‖ =
        ‖Complex.exp (Complex.partialLogSum 1 (wp / r))‖ *
          ‖Complex.exp (Complex.partialLogSum 1 (wp / conj r))‖ := by
    simp only [Complex.partialLogSum_eq_sum, Finset.range_one, Finset.sum_singleton,
      zero_add, pow_one, Complex.norm_exp]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [wm, wp, Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_conj, zero_mul, one_mul, zero_sub]
    norm_num
    ring
  rw [Complex.weierstrassFactor_def, Complex.weierstrassFactor_def,
    Complex.weierstrassFactor_def, Complex.weierstrassFactor_def,
    norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖1 - wm / r‖ * ‖Complex.exp (Complex.partialLogSum 1 (wm / r))‖ *
          (‖1 - wm / conj r‖ *
            ‖Complex.exp (Complex.partialLogSum 1 (wm / conj r))‖) =
        (‖1 - wm / r‖ * ‖1 - wm / conj r‖) *
          (‖Complex.exp (Complex.partialLogSum 1 (wm / r))‖ *
            ‖Complex.exp (Complex.partialLogSum 1 (wm / conj r))‖) := by ring
    _ < (‖1 - wp / r‖ * ‖1 - wp / conj r‖) *
          (‖Complex.exp (Complex.partialLogSum 1 (wp / r))‖ *
            ‖Complex.exp (Complex.partialLogSum 1 (wp / conj r))‖) := by
      rw [hexp]
      exact mul_lt_mul_of_pos_right hlinear
        (mul_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _))
          (norm_pos_iff.mpr (Complex.exp_ne_zero _)))
    _ = ‖1 - wp / r‖ * ‖Complex.exp (Complex.partialLogSum 1 (wp / r))‖ *
          (‖1 - wp / conj r‖ *
            ‖Complex.exp (Complex.partialLogSum 1 (wp / conj r))‖) := by ring

private theorem divisorZeroIndex_im_sq_le
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) {muSq : ℝ}
    (hstrip : ∀ z : ℂ, F z = 0 → z.im ^ 2 ≤ muSq)
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).im ^ 2 ≤ muSq := by
  apply hstrip
  have hsupport :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support
      (f := F) (U := (Set.univ : Set ℂ)) p
  have hdivisor : MeromorphicOn.divisor F Set.univ
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    simpa only [Function.mem_support] using hsupport
  have horder : analyticOrderNatAt F
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    intro hzero
    apply hdivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hF]
    simp [hzero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero horder

private theorem norm_tprod_lt_norm_tprod_of_equiv_pairing
    {ι : Type*} (q : ι ≃ ι) {f g : ι → ℂ}
    (hf : Multipliable f) (hg : Multipliable g)
    (hstrict : ∀ i : ι, ‖f i * f (q i)‖ < ‖g i * g (q i)‖)
    (i0 : ι) (hg0 : ∏' i : ι, g i ≠ 0) :
    ‖∏' i : ι, f i‖ < ‖∏' i : ι, g i‖ := by
  have hfq : Multipliable (f ∘ q) := q.multipliable_iff.mpr hf
  have hgq : Multipliable (g ∘ q) := q.multipliable_iff.mpr hg
  have hfpair : Multipliable (fun i : ι ↦ f i * f (q i)) := hf.mul hfq
  have hgpair : Multipliable (fun i : ι ↦ g i * g (q i)) := hg.mul hgq
  have hfpair_eq :
      (∏' i : ι, f i * f (q i)) = (∏' i : ι, f i) ^ 2 := by
    have hqf : (∏' i : ι, (f ∘ q) i) = ∏' i : ι, f i := by
      simpa only [Function.comp_apply] using q.tprod_eq f
    change (∏' i : ι, f i * (f ∘ q) i) = (∏' i : ι, f i) ^ 2
    rw [hf.tprod_mul hfq, hqf]
    ring
  have hgpair_eq :
      (∏' i : ι, g i * g (q i)) = (∏' i : ι, g i) ^ 2 := by
    have hqg : (∏' i : ι, (g ∘ q) i) = ∏' i : ι, g i := by
      simpa only [Function.comp_apply] using q.tprod_eq g
    change (∏' i : ι, g i * (g ∘ q) i) = (∏' i : ι, g i) ^ 2
    rw [hg.tprod_mul hgq, hqg]
    ring
  have hpaired :
      ‖∏' i : ι, f i * f (q i)‖ < ‖∏' i : ι, g i * g (q i)‖ := by
    apply norm_tprod_lt_norm_tprod_of_pointwise hfpair hgpair
      (fun i ↦ (hstrict i).le) (hstrict i0)
    rw [hgpair_eq]
    exact pow_ne_zero 2 hg0
  rw [hfpair_eq, hgpair_eq, norm_pow, norm_pow] at hpaired
  nlinarith [norm_nonneg (∏' i : ι, f i), norm_nonneg (∏' i : ι, g i)]

private theorem norm_canonicalProduct_pair_sub_I_lt_add_I
    {F : ℂ → ℂ} (horder : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F)
    (hzero : F 0 ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    {muSq : ℝ} (hstrip : ∀ z : ℂ, F z = 0 → z.im ^ 2 ≤ muSq)
    {b : ℂ} (hfactor : ∀ z : ℂ, F z = Complex.exp b *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ) z)
    {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im)
    (hzstrip : muSq - a ^ 2 < z.im ^ 2)
    (p0 : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) :
    ‖Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ)
        (z - I * (a : ℂ))‖ <
      ‖Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set ℂ)
        (z + I * (a : ℂ))‖ := by
  let Z := Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)
  let q : Z ≃ Z := divisorZeroIndexConjEquiv horder.differentiable ⟨0, hzero⟩ hconj
  let zm : ℂ := z - I * (a : ℂ)
  let zp : ℂ := z + I * (a : ℂ)
  let fm : Z → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zm / Complex.Hadamard.divisorZeroIndex₀_val p)
  let fp : Z → ℂ := fun p ↦
    Complex.weierstrassFactor 1
      (zp / Complex.Hadamard.divisorZeroIndex₀_val p)
  have hsum : Summable
      (fun p : Z ↦ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
    simpa [Z] using horder.summable_norm_inv_pow_divisorZeroIndex₀
      (show (0 : ℝ) ≤ 1 by norm_num) ⟨0, hzero⟩
  have hm : Multipliable fm := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 F hsum).hasProd (Set.mem_univ zm)
    simpa only [fm, zm, Z] using hprod.multipliable
  have hp : Multipliable fp := by
    have hprod :=
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ
        1 F hsum).hasProd (Set.mem_univ zp)
    simpa only [fp, zp, Z] using hprod.multipliable
  have hqval : ∀ p : Z,
      Complex.Hadamard.divisorZeroIndex₀_val (q p) =
        conj (Complex.Hadamard.divisorZeroIndex₀_val p) := by
    intro p
    exact divisorZeroIndexConjEquiv_val horder.differentiable ⟨0, hzero⟩ hconj p
  have hstrict : ∀ p : Z, ‖fm p * fm (q p)‖ < ‖fp p * fp (q p)‖ := by
    intro p
    change
      ‖Complex.weierstrassFactor 1
          (zm / Complex.Hadamard.divisorZeroIndex₀_val p) *
        Complex.weierstrassFactor 1
          (zm / Complex.Hadamard.divisorZeroIndex₀_val (q p))‖ <
      ‖Complex.weierstrassFactor 1
          (zp / Complex.Hadamard.divisorZeroIndex₀_val p) *
        Complex.weierstrassFactor 1
          (zp / Complex.Hadamard.divisorZeroIndex₀_val (q p))‖
    rw [hqval]
    simpa only [zm, zp] using
      norm_weierstrassFactor_pair_sub_I_lt_add_I
        (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
        (divisorZeroIndex_im_sq_le horder.differentiable hstrip p) ha hz hzstrip
  have hproduct_ne : ∏' p : Z, fp p ≠ 0 := by
    have hFzp : F zp ≠ 0 := by
      intro hFzero
      have hroot := hstrip zp hFzero
      have him : muSq < zp.im ^ 2 := by
        simp only [zp, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
        nlinarith
      linarith
    intro hprodzero
    apply hFzp
    rw [hfactor zp]
    change Complex.exp b * (∏' p : Z, fp p) = 0
    rw [hprodzero, mul_zero]
  change ‖∏' p : Z, fm p‖ < ‖∏' p : Z, fp p‖
  exact norm_tprod_lt_norm_tprod_of_equiv_pairing q hm hp hstrict p0 hproduct_ne

theorem verticalAverage_conj
    {F : ℂ → ℂ} (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    (a : ℝ) (z : ℂ) :
    verticalAverage a F (conj z) = conj (verticalAverage a F z) := by
  rw [verticalAverage, verticalAverage,
    show conj z + I * (a : ℂ) = conj (z - I * (a : ℂ)) by
      simp [sub_eq_add_neg],
    show conj z - I * (a : ℂ) = conj (z + I * (a : ℂ)) by
      simp [sub_eq_add_neg],
    hconj, hconj, map_div₀, map_add]
  simp only [map_ofNat, add_comm]

theorem verticalAverage_zero_im_sq_le
    {F : ℂ → ℂ} (horder : Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) F)
    (heven : ∀ z : ℂ, F (-z) = F z) (hzero : F 0 ≠ 0)
    (hconj : ∀ z : ℂ, F (conj z) = conj (F z))
    {muSq : ℝ} (hstrip : ∀ z : ℂ, F z = 0 → z.im ^ 2 ≤ muSq)
    {a : ℝ} (ha0 : 0 ≤ a) (haSq : a ^ 2 ≤ muSq) :
    ∀ z : ℂ, verticalAverage a F z = 0 → z.im ^ 2 ≤ muSq - a ^ 2 := by
  intro z havg
  rcases ha0.eq_or_lt with rfl | ha
  · have hz := hstrip z (by simpa [verticalAverage] using havg)
    simpa using hz
  · have hmu : 0 ≤ muSq - a ^ 2 := by linarith
    have hderiv : deriv F 0 = 0 := deriv_zero_of_even horder.differentiable heven
    obtain ⟨b, hfactor⟩ := exists_constant_hadamard_factorization horder hzero hderiv
    have hupper : ∀ {w : ℂ}, 0 < w.im → muSq - a ^ 2 < w.im ^ 2 →
        verticalAverage a F w ≠ 0 := by
      intro w hw hwstrip havg_w
      have hsum_w : F (w + I * (a : ℂ)) + F (w - I * (a : ℂ)) = 0 := by
        simpa [verticalAverage] using havg_w
      let Z := Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)
      cases isEmpty_or_nonempty Z with
      | inl _ =>
          have hproduct : ∀ v : ℂ,
              Complex.Hadamard.divisorCanonicalProduct 1 F
                (Set.univ : Set ℂ) v = 1 := by
            intro v
            simp only [Complex.Hadamard.divisorCanonicalProduct]
            exact tprod_empty
          have hexpzero : Complex.exp b = 0 := by
            have h := hsum_w
            rw [hfactor, hfactor, hproduct, hproduct] at h
            have htwo : (2 : ℂ) * Complex.exp b = 0 := by
              simpa only [mul_one, two_mul] using h
            exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
          exact Complex.exp_ne_zero b hexpzero
      | inr _ =>
          let p0 : Z := Classical.choice (inferInstance : Nonempty Z)
          have hproduct := norm_canonicalProduct_pair_sub_I_lt_add_I
            horder hzero hconj hstrip hfactor ha hw hwstrip p0
          have hstrict : ‖F (w - I * (a : ℂ))‖ < ‖F (w + I * (a : ℂ))‖ := by
            rw [hfactor, hfactor, norm_mul, norm_mul]
            exact mul_lt_mul_of_pos_left hproduct
              (norm_pos_iff.mpr (Complex.exp_ne_zero b))
          have heq : F (w + I * (a : ℂ)) = -F (w - I * (a : ℂ)) :=
            eq_neg_of_add_eq_zero_left hsum_w
          have hnorm : ‖F (w - I * (a : ℂ))‖ = ‖F (w + I * (a : ℂ))‖ := by
            rw [heq, norm_neg]
          exact hstrict.ne hnorm
    by_contra hzstrip
    have hzstrip' : muSq - a ^ 2 < z.im ^ 2 := lt_of_not_ge hzstrip
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · exfalso
      apply hupper (show 0 < (-z).im by simpa using neg_pos.mpr hz)
        (show muSq - a ^ 2 < (-z).im ^ 2 by simpa using hzstrip')
      rw [verticalAverage_even heven]
      exact havg
    · nlinarith
    · exact (hupper hz hzstrip' havg).elim

theorem dbnCoshApprox_zero_pos (t a : ℝ) (n : ℕ) :
    0 < (dbnCoshApprox t a n 0).re := by
  let f : ℝ → ℝ := fun u ↦
    Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh (a * u) ^ n
  have hf_int : Integrable f (volume.restrict (Ioi 0)) := by
    have hre := (integrableOn_dbn_cosh_pow_integrand t a n 0).re
    apply hre.congr
    filter_upwards with u
    simp only [dbnCoshIntegrand, zero_mul, Complex.cos_zero, mul_one]
    dsimp only [f]
    rw [← Complex.ofReal_mul]
    exact RCLike.ofReal_re _
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos
      (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.le))
      (pow_pos (Real.cosh_pos _) n)).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
      intro u hu
      exact (mul_pos
        (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.1.le))
        (pow_pos (Real.cosh_pos _) n)).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  have hf_pos : 0 < ∫ u, f u ∂volume.restrict (Ioi 0) :=
    (integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int).2 hsupport
  have happrox : dbnCoshApprox t a n 0 =
      ((∫ u, f u ∂volume.restrict (Ioi 0) : ℝ) : ℂ) := by
    rw [dbnCoshApprox, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with u
    simp only [dbnCoshIntegrand, zero_mul, Complex.cos_zero, mul_one]
    dsimp only [f]
    push_cast
    ring
  rw [happrox]
  simpa using hf_pos

theorem dbnCoshApprox_zero_ne_zero (t a : ℝ) (n : ℕ) :
    dbnCoshApprox t a n 0 ≠ 0 := by
  intro hzero
  have hpos := dbnCoshApprox_zero_pos t a n
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

private theorem dbnCoshApprox_order_one (t a : ℝ) (n : ℕ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (dbnCoshApprox t a n) := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_entireOfOrderAtMost_one t
  | succ n hn => exact entireOfOrderAtMost_verticalAverage hn a

private theorem dbnCoshApprox_even (t a : ℝ) (n : ℕ) :
    ∀ z : ℂ, dbnCoshApprox t a n (-z) = dbnCoshApprox t a n z := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_neg t
  | succ n hn => exact verticalAverage_even hn a

private theorem dbnCoshApprox_conj (t a : ℝ) (n : ℕ) :
    ∀ z : ℂ, dbnCoshApprox t a n (conj z) = conj (dbnCoshApprox t a n z) := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_conj t
  | succ n hn => exact verticalAverage_conj hn a

theorem dbnCoshApprox_zero_im_sq_le
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hbudget : (n : ℝ) * a ^ 2 ≤ 1) {z : ℂ}
    (hz : dbnCoshApprox 0 a n z = 0) :
    z.im ^ 2 ≤ 1 - (n : ℝ) * a ^ 2 := by
  induction n generalizing z with
  | zero =>
      rw [dbnCoshApprox_zero] at hz
      have hstrip := deBruijnNewmanH_zero_im_mem_Ioo hz
      have hprod : 0 < (z.im + 1) * (1 - z.im) := by
        apply mul_pos
        · linarith [hstrip.1]
        · linarith [hstrip.2]
      have hsq : z.im ^ 2 ≤ 1 := by nlinarith
      simpa only [Nat.cast_zero, zero_mul, sub_zero] using hsq
  | succ n hn =>
      have haSq0 : 0 ≤ a ^ 2 := sq_nonneg a
      have hbudget' : (n : ℝ) * a ^ 2 ≤ 1 := by
        norm_num [Nat.cast_add, Nat.cast_one] at hbudget
        nlinarith
      have haSq : a ^ 2 ≤ 1 - (n : ℝ) * a ^ 2 := by
        norm_num [Nat.cast_add, Nat.cast_one] at hbudget
        nlinarith
      have hzavg : verticalAverage a (dbnCoshApprox 0 a n) z = 0 := by
        rw [verticalAverage_dbnCoshApprox]
        exact hz
      have hstep := verticalAverage_zero_im_sq_le
        (dbnCoshApprox_order_one 0 a n) (dbnCoshApprox_even 0 a n)
        (dbnCoshApprox_zero_ne_zero 0 a n) (dbnCoshApprox_conj 0 a n)
        (fun w hw ↦ hn hbudget' hw) ha haSq z hzavg
      norm_num [Nat.cast_add, Nat.cast_one] at hbudget ⊢
      nlinarith

private theorem dbnForwardApprox_zero_im_sq_le
    {t : ℝ} (ht0 : 0 ≤ t) (hthalf : t ≤ (1 : ℝ) / 2)
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : dbnForwardApprox 0 t n z = 0) :
    z.im ^ 2 ≤ 1 - 2 * t := by
  let a : ℝ := Real.sqrt (2 * t / (n : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrad : 0 ≤ 2 * t / (n : ℝ) := by positivity
  have haSq : a ^ 2 = 2 * t / (n : ℝ) := by
    exact Real.sq_sqrt hrad
  have hbudget : (n : ℝ) * a ^ 2 ≤ 1 := by
    rw [haSq]
    field_simp [hnR.ne']
    nlinarith
  have hstrip := dbnCoshApprox_zero_im_sq_le (Real.sqrt_nonneg _) n hbudget
    (show dbnCoshApprox 0 a n z = 0 by simpa only [dbnForwardApprox, a] using hz)
  rw [haSq] at hstrip
  field_simp [hnR.ne'] at hstrip
  exact hstrip

private theorem exists_deBruijnNewmanH_isolating_outside_sq_strip_closedBall
    {t bound : ℝ} {z0 : ℂ} (houtside : bound < z0.im ^ 2) :
    ∃ R > 0,
      (∀ z ∈ Metric.sphere z0 R, deBruijnNewmanH t z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall z0 R, bound < z.im ^ 2) := by
  have hanalytic : AnalyticOnNhd ℂ (deBruijnNewmanH t) (Set.univ : Set ℂ) :=
    fun z _ ↦ (differentiable_deBruijnNewmanH t).analyticAt z
  have hnot_local_zero : ¬deBruijnNewmanH t =ᶠ[𝓝 z0] 0 := by
    intro hlocal
    have hglobal := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z0) hlocal
    exact deBruijnNewmanH_zero_ne_zero t (hglobal (mem_univ 0))
  have hisolated : ∀ᶠ z in 𝓝[≠] z0, deBruijnNewmanH t z ≠ 0 :=
    ((hanalytic z0 (mem_univ z0)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      hnot_local_zero
  have hnear_nonzero : ∀ᶠ z in 𝓝 z0, z ≠ z0 → deBruijnNewmanH t z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hisolated
  have hopen : IsOpen {z : ℂ | bound < z.im ^ 2} :=
    isOpen_lt continuous_const (Complex.continuous_im.pow 2)
  have hnear_outside : ∀ᶠ z in 𝓝 z0, bound < z.im ^ 2 :=
    hopen.mem_nhds houtside
  have hcombined : ∀ᶠ z in 𝓝 z0,
      (z ≠ z0 → deBruijnNewmanH t z ≠ 0) ∧ bound < z.im ^ 2 :=
    hnear_nonzero.and hnear_outside
  obtain ⟨R, hR, hsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hcombined
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz
    exact (hsubset (Metric.sphere_subset_closedBall hz)).1
      (Metric.ne_of_mem_sphere hz hR.ne')
  · intro z hz
    exact (hsubset hz).2

private theorem dbnForwardApprox_order_one (t delta : ℝ) (n : ℕ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (dbnForwardApprox t delta n) := by
  simpa only [dbnForwardApprox] using
    dbnCoshApprox_order_one t (Real.sqrt (2 * delta / (n : ℝ))) n

theorem eventually_exists_dbnForwardApprox_zero_mem_closedBall
    {t : ℝ} (ht : 0 ≤ t) {z0 : ℂ} {R : ℝ} (hR : 0 < R)
    (hz0 : deBruijnNewmanH t z0 = 0)
    (hboundary : ∀ z ∈ Metric.sphere z0 R, deBruijnNewmanH t z ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      ∃ z ∈ Metric.closedBall z0 R, dbnForwardApprox 0 t n z = 0 := by
  have hsphere_nonempty : (Metric.sphere z0 R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hnorm_cont : ContinuousOn (fun z : ℂ ↦ ‖deBruijnNewmanH t z‖)
      (Metric.sphere z0 R) :=
    (differentiable_deBruijnNewmanH t).continuous.norm.continuousOn
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_sphere z0 R).exists_isMinOn hsphere_nonempty hnorm_cont
  let m : ℝ := ‖deBruijnNewmanH t x‖
  have hm : 0 < m := norm_pos_iff.mpr (hboundary x hx)
  let B : ℝ := ‖z0‖ + R
  have hsphere_bound : ∀ z ∈ Metric.sphere z0 R, ‖z‖ ≤ B := by
    intro z hz
    have hdist : ‖z - z0‖ = R := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp hz
    dsimp only [B]
    calc
      ‖z‖ = ‖(z - z0) + z0‖ := by congr 1; ring
      _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
      _ = ‖z0‖ + R := by rw [hdist]; ring
  have hz0_bound : ‖z0‖ ≤ B := by
    dsimp only [B]
    linarith
  have herr : ∀ᶠ n : ℕ in atTop,
      (∫ u in Ioi (0 : ℝ), dbnForwardError 0 t B n u) < m / 2 := by
    exact (tendsto_integral_dbnForwardError 0 ht B).eventually
      (Iio_mem_nhds (half_pos hm))
  filter_upwards [herr] with n hn
  have hclose : ∀ z ∈ Metric.sphere z0 R,
      ‖dbnForwardApprox 0 t n z - deBruijnNewmanH t z‖ < m / 2 := by
    intro z hz
    have herror := norm_dbnForwardApprox_sub_le_errorIntegral 0 ht
      (hsphere_bound z hz) n
    simpa only [zero_add] using herror.trans_lt hn
  have hcenter_small : ‖dbnForwardApprox 0 t n z0‖ < m / 2 := by
    have hcenter := norm_dbnForwardApprox_sub_le_errorIntegral 0 ht hz0_bound n
    simp only [zero_add, hz0, sub_zero] at hcenter
    exact hcenter.trans_lt hn
  by_contra hexists
  have hzero_free : ∀ z ∈ Metric.closedBall z0 R,
      dbnForwardApprox 0 t n z ≠ 0 := by
    intro z hz hzero
    exact hexists ⟨z, hz, hzero⟩
  have hdiff := (dbnForwardApprox_order_one 0 t n).differentiable
  have hanalytic : AnalyticOnNhd ℂ (dbnForwardApprox 0 t n)
      (Metric.closedBall z0 R) := fun z _ ↦ hdiff.analyticAt z
  have hanalytic_abs : AnalyticOnNhd ℂ (dbnForwardApprox 0 t n)
      (Metric.closedBall z0 |R|) := by
    simpa [abs_of_pos hR] using hanalytic
  have hnorm_boundary : ∀ z ∈ Metric.sphere z0 R,
      m / 2 < ‖dbnForwardApprox 0 t n z‖ := by
    intro z hz
    have hmin : m ≤ ‖deBruijnNewmanH t z‖ := hxmin hz
    have htriangle : ‖deBruijnNewmanH t z‖ ≤
        ‖dbnForwardApprox 0 t n z - deBruijnNewmanH t z‖ +
          ‖dbnForwardApprox 0 t n z‖ := by
      calc
        ‖deBruijnNewmanH t z‖ =
            ‖(deBruijnNewmanH t z - dbnForwardApprox 0 t n z) +
              dbnForwardApprox 0 t n z‖ := by congr 1; ring
        _ ≤ ‖deBruijnNewmanH t z - dbnForwardApprox 0 t n z‖ +
            ‖dbnForwardApprox 0 t n z‖ := norm_add_le _ _
        _ = ‖dbnForwardApprox 0 t n z - deBruijnNewmanH t z‖ +
            ‖dbnForwardApprox 0 t n z‖ := by rw [norm_sub_rev]
    nlinarith [hclose z hz]
  have hcircle : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖dbnForwardApprox 0 t n z‖) z0 R :=
    (hanalytic_abs.mono Metric.sphere_subset_closedBall).meromorphicOn
      |>.circleIntegrable_log_norm
  have hlog_boundary : ∀ z ∈ Metric.sphere z0 |R|,
      Real.log (m / 2) ≤ Real.log ‖dbnForwardApprox 0 t n z‖ := by
    intro z hz
    have hz' : z ∈ Metric.sphere z0 R := by simpa [abs_of_pos hR] using hz
    have hnorm := hnorm_boundary z hz'
    have hnorm_pos : 0 < ‖dbnForwardApprox 0 t n z‖ := (half_pos hm).trans hnorm
    exact Real.strictMonoOn_log.monotoneOn (half_pos hm) hnorm_pos hnorm.le
  have havg_lower : Real.log (m / 2) ≤
      circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox 0 t n z‖) z0 R := by
    calc
      Real.log (m / 2) = circleAverage (fun _ : ℂ ↦ Real.log (m / 2)) z0 R :=
        (circleAverage_const _ _ _).symm
      _ ≤ circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox 0 t n z‖) z0 R :=
        circleAverage_mono (circleIntegrable_const _ _ _) hcircle hlog_boundary
  have hcenter_ne : dbnForwardApprox 0 t n z0 ≠ 0 :=
    hzero_free z0 (Metric.mem_closedBall_self hR.le)
  have hcenter_log : Real.log ‖dbnForwardApprox 0 t n z0‖ < Real.log (m / 2) :=
    Real.log_lt_log (norm_pos_iff.mpr hcenter_ne) hcenter_small
  have hzero_free_abs : ∀ z ∈ Metric.closedBall z0 |R|,
      dbnForwardApprox 0 t n z ≠ 0 := by
    simpa [abs_of_pos hR] using hzero_free
  rw [hanalytic_abs.circleAverage_log_norm_of_ne_zero hzero_free_abs] at havg_lower
  exact (not_lt_of_ge havg_lower) hcenter_log

theorem deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
    {t : ℝ} (ht0 : 0 ≤ t) (hthalf : t ≤ (1 : ℝ) / 2)
    {z : ℂ} (hz : deBruijnNewmanH t z = 0) :
    z.im ^ 2 ≤ 1 - 2 * t := by
  by_contra hstrip
  have houtside : 1 - 2 * t < z.im ^ 2 := lt_of_not_ge hstrip
  obtain ⟨R, hR, hboundary, hball_outside⟩ :=
    exists_deBruijnNewmanH_isolating_outside_sq_strip_closedBall houtside
  have hpersist := eventually_exists_dbnForwardApprox_zero_mem_closedBall
    ht0 hR hz hboundary
  obtain ⟨n, hnzero, hnpos⟩ :=
    (hpersist.and (eventually_gt_atTop 0)).exists
  obtain ⟨w, hwball, hwzero⟩ := hnzero
  have hfinite := dbnForwardApprox_zero_im_sq_le ht0 hthalf hnpos hwzero
  exact (not_lt_of_ge hfinite) (hball_outside w hwball)

theorem deBruijnNewmanAllZerosReal_one_half :
    deBruijnNewmanAllZerosReal ((1 : ℝ) / 2) := by
  intro z hz
  have hsq := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
    (t := (1 : ℝ) / 2) (by norm_num) le_rfl hz
  norm_num at hsq
  nlinarith [sq_nonneg z.im]

end

end LeanLab.Riemann
