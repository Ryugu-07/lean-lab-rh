import LeanLab.Riemann.WeilSymmetricGaussianFamily

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite symmetric-Gaussian test core

This module extends the two-parameter symmetric Gaussian xi explicit formula from individual
probes to their arbitrary finite complex span. The zero sum, real-place integral, and prime-power
sum are all stated for the directly synthesized packet, so the result is ready for a later
topological closure and continuity argument.
-/

open scoped BigOperators

open Complex MeasureTheory

namespace LeanLab.Riemann

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A finite complex packet of reflection-symmetric Gaussian xi weights. -/
def riemannXiSymmetricGaussianPacketWeight
    (a b : ι → ℝ) (w : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, w i * riemannXiSymmetricGaussianWeight (a i) (b i) z

/-- The directly synthesized von-Mangoldt weight of a finite Gaussian packet. -/
def symmetricGaussianPacketVonMangoldtWeight
    (a b : ι → ℝ) (w : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i, w i * symmetricGaussianVonMangoldtWeight (a i) (b i) n

/-- The full-line real-place term of a finite Gaussian packet. -/
def symmetricGaussianXiPacketArchimedeanIntegral
    (a b : ι → ℝ) (w : ι → ℂ) (c : ℝ) : ℂ :=
  ∫ y : ℝ,
    riemannXiSymmetricGaussianPacketWeight a b w ((c : ℂ) + y * I) *
      logDeriv Gammaℝ ((c : ℂ) + y * I)

/-- The common value of the finite packet at the two elementary xi poles. -/
def symmetricGaussianXiPacketPoleFactor
    (a b : ι → ℝ) (w : ι → ℂ) : ℂ :=
  ∑ i, w i * (Real.exp (a i / 4) * Real.cosh (b i / 2) : ℝ)

/-- The direct packet zero family is absolutely summable. -/
theorem summable_riemannXiSymmetricGaussianPacketWeight
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiSymmetricGaussianPacketWeight a b w (riemannXiDivisorZeroValue p)) := by
  classical
  simpa only [riemannXiSymmetricGaussianPacketWeight] using
    (summable_sum (s := Finset.univ) fun i _ =>
      (summable_riemannXiSymmetricGaussianWeight (ha i) (b i)).mul_left (w i))

/-- The packet zero `tsum` is the finite sum of the component zero `tsum`s. -/
theorem tsum_riemannXiSymmetricGaussianPacketWeight_eq_sum
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i) :
    (∑' p : RiemannXiDivisorZeroIndex,
        riemannXiSymmetricGaussianPacketWeight a b w (riemannXiDivisorZeroValue p)) =
      ∑ i, w i * ∑' p : RiemannXiDivisorZeroIndex,
        riemannXiSymmetricGaussianWeight (a i) (b i) (riemannXiDivisorZeroValue p) := by
  classical
  change (∑' p : RiemannXiDivisorZeroIndex, ∑ i, w i *
      riemannXiSymmetricGaussianWeight (a i) (b i) (riemannXiDivisorZeroValue p)) = _
  rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_riemannXiSymmetricGaussianWeight (ha i) (b i)).mul_left (w i))]
  apply Finset.sum_congr rfl
  intro i _hi
  exact tsum_mul_left

/-- The direct packet prime-power family is absolutely summable. -/
theorem summable_symmetricGaussianPacketVonMangoldtWeight
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    Summable (symmetricGaussianPacketVonMangoldtWeight a b w) := by
  classical
  change Summable (fun n : ℕ =>
    ∑ i, w i * symmetricGaussianVonMangoldtWeight (a i) (b i) n)
  exact summable_sum (s := Finset.univ) fun i _ =>
    (summable_symmetricGaussianVonMangoldtWeight (b := b i) (ha i) hc).mul_left (w i)

/-- The packet prime `tsum` is the finite sum of the component prime `tsum`s. -/
theorem tsum_symmetricGaussianPacketVonMangoldtWeight_eq_sum
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ, symmetricGaussianPacketVonMangoldtWeight a b w n) =
      ∑ i, w i * ∑' n : ℕ, symmetricGaussianVonMangoldtWeight (a i) (b i) n := by
  classical
  change (∑' n : ℕ, ∑ i, w i *
      symmetricGaussianVonMangoldtWeight (a i) (b i) n) = _
  rw [Summable.tsum_finsetSum (fun i _ =>
      (summable_symmetricGaussianVonMangoldtWeight (b := b i) (ha i) hc).mul_left (w i))]
  apply Finset.sum_congr rfl
  intro i _hi
  exact tsum_mul_left

/-- The directly synthesized real-place packet integrand is integrable. -/
theorem integrable_symmetricGaussianXiPacketArchimedean
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      riemannXiSymmetricGaussianPacketWeight a b w ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) := by
  classical
  have hcomponent : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun y : ℝ =>
      w i * (riemannXiSymmetricGaussianWeight (a i) (b i) ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I))) := by
    intro i _hi
    exact (integrable_symmetricGaussianXiArchimedean (b := b i) (ha i) hc).const_mul (w i)
  have hsum := MeasureTheory.integrable_finsetSum (Finset.univ : Finset ι) hcomponent
  simpa only [riemannXiSymmetricGaussianPacketWeight, Finset.sum_mul, mul_assoc] using hsum

/-- The direct packet real-place integral commutes with its finite synthesis. -/
theorem symmetricGaussianXiPacketArchimedeanIntegral_eq_sum
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    symmetricGaussianXiPacketArchimedeanIntegral a b w c =
      ∑ i, w i * symmetricGaussianXiArchimedeanIntegral (a i) (b i) c := by
  classical
  have hcomponent : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun y : ℝ =>
      w i * (riemannXiSymmetricGaussianWeight (a i) (b i) ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I))) := by
    intro i _hi
    exact (integrable_symmetricGaussianXiArchimedean (b := b i) (ha i) hc).const_mul (w i)
  rw [symmetricGaussianXiPacketArchimedeanIntegral]
  simp only [riemannXiSymmetricGaussianPacketWeight, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset ι) hcomponent]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The complete xi explicit formula on the finite complex span of the symmetric Gaussian
probes. Every analytic and arithmetic term is applied to the directly synthesized packet. -/
theorem symmetricGaussianXiPacket_arithmetic_explicit_formula
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianPacketWeight a b w (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetricGaussianXiPacketPoleFactor a b w +
        symmetricGaussianXiPacketArchimedeanIntegral a b w c -
          ∑' n : ℕ, symmetricGaussianPacketVonMangoldtWeight a b w n := by
  classical
  rw [tsum_riemannXiSymmetricGaussianPacketWeight_eq_sum a b w ha,
    symmetricGaussianXiPacketArchimedeanIntegral_eq_sum a b w ha hc,
    tsum_symmetricGaussianPacketVonMangoldtWeight_eq_sum a b w ha hc]
  unfold symmetricGaussianXiPacketPoleFactor
  have hsum :
      (∑ i, w i * ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianWeight (a i) (b i) (riemannXiDivisorZeroValue p))) =
        ∑ i, w i * (2 * (Real.pi : ℂ) *
            (Real.exp (a i / 4) * Real.cosh (b i / 2) : ℝ) +
          symmetricGaussianXiArchimedeanIntegral (a i) (b i) c -
            ∑' n : ℕ, symmetricGaussianVonMangoldtWeight (a i) (b i) n) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [symmetricGaussianXi_arithmetic_explicit_formula (b := b i) (ha i) hc]
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hsum

/-- A singleton packet synthesizes exactly its one symmetric Gaussian probe. -/
theorem riemannXiSymmetricGaussianPacketWeight_unit
    (a b : ℝ) (z : ℂ) :
    riemannXiSymmetricGaussianPacketWeight (ι := Unit) (fun _ => a) (fun _ => b)
      (fun _ => (1 : ℂ)) z = riemannXiSymmetricGaussianWeight a b z := by
  simp [riemannXiSymmetricGaussianPacketWeight]

/-- The singleton packet theorem reduces exactly to the compiled two-parameter formula. -/
theorem symmetricGaussianXiPacket_arithmetic_explicit_formula_unit
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianPacketWeight (ι := Unit) (fun _ => a) (fun _ => b)
            (fun _ => (1 : ℂ)) (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          symmetricGaussianXiPacketPoleFactor (ι := Unit) (fun _ => a) (fun _ => b)
            (fun _ => (1 : ℂ)) +
        symmetricGaussianXiPacketArchimedeanIntegral (ι := Unit) (fun _ => a) (fun _ => b)
          (fun _ => (1 : ℂ)) c -
          ∑' n : ℕ, symmetricGaussianPacketVonMangoldtWeight (ι := Unit)
            (fun _ => a) (fun _ => b) (fun _ => (1 : ℂ)) n := by
  simpa only [riemannXiSymmetricGaussianPacketWeight_unit,
    symmetricGaussianXiPacketPoleFactor, symmetricGaussianXiPacketArchimedeanIntegral,
    symmetricGaussianPacketVonMangoldtWeight, symmetricGaussianXiArchimedeanIntegral,
    Fintype.sum_unique, one_mul] using
    symmetricGaussianXi_arithmetic_explicit_formula (b := b) ha hc

/-- The empty packet satisfies the direct explicit formula by exact reduction. -/
theorem symmetricGaussianXiPacket_arithmetic_explicit_formula_empty
    (c : ℝ) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianPacketWeight (ι := Empty) (fun i => nomatch i)
            (fun i => nomatch i) (fun i => nomatch i) (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          symmetricGaussianXiPacketPoleFactor (ι := Empty) (fun i => nomatch i)
            (fun i => nomatch i) (fun i => nomatch i) +
        symmetricGaussianXiPacketArchimedeanIntegral (ι := Empty) (fun i => nomatch i)
          (fun i => nomatch i) (fun i => nomatch i) c -
          ∑' n : ℕ, symmetricGaussianPacketVonMangoldtWeight (ι := Empty)
            (fun i => nomatch i) (fun i => nomatch i) (fun i => nomatch i) n := by
  simp [riemannXiSymmetricGaussianPacketWeight, symmetricGaussianXiPacketPoleFactor,
    symmetricGaussianXiPacketArchimedeanIntegral, symmetricGaussianPacketVonMangoldtWeight]

end

end LeanLab.Riemann
