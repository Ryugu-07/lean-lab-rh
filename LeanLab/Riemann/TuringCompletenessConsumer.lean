import LeanLab.Riemann.WeilZeroCutoff

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Turing-style finite zero-list completeness

This module isolates the positive logical consumer behind a Turing-style zero computation.
Candidate zeros are actual multiplicity-bearing xi divisor indices. An exact argument-principle
count turns subset inclusion into finite exhaustion; critical-line location then transfers to
every actual nontrivial zeta zero in the rectangle.

No root isolation, numerical height, Turing average estimate, or global tail theorem is asserted.
-/

open Complex Function Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The actual multiplicity-bearing xi divisor indices strictly inside an open rectangle. -/
def turingXiZeroIndexFinset (l r b t : ℝ) : Finset RiemannXiDivisorZeroIndex :=
  (finite_riemannXiZeroStrictlyInsideRectangle l r b t).toFinset

@[simp]
theorem mem_turingXiZeroIndexFinset_iff
    {l r b t : ℝ} {p : RiemannXiDivisorZeroIndex} :
    p ∈ turingXiZeroIndexFinset l r b t ↔
      riemannXiZeroStrictlyInsideRectangle l r b t p := by
  simp [turingXiZeroIndexFinset]

/-- The constant-one finite sum over the interior divisor indices is their cardinality. -/
theorem finsum_riemannXiZeroStrictlyInsideRectangle_one_eq_card
    (l r b t : ℝ) :
    (∑ᶠ p : RiemannXiDivisorZeroIndex,
        if riemannXiZeroStrictlyInsideRectangle l r b t p then (1 : ℂ) else 0) =
      (turingXiZeroIndexFinset l r b t).card := by
  rw [finsum_eq_sum_of_support_subset
    (s := turingXiZeroIndexFinset l r b t)]
  · have hfilter :
        (turingXiZeroIndexFinset l r b t).filter
            (riemannXiZeroStrictlyInsideRectangle l r b t) =
          turingXiZeroIndexFinset l r b t := by
      apply Finset.filter_eq_self.2
      intro p hp
      exact mem_turingXiZeroIndexFinset_iff.1 hp
    simp [hfilter]
  · intro p hp
    simp only [Function.mem_support] at hp
    by_contra hpmem
    have hpout : ¬riemannXiZeroStrictlyInsideRectangle l r b t p := by
      simpa using hpmem
    exact hp (if_neg hpout)

/-- The unweighted xi argument principle counts actual interior divisor indices with
multiplicity. -/
theorem rectangleBoundaryIntegral_logDeriv_riemannXi_eq_turingXiZeroIndexFinset_card
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    rectangleBoundaryIntegral (logDeriv riemannXi) l r b t =
      2 * (Real.pi : ℂ) * I * (turingXiZeroIndexFinset l r b t).card := by
  have hcount :=
    rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
      (F := fun _ => 1) (by fun_prop) hlr hbt hboundary
  simpa [finsum_riemannXiZeroStrictlyInsideRectangle_one_eq_card] using hcount

/-- A finite candidate list of actual xi divisor indices, together with line location and exact
cardinality. -/
structure TuringXiRectangleCertificate
    (candidates : Finset RiemannXiDivisorZeroIndex) (l r b t : ℝ) : Prop where
  subset_actual :
    candidates ⊆ turingXiZeroIndexFinset l r b t
  candidates_on_line :
    ∀ p ∈ candidates, OnCriticalLine (riemannXiDivisorZeroValue p)
  card_eq_actual :
    candidates.card = (turingXiZeroIndexFinset l r b t).card

/-- A candidate subfinset with the full cardinality exhausts the actual divisor indices. -/
theorem TuringXiRectangleCertificate.candidates_eq_actual
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiRectangleCertificate candidates l r b t) :
    candidates = turingXiZeroIndexFinset l r b t := by
  apply Finset.eq_of_subset_of_card_le hcert.subset_actual
  rw [hcert.card_eq_actual]

/-- Exhaustion transfers the certified critical-line location to every actual divisor index in
the rectangle. -/
theorem TuringXiRectangleCertificate.actual_indices_on_line
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiRectangleCertificate candidates l r b t)
    {p : RiemannXiDivisorZeroIndex}
    (hp : p ∈ turingXiZeroIndexFinset l r b t) :
    OnCriticalLine (riemannXiDivisorZeroValue p) := by
  apply hcert.candidates_on_line p
  rw [hcert.candidates_eq_actual]
  exact hp

/-- A complete certified candidate list places every actual nontrivial zeta zero in the open
rectangle on the critical line. -/
theorem TuringXiRectangleCertificate.nontrivial_zeros_on_line
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiRectangleCertificate candidates l r b t)
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hinside :
      l < rho.re ∧ rho.re < r ∧ b < rho.im ∧ rho.im < t) :
    OnCriticalLine rho := by
  obtain ⟨p, hpval⟩ := (exists_riemannXiDivisorZeroIndex_val_iff rho).2 hrho
  have hpinside : riemannXiZeroStrictlyInsideRectangle l r b t p := by
    simpa [riemannXiZeroStrictlyInsideRectangle, hpval] using hinside
  have hpline := hcert.actual_indices_on_line
    (mem_turingXiZeroIndexFinset_iff.2 hpinside)
  simpa [hpval] using hpline

/-- The boundary-count form of a Turing certificate. The analytic count replaces a direct
cardinality equality. -/
structure TuringXiBoundaryCountCertificate
    (candidates : Finset RiemannXiDivisorZeroIndex) (l r b t : ℝ) : Prop where
  subset_actual :
    candidates ⊆ turingXiZeroIndexFinset l r b t
  candidates_on_line :
    ∀ p ∈ candidates, OnCriticalLine (riemannXiDivisorZeroValue p)
  boundary_count :
    rectangleBoundaryIntegral (logDeriv riemannXi) l r b t =
      2 * (Real.pi : ℂ) * I * candidates.card

/-- The analytic xi argument-principle identity converts a boundary-count certificate into an
exact rectangle certificate. -/
theorem TuringXiBoundaryCountCertificate.toRectangleCertificate
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiBoundaryCountCertificate candidates l r b t)
    (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    TuringXiRectangleCertificate candidates l r b t := by
  have hactual :=
    rectangleBoundaryIntegral_logDeriv_riemannXi_eq_turingXiZeroIndexFinset_card
      hlr hbt hboundary
  have hmul :
      2 * (Real.pi : ℂ) * I * candidates.card =
        2 * (Real.pi : ℂ) * I * (turingXiZeroIndexFinset l r b t).card :=
    hcert.boundary_count.symm.trans hactual
  have hcoeff : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hcardCast :
      (candidates.card : ℂ) =
        ((turingXiZeroIndexFinset l r b t).card : ℂ) := by
    exact mul_left_cancel₀ hcoeff hmul
  refine
    { subset_actual := hcert.subset_actual
      candidates_on_line := hcert.candidates_on_line
      card_eq_actual := ?_ }
  exact_mod_cast hcardCast

/-- The boundary-count certificate exhausts the actual interior divisor indices. -/
theorem TuringXiBoundaryCountCertificate.candidates_eq_actual
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiBoundaryCountCertificate candidates l r b t)
    (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    candidates = turingXiZeroIndexFinset l r b t :=
  (hcert.toRectangleCertificate hlr hbt hboundary).candidates_eq_actual

/-- The boundary-count certificate places every actual nontrivial zeta zero in the rectangle on
the critical line. -/
theorem TuringXiBoundaryCountCertificate.nontrivial_zeros_on_line
    {candidates : Finset RiemannXiDivisorZeroIndex} {l r b t : ℝ}
    (hcert : TuringXiBoundaryCountCertificate candidates l r b t)
    (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p)
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hinside :
      l < rho.re ∧ rho.re < r ∧ b < rho.im ∧ rho.im < t) :
    OnCriticalLine rho :=
  (hcert.toRectangleCertificate hlr hbt hboundary).nontrivial_zeros_on_line
    hrho hinside

/-- Without the exact count, checking every listed point can omit an off-line ambient point. -/
theorem exists_line_candidate_proper_subset_with_offline_ambient :
    ∃ candidates ambient : Finset ℂ,
      candidates ⊂ ambient ∧
      (∀ rho ∈ candidates, OnCriticalLine rho) ∧
      ∃ rho ∈ ambient, ¬OnCriticalLine rho := by
  let linePoint : ℂ := (1 / 2 : ℝ) + I
  let offLinePoint : ℂ := (1 / 4 : ℝ) + 2 * I
  refine ⟨{linePoint}, {linePoint, offLinePoint}, ?_, ?_, offLinePoint, ?_, ?_⟩
  · rw [Finset.ssubset_iff_subset_ne]
    constructor
    · simp
    · intro heq
      have hoff : offLinePoint ∈ ({linePoint} : Finset ℂ) := by
        rw [heq]
        simp
      simp only [Finset.mem_singleton] at hoff
      have hre := congrArg Complex.re hoff
      norm_num [linePoint, offLinePoint] at hre
  · intro rho hrho
    simp only [Finset.mem_singleton] at hrho
    subst rho
    norm_num [linePoint, OnCriticalLine]
  · simp
  · norm_num [offLinePoint, OnCriticalLine]

/-- Aggregate of exactly the finite Turing-completeness consumer proved in this module. -/
structure TuringCompletenessConsumerCertificate : Prop where
  membership_exact :
    ∀ l r b t p,
      p ∈ turingXiZeroIndexFinset l r b t ↔
        riemannXiZeroStrictlyInsideRectangle l r b t p
  argument_principle_count :
    ∀ {l r b t : ℝ}, l < r → b < t →
      (∀ p : RiemannXiDivisorZeroIndex,
        ¬riemannXiZeroOnRectangleBoundary l r b t p) →
      rectangleBoundaryIntegral (logDeriv riemannXi) l r b t =
        2 * (Real.pi : ℂ) * I * (turingXiZeroIndexFinset l r b t).card
  direct_exhaustion :
    ∀ {candidates l r b t},
      TuringXiRectangleCertificate candidates l r b t →
      candidates = turingXiZeroIndexFinset l r b t
  direct_actual_zero_location :
    ∀ {candidates l r b t rho},
      TuringXiRectangleCertificate candidates l r b t →
      IsNontrivialZero rho →
      l < rho.re ∧ rho.re < r ∧ b < rho.im ∧ rho.im < t →
      OnCriticalLine rho
  boundary_exhaustion :
    ∀ {candidates l r b t},
      TuringXiBoundaryCountCertificate candidates l r b t →
      l < r → b < t →
      (∀ p : RiemannXiDivisorZeroIndex,
        ¬riemannXiZeroOnRectangleBoundary l r b t p) →
      candidates = turingXiZeroIndexFinset l r b t
  boundary_actual_zero_location :
    ∀ {candidates l r b t rho},
      TuringXiBoundaryCountCertificate candidates l r b t →
      l < r → b < t →
      (∀ p : RiemannXiDivisorZeroIndex,
        ¬riemannXiZeroOnRectangleBoundary l r b t p) →
      IsNontrivialZero rho →
      l < rho.re ∧ rho.re < r ∧ b < rho.im ∧ rho.im < t →
      OnCriticalLine rho
  no_count_negative_control :
    ∃ candidates ambient : Finset ℂ,
      candidates ⊂ ambient ∧
      (∀ rho ∈ candidates, OnCriticalLine rho) ∧
      ∃ rho ∈ ambient, ¬OnCriticalLine rho

/-- Kernel-checked endpoint for the positive Turing-style finite completeness consumer. -/
theorem turingCompletenessConsumer_endpoint :
    TuringCompletenessConsumerCertificate where
  membership_exact := by
    intro l r b t p
    exact mem_turingXiZeroIndexFinset_iff
  argument_principle_count := by
    intro l r b t hlr hbt hboundary
    exact
      rectangleBoundaryIntegral_logDeriv_riemannXi_eq_turingXiZeroIndexFinset_card
        hlr hbt hboundary
  direct_exhaustion := by
    intro candidates l r b t hcert
    exact hcert.candidates_eq_actual
  direct_actual_zero_location := by
    intro candidates l r b t rho hcert hrho hinside
    exact hcert.nontrivial_zeros_on_line hrho hinside
  boundary_exhaustion := by
    intro candidates l r b t hcert hlr hbt hboundary
    exact hcert.candidates_eq_actual hlr hbt hboundary
  boundary_actual_zero_location := by
    intro candidates l r b t rho hcert hlr hbt hboundary hrho hinside
    exact hcert.nontrivial_zeros_on_line hlr hbt hboundary hrho hinside
  no_count_negative_control :=
    exists_line_candidate_proper_subset_with_offline_ambient

end

end LeanLab.Riemann
