import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section

/-!
# A ladder-frequency counterexample for the M2 literature audit

This file checks that logarithmic separation in the dyadic-triadic ladder is not bounded below
by a positive constant times Manhattan distance.
-/

namespace LeanLab.Riemann

/-- The source's logarithmic frequency for two dyadic-triadic ladder indices. -/
def m2AuditCarvillLadderFrequency (j k j' k' : ℕ) : ℝ :=
  (((j' : ℤ) - j : ℤ) : ℝ) * Real.log 2 +
    (((k' : ℤ) - k : ℤ) : ℝ) * Real.log 3

/-- Manhattan distance between two dyadic-triadic ladder indices. -/
def m2AuditCarvillLadderDistance (j k j' k' : ℕ) : ℕ :=
  Int.natAbs ((j' : ℤ) - j) + Int.natAbs ((k' : ℤ) - k)

theorem m2Audit_three_log_two_lt_two_log_three :
    3 * Real.log 2 < 2 * Real.log 3 := by
  have h := Real.strictMonoOn_log
    (show (2 : ℝ) ^ 3 ∈ Set.Ioi 0 by norm_num)
    (show (3 : ℝ) ^ 2 ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ^ 3 < (3 : ℝ) ^ 2 by norm_num)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem m2Audit_two_log_three_lt_four_log_two :
    2 * Real.log 3 < 4 * Real.log 2 := by
  have h := Real.strictMonoOn_log
    (show (3 : ℝ) ^ 2 ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ^ 4 ∈ Set.Ioi 0 by norm_num)
    (show (3 : ℝ) ^ 2 < (2 : ℝ) ^ 4 by norm_num)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem m2Audit_carvill_pair_frequency :
    m2AuditCarvillLadderFrequency 0 2 3 0 =
      3 * Real.log 2 - 2 * Real.log 3 := by
  norm_num [m2AuditCarvillLadderFrequency]
  ring

theorem m2Audit_carvill_pair_distance :
    m2AuditCarvillLadderDistance 0 2 3 0 = 5 := by
  norm_num [m2AuditCarvillLadderDistance]

/-- The source's frequency lower bound fails for `(j,k)=(0,2)` and `(j',k')=(3,0)`. -/
theorem m2Audit_carvill_ladder_frequency_counterexample :
    |3 * Real.log 2 - 2 * Real.log 3| <
      min (Real.log 2) (Real.log 3) * 5 := by
  have hlog : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  rw [min_eq_left hlog.le]
  rw [abs_of_neg (sub_neg.mpr m2Audit_three_log_two_lt_two_log_three)]
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith [m2Audit_two_log_three_lt_four_log_two]

/-- Negation of the displayed frequency-to-Manhattan-distance estimate at the audit pair. -/
theorem not_m2Audit_carvill_ladder_frequency_lower_bound :
    ¬ min (Real.log 2) (Real.log 3) * 5 ≤
      |3 * Real.log 2 - 2 * Real.log 3| :=
  not_le_of_gt m2Audit_carvill_ladder_frequency_counterexample

/-- Source-facing failure of the frequency lower bound at two admissible ladder indices. -/
theorem not_m2Audit_carvill_source_frequency_lower_bound :
    ¬ min (Real.log 2) (Real.log 3) *
        (m2AuditCarvillLadderDistance 0 2 3 0 : ℝ) ≤
      |m2AuditCarvillLadderFrequency 0 2 3 0| := by
  rw [m2Audit_carvill_pair_distance, m2Audit_carvill_pair_frequency]
  exact not_m2Audit_carvill_ladder_frequency_lower_bound

end LeanLab.Riemann
