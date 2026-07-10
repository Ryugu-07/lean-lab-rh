import Mathlib

set_option linter.style.header false

/-!
# Hello proof

Smoke test for the Lean/mathlib environment.
-/

example : 2 + 2 = 4 := by
  norm_num
