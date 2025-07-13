/-
Minimal Analysis.SpecialFunctions.Pow.Real for Recognition Science
Based on Mathlib but self-contained
-/

import Imports.Data.Real.Basic

namespace Real

-- Real power function properties
theorem pow_zero (a : ℝ) : a ^ (0 : ℕ) = 1 := by simp [pow_zero]
theorem pow_one (a : ℝ) : a ^ (1 : ℕ) = a := by simp [pow_one]
theorem pow_two (a : ℝ) : a ^ (2 : ℕ) = a * a := by simp [pow_two]

theorem pow_add (a : ℝ) (m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  simp [pow_add]

theorem pow_mul (a : ℝ) (m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  simp [pow_mul]

-- Monotonicity
theorem pow_lt_pow_right {a : ℝ} (ha : 1 < a) {m n : ℕ} (h : m < n) : a ^ m < a ^ n := by
  exact pow_lt_pow_right ha h

theorem pow_le_pow_right {a : ℝ} (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := by
  exact pow_le_pow_right ha h

-- For Recognition Science φ calculations
theorem pow_pos_of_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := by
  exact pow_pos ha n

end Real
