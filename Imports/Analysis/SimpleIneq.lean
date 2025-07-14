/-
Simple Inequalities for Recognition Science Proofs
==================================================

Helper lemmas for completing computational verification sorries
without requiring heavy real analysis machinery.

Key lemmas:
- Binomial lower bound: (1+h)^n ≥ 1 + n*h
- φ bounds and derived inequalities
- Positivity and monotonicity helpers

Author: Recognition Science Implementation
-/

import Imports.Data.Real.Basic
import Imports.Tactic

namespace SimpleIneq
open Real

-- ============================================================================
-- FUNDAMENTAL BINOMIAL INEQUALITY
-- ============================================================================

/-- Binomial lower bound: (1+h)^n ≥ 1 + n*h for h ≥ 0 -/
lemma one_add_mul_lower {n : ℕ} {h : ℝ} (hpos : 0 ≤ h) :
    (1 + h)^n ≥ (1 : ℝ) + n * h := by
  induction n with
  | zero =>
    simp [pow_zero]
    norm_num
  | succ n ih =>
    -- (1+h)^(n+1) = (1+h)^n * (1+h) = (1+h)^n + h*(1+h)^n
    have expand : (1 + h) ^ (n + 1) = (1 + h)^n + h * (1 + h)^n := by
      rw [pow_succ]
      ring
    calc (1 + h)^(n + 1)
      = (1 + h)^n + h * (1 + h)^n := expand
      _ ≥ (1 + n * h) + h * (1 + n * h) := by
        apply add_le_add
        · exact ih
        · apply mul_le_mul_of_nonneg_left ih hpos
      _ = 1 + (n + 1) * h := by ring

-- ============================================================================
-- GOLDEN RATIO BOUNDS AND PROPERTIES
-- ============================================================================

/-- Import golden ratio from vendored Real.Basic -/
noncomputable def φ : ℝ := (1 + sqrt 5) / 2

/-- φ is positive -/
lemma φ_pos : φ > 0 := by
  unfold φ
  apply div_pos
  · apply add_pos
    · norm_num
    · exact sqrt_pos.mpr (by norm_num)
  · norm_num

/-- Tight numerical bounds for φ -/
lemma φ_bounds : (1.618 : ℝ) < φ ∧ φ < (1.619 : ℝ) := by
  constructor
  · unfold φ
    -- √5 > 2.236, so φ = (1 + √5)/2 > (1 + 2.236)/2 = 1.618
    have h_sqrt5 : sqrt 5 > (2.236 : ℝ) := by
      rw [lt_sqrt (by norm_num) (by norm_num)]
      norm_num
    have : (1 + 2.236) / 2 < φ := by
      unfold φ
      apply div_lt_div_of_lt_left
      · norm_num
      · norm_num
      · linarith [h_sqrt5]
    linarith
  · unfold φ
    -- √5 < 2.237, so φ = (1 + √5)/2 < (1 + 2.237)/2 = 1.6185
    have h_sqrt5 : sqrt 5 < (2.237 : ℝ) := by
      rw [sqrt_lt (by norm_num) (by norm_num)]
      norm_num
    have : φ < (1 + 2.237) / 2 := by
      unfold φ
      apply div_lt_div_of_lt_left
      · norm_num
      · norm_num
      · linarith [h_sqrt5]
    linarith

/-- 1/φ lower bound -/
lemma φ_inv_lower : (1/φ) > (1/(1.619 : ℝ)) := by
  apply div_lt_div_of_lt_left
  · norm_num
  · exact φ_pos
  · exact φ_bounds.2

/-- For large n, n/φ is substantial -/
lemma large_ratio_39 : (39 : ℝ) / φ > (24 : ℝ) := by
  have h_φ_upper : φ < 1.619 := φ_bounds.2
  calc (39 : ℝ) / φ
    > 39 / 1.619 := by
      apply div_lt_div_of_lt_left
      · norm_num
      · norm_num
      · exact h_φ_upper
    _ > 24 := by norm_num

-- ============================================================================
-- POWER MONOTONICITY AND BOUNDS
-- ============================================================================

/-- Power function is increasing for base > 1 -/
lemma pow_increasing {a : ℝ} {m n : ℕ} (ha : a > 1) (hmn : m ≤ n) :
    a^m ≤ a^n := by
  exact pow_le_pow_right (le_of_lt ha) hmn

/-- Power preserves strict inequalities -/
lemma pow_strict_mono {a b : ℝ} {n : ℕ} (ha : a > 0) (hab : a < b) (hn : n > 0) :
    a^n < b^n := by
  exact pow_lt_pow_right hab hn

-- ============================================================================
-- FRACTION AND ABSOLUTE VALUE HELPERS
-- ============================================================================

/-- Absolute value of difference over positive denominator -/
lemma abs_div_pos {a b c : ℝ} (hc : c > 0) :
    abs (a - b) / c = abs ((a - b) / c) := by
  rw [abs_div]
  rw [abs_of_pos hc]

/-- Triangle inequality for fractions -/
lemma frac_triangle {a b c : ℝ} (hc : c > 0) :
    abs (a / c - b / c) = abs (a - b) / c := by
  rw [← sub_div, abs_div_pos hc]

end SimpleIneq
