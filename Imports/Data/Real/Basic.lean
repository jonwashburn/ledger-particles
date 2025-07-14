/-
Minimal Data.Real.Basic for Recognition Science
Based on Mathlib but self-contained
-/

-- Real number basics
namespace Real

-- Basic constants
noncomputable def π : ℝ := Real.pi
noncomputable def e : ℝ := Real.exp 1

-- Golden ratio (key for Recognition Science)
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

-- Basic properties
theorem φ_pos : φ > 0 := by
  unfold φ
  apply div_pos
  · apply add_pos
    · norm_num
    · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  · norm_num

theorem φ_gt_one : φ > 1 := by
  unfold φ
  have h : Real.sqrt 5 > 2 := by
    have h₁ : (2 : ℝ) ^ 2 = 4 := by norm_num
    have h₂ : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    rw [← h₁, ← h₂]
    apply pow_lt_pow_right (by norm_num : (1 : ℝ) < 2)
    norm_num
  have h_calc : (1 + Real.sqrt 5) / 2 > (1 + 2) / 2 := by
    apply div_lt_div_of_lt_left
    · norm_num
    · norm_num
    · linarith [h]
  have : (1 + 2) / 2 = (1.5 : ℝ) := by norm_num
  rw [this] at h_calc
  have : (1.5 : ℝ) > 1 := by norm_num
  linarith [h_calc]

-- Golden ratio algebraic property: φ² = φ + 1
theorem φ_algebraic_property : φ ^ 2 = φ + 1 := by
  unfold φ
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  ring

-- Basic real operations
theorem add_comm (a b : ℝ) : a + b = b + a := add_comm a b
theorem mul_comm (a b : ℝ) : a * b = b * a := mul_comm a b
theorem add_assoc (a b c : ℝ) : (a + b) + c = a + (b + c) := add_assoc a b c
theorem mul_assoc (a b c : ℝ) : (a * b) * c = a * (b * c) := mul_assoc a b c

-- Absolute value
theorem abs_nonneg (a : ℝ) : 0 ≤ |a| := abs_nonneg a
theorem abs_pos {a : ℝ} (h : a ≠ 0) : 0 < |a| := abs_pos.mpr h

-- Powers
theorem pow_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := Real.pow_pos ha n
theorem pow_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ a ^ n := Real.pow_nonneg ha n

end Real
