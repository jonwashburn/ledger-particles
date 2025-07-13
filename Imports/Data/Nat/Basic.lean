/-
Minimal Data.Nat.Basic for Recognition Science
Based on Mathlib but self-contained
-/

namespace Nat

-- Basic properties of natural numbers
theorem zero_le (n : ℕ) : 0 ≤ n := Nat.zero_le n

theorem succ_pos (n : ℕ) : 0 < n.succ := Nat.zero_lt_succ n

theorem one_pos : (0 : ℕ) < 1 := Nat.zero_lt_one

-- Addition properties
theorem add_zero (n : ℕ) : n + 0 = n := Nat.add_zero n
theorem zero_add (n : ℕ) : 0 + n = n := Nat.zero_add n
theorem add_succ (n m : ℕ) : n + m.succ = (n + m).succ := Nat.add_succ n m
theorem succ_add (n m : ℕ) : n.succ + m = (n + m).succ := Nat.succ_add n m

-- Multiplication properties
theorem mul_zero (n : ℕ) : n * 0 = 0 := Nat.mul_zero n
theorem zero_mul (n : ℕ) : 0 * n = 0 := Nat.zero_mul n
theorem mul_one (n : ℕ) : n * 1 = n := Nat.mul_one n
theorem one_mul (n : ℕ) : 1 * n = n := Nat.one_mul n

-- Ordering properties
theorem le_refl (n : ℕ) : n ≤ n := Nat.le_refl n
theorem le_trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k := Nat.le_trans
theorem lt_trans {n m k : ℕ} : n < m → m < k → n < k := Nat.lt_trans

-- Useful for Recognition Science
theorem mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by
  have h := Nat.mod_two_eq_zero_or_one n
  exact h

end Nat
