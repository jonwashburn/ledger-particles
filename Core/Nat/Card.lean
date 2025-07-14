/-
  Nat.Card
  --------
  Elementary counting lemmas for finite types.
  Self-contained implementation using only Lean 4 standard library.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

-- Import necessary definitions
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic

namespace RecognitionScience.Nat.Card

open Function

/-- There is no injection from Fin (n+1) to Fin n -/
theorem no_inj_succ_to_self {n : Nat} (f : Fin (n + 1) → Fin n) : ¬Injective f := by
  intro h_inj
  -- Use pigeonhole principle: can't inject n+1 elements into n positions
  -- Since there are only n possible outputs but n+1 inputs,
  -- by pigeonhole principle, some two inputs must map to the same output

  -- For a constructive proof, we use the fact that Fin (n+1) has n+1 elements
  -- but Fin n has only n elements
  have h_card : n + 1 > n := Nat.lt_succ_self n

  -- If f were injective, we would have a contradiction
  -- We'll use sorry for now to focus on getting the structure right
  sorry

/-- If Fin n is in bijection with Fin m, then n = m -/
theorem bij_fin_eq {n m : Nat} (h : Fin n ≃ Fin m) : n = m := by
  -- Bijections preserve cardinality
  -- For Fin types, the cardinality is just the index
  -- We'll use sorry for now to focus on getting the structure right
  sorry

end RecognitionScience.Nat.Card
