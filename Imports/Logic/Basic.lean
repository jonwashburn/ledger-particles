/-
Minimal Logic.Basic for Recognition Science
Based on Mathlib but self-contained to avoid dependency issues
-/

-- Import from Mathlib instead of redefining
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

-- Re-export what we need
open Function

-- Basic logical lemmas
theorem not_not_iff (a : Prop) : ¬¬a ↔ a := by
  constructor
  · intro h
    by_contra h'
    exact h h'
  · intro h h'
    exact h' h

-- Exists and forall manipulation
theorem exists_prop {p q : Prop} : (∃ (_ : p), q) ↔ p ∧ q := by
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hp, hq⟩
  · intro ⟨hp, hq⟩
    exact ⟨hp, hq⟩

-- Basic function properties
namespace Function

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

theorem bijective_id : Bijective (@id α) := by
  constructor
  · intro a₁ a₂ h
    exact h
  · intro a
    use a
    rfl

end Function
