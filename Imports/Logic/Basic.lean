/-
Minimal Logic.Basic for Recognition Science
Based on Mathlib but self-contained to avoid dependency issues
-/

-- Basic logical operations and tactics
variable {α β γ : Sort*}

-- Function composition and identity
def Function.comp (g : β → γ) (f : α → β) : α → γ := fun a => g (f a)
def Function.id : α → α := fun a => a

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
