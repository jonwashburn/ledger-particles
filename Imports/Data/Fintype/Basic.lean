/-
Minimal Data.Fintype.Basic for Recognition Science
Based on Mathlib but self-contained
-/

import Imports.Logic.Basic
import Imports.Data.Nat.Basic

-- Basic finite type structure
class Fintype (α : Type*) where
  elems : Finset α
  complete : ∀ a : α, a ∈ elems

-- Finite sets (simplified)
structure Finset (α : Type*) where
  val : List α
  nodup : List.Nodup val

namespace Finset

def mem (a : α) (s : Finset α) : Prop := a ∈ s.val

instance : Membership α (Finset α) := ⟨mem⟩

def card (s : Finset α) : ℕ := s.val.length

-- Basic finite types
instance : Fintype Empty where
  elems := ⟨[], List.nodup_nil⟩
  complete := fun a => Empty.rec a

instance : Fintype Unit where
  elems := ⟨[()], by simp [List.Nodup]⟩
  complete := fun _ => by simp [mem]

instance : Fintype Bool where
  elems := ⟨[true, false], by simp [List.Nodup]⟩
  complete := fun b => by cases b <;> simp [mem]

-- Finite natural numbers
def range (n : ℕ) : Finset ℕ := ⟨List.range n, List.nodup_range n⟩

instance (n : ℕ) : Fintype (Fin n) where
  elems := ⟨List.finRange n, List.nodup_finRange n⟩
  complete := fun i => List.mem_finRange.mpr i.isLt

end Finset
