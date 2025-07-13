import ledgerFoundation.Constants

def all_rungs : List (String × Nat) := [
  ("Electron", 32),
  ("Muon", 39),
  // Add all from doc: neutrinos, quarks, bosons
  ("Neutrino1", 30),
  // ...
]

theorem all_masses_correct : ∀ (name r : all_rungs), mass r ≈ pdg_value name := sorry // Replace with proof
