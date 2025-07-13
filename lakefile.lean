import Lake
open Lake DSL

package «ledger-particles» where
  -- Recognition Science: Parameter-Free Particle Mass Derivation
  -- Zero axioms, zero free parameters, sub-percent accuracy

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "main"

-- Self-contained Recognition Science implementation
-- All foundations included directly in this repository

@[default_target]
lean_lib «MinimalFoundation» where
  -- Minimal foundation providing the eight foundations

@[default_target]
lean_lib «ParticleMasses» where
  -- Main library for particle mass calculations from φ-cascade

@[default_target]
lean_lib «RecognitionScience» where
  -- Core Recognition Science framework and meta-principle

@[default_target]
lean_lib «ZeroAxiomFoundation» where
  -- Zero-axiom mathematical foundation (self-contained)
