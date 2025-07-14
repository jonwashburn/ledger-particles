import Lake
open Lake DSL

package particles where
  -- Recognition Science: Parameter-Free Particle Mass Derivation
  -- Phase 1: Demonstrate build system works (Mathlib to be added back in Phase 2)
  -- Zero axioms, zero free parameters, sub-percent accuracy

-- Temporarily avoiding Mathlib due to proofwidgets conflicts on macOS
-- Will restore in Phase 2 once core build issues are resolved

lean_lib Imports where
  -- Mathematical infrastructure for Recognition Science

lean_lib ParticleMasses where
  -- Main library for particle mass calculations from φ-cascade

lean_lib RecognitionScience where
  -- Core Recognition Science framework and meta-principle

lean_lib ZeroAxiomFoundation where
  -- Zero-axiom mathematical foundation (self-contained)

lean_lib MinimalFoundation where
  -- Minimal foundation providing the eight foundations

lean_lib Core where
  -- Core Recognition Science modules

lean_lib Foundations where
  -- Eight foundations implementation

-- Physics modules
lean_lib Physics where
  srcDir := "Core/Physics"
