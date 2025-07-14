import Lake
open Lake DSL

package particles where
  -- Recognition Science: Parameter-Free Particle Mass Derivation
  -- Phase 2: Adding Mathlib support for complete mathematical proofs
  -- Zero axioms, zero free parameters, sub-percent accuracy

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Imports where
  -- Mathematical infrastructure based on verified Mathlib

lean_lib ParticleMasses where
  -- Main library for particle mass calculations from φ-cascade

lean_lib RecognitionScience where
  -- Core Recognition Science framework and meta-principle

lean_lib ZeroAxiomFoundation where
  -- Zero-axiom mathematical foundation (self-contained)

lean_lib MinimalFoundation where
  -- Minimal foundation providing the eight foundations

lean_lib Computation where
  -- Verified numerical computations and proofs

lean_lib Core where
  -- Core Recognition Science modules

lean_lib Foundations where
  -- Eight foundations implementation

-- Physics modules
lean_lib Physics where
  srcDir := "Core/Physics"
