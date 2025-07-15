import Lake
open Lake DSL

package particles where
  -- Recognition Science: Unified Architecture
  -- Core Mathematical Foundations
  -- Zero axioms, zero free parameters, sub-percent accuracy

-- Essential dependencies only - no proofwidgets
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation" @ "main"

-- Mathematical infrastructure
lean_lib Imports where
  -- Mathematical foundations based on verified Mathlib

-- Core Recognition Science modules
lean_lib Core where
  -- Meta-principle, eight foundations, core theory

-- Computational verification
lean_lib Computation where
  -- Verified numerical computations (zero sorries)

-- Supporting modules
lean_lib Foundations where
  -- Foundation implementations

lean_lib Parameters where
  -- Parameter and constant definitions

-- Main libraries
lean_lib ParticleMasses where
  -- Particle mass predictions from φ-cascade

lean_lib ZeroAxiomFoundation where
  -- Zero-axiom mathematical foundation

-- Additional targets
lean_lib Fintype where
  -- Finite type theory

lean_lib Particles where
  -- Particle physics applications

-- Integration testing
lean_exe test_integration where
  root := `test_integration
