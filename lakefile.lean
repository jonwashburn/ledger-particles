import Lake
open Lake DSL

package «ledger-particles» where
  -- Recognition Science: Parameter-Free Particle Mass Derivation

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib «ParticleMasses» where
  -- Main library for particle mass calculations
