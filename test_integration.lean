/-
Integration Test for Recognition Science Unified Architecture
=============================================================

This file tests that all modules in the unified architecture
import and work correctly together.
-/

-- Test Core module imports
import Core

-- Test individual module imports
import RecognitionScience
import ParticleMasses
import ZeroAxiomFoundation
import MinimalFoundation

-- Test that key definitions exist
#check φ  -- Golden ratio
#check E_coh  -- Coherence quantum
#check mass  -- Mass function

-- Test that core theorems are accessible
#check golden_ratio_minimal_cost  -- Should exist from foundations
#check zero_axiom_foundation  -- Should exist from ZeroAxiomFoundation

-- Test namespace organization
namespace RecognitionScience

-- Test that we can access unified content
#check Core.φ  -- Should be accessible
#check Core.E_coh  -- Should be accessible

end RecognitionScience

-- Integration test passed if this file compiles
def integration_test_passed : Bool := true

#check integration_test_passed
