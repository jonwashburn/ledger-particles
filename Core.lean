/-
Recognition Science: Core Module Collection
==========================================

This file imports all core Recognition Science modules for unified access.
Part of Phase 3 architecture unification.

Author: Recognition Science Implementation Team
-/

-- Fundamental Core Modules
import Core.Kernel
import Core.Arith
import Core.Constants
import Core.Finite

-- Advanced Core Theory
import Core.MetaPrinciple
import Core.EightFoundations
import Core.ConstantsFromFoundations
import Core.Representation

-- Specialized Modules
import Core.Nat.Card
import Core.Physics.MassGap
import Core.Physics.RungGap

-- Re-export key namespaces for convenient access
export Core.MetaPrinciple
export Core.EightFoundations
export Core.Physics
