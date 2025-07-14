/-
  Recognition Science: Core Kernel
  ================================

  Minimal kernel for Recognition Science.
-/

import Core.MetaPrincipleMinimal

namespace RecognitionScience.Kernel

open Core.MetaPrincipleMinimal

def MetaPrinciple : Prop := Core.MetaPrincipleMinimal.MetaPrinciple

theorem meta_principle_holds : MetaPrinciple :=
  Core.MetaPrincipleMinimal.meta_principle_holds

end RecognitionScience.Kernel
