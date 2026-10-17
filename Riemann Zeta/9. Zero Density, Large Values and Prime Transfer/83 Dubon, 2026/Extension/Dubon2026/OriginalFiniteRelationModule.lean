import Dubon2026.OriginalRelationModuleSequence
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The original finite relation module is an integral lattice

For the finite coefficient in the class/Ext argument, the actual kernel
of its free cover is a finite free integral module. Reuse the pinned
Noetherian submodule and PID theorems, supplying the lattice input for
the relation-module extension criterion needed by DUB-17.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Finite B]

/-- The genuine relation module of a finite coefficient over a finite group is finitely generated over the integers. -/
theorem originalRelationModule_finite : Module.Finite ℤ (originalRelationModule B) := by
  letI : Module.Finite ℤ (Rep.free ℤ G B) := by
    change Module.Finite ℤ (B →₀ G →₀ ℤ)
    infer_instance
  change Module.Finite ℤ (LinearMap.ker (originalRelationFreeCover B).hom.toLinearMap)
  infer_instance

/-- The genuine finite relation module is free over the integers by the PID theorem, not a supplied lattice certificate. -/
theorem originalRelationModule_free : Module.Free ℤ (originalRelationModule B) := by
  letI := originalRelationModule_finite B
  change Module.Free ℤ (LinearMap.ker (originalRelationFreeCover B).hom.toLinearMap)
  infer_instance

end
end Dubon2026
