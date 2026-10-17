import Dubon2026.OriginalArbitraryPIDSubmodule
import Dubon2026.OriginalRelationModuleSequence

/-! # Integral freeness of the literal arbitrary relation kernel

This discharges the integral freeness input for the actual infinite
arithmetic fundamental coefficient on DUB-17's duality route.
It does not assert projectivity over the integral group ring.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

/-- The literal kernel of the actual free cover is free over the integers, without finite coefficient or finite rank assumptions. -/
theorem originalArbitraryRelationModule_free {G : Type} [Group G] (B : Rep ℤ G) :
    Module.Free ℤ (originalRelationModule B) := by
  letI : Module.Free ℤ (Rep.free ℤ G B) := by
    change Module.Free ℤ (B →₀ G →₀ ℤ)
    infer_instance
  change Module.Free ℤ (LinearMap.ker (originalRelationFreeCover B).hom.toLinearMap)
  exact originalSubmodule_free_of_free_over_PID _

end
end Dubon2026
