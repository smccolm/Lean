import Dubon2026.OriginalRelationGroupChange
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! The canonical free presentation map for an actual group isomorphism
is invertible. This is used to carry the original ambient-stage Cartier
extension back to its literal image field in the arithmetic union, before
the proved source-class lift and S-unit correction on DUB-17's chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G H : Type} [Group G] [Group H] (e : G ≃* H) (B : Rep.{0} ℤ H)

/-- The actual canonical map of free relation covers under a group
isomorphism is the usual reindexing equivalence on the group coordinates. -/
theorem originalRelationFreeGroupChange_bijective :
    Function.Bijective (originalRelationFreeGroupChange e.toMonoidHom B).hom := by
  let l : (B →₀ G →₀ ℤ) ≃ₗ[ℤ] (B →₀ H →₀ ℤ) :=
    Finsupp.mapRange.linearEquiv (Finsupp.domLCongr e.toEquiv)
  have h : (originalRelationFreeGroupChange e.toMonoidHom B).hom.toLinearMap = l.toLinearMap := by
    ext b g
    simp [originalRelationFreeGroupChange, Rep.freeLift, Representation.freeLift, l]
  exact (congrArg (fun m : (B →₀ G →₀ ℤ) →ₗ[ℤ] (B →₀ H →₀ ℤ) =>
    Function.Bijective m) h).mpr l.bijective

end
end Dubon2026
