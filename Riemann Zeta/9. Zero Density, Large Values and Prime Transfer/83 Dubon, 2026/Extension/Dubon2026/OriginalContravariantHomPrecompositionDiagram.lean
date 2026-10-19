import Dubon2026.OriginalContravariantHomSequence

/-! A genuine map of original presentations induces the reversed dual
diagram. Applied to the native relation group-change/tower diagram, this
compares the local connecting classes before and after finite correction
descent, the next dependency in DUB-17's prescribed local recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2
variable {G : Type} [Group G]
  (X Y : ShortComplex (Rep.{0} ℤ G)) (D : Rep.{0} ℤ G)

/-- Precomposition with the actual presentation map gives a commuting
diagram of original dual sequences, retaining all three component maps. -/
def originalContravariantHomPrecompositionDiagram (f : X ⟶ Y) :
    originalContravariantHomShortComplex Y D ⟶
      originalContravariantHomShortComplex X D where
  τ₁ := originalInternalHomPrecomposition D f.τ₃
  τ₂ := originalInternalHomPrecomposition D f.τ₂
  τ₃ := originalInternalHomPrecomposition D f.τ₁
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro η
    change Y.X₃ →ₗ[ℤ] D at η
    apply LinearMap.ext
    intro x
    exact congrArg η (congrArg (fun m => m.hom x) f.comm₂₃).symm
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro η
    change Y.X₂ →ₗ[ℤ] D at η
    apply LinearMap.ext
    intro x
    exact congrArg η (congrArg (fun m => m.hom x) f.comm₁₂).symm

end
end Dubon2026
