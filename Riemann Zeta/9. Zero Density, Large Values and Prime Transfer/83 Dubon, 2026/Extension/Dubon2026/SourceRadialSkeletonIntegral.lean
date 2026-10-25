import Dubon2026.SourceRadialEdgeSkeleton

/-! DUB-17/18 -> cover reciprocity -> actual cycle integrals.
These three path laws are the exact inputs used by the native tree-walk
argument. They will be discharged by the already proved cover integral laws
for each differential regular on the actual skeleton. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

/-- The elementary integral laws on paths in the actual skeleton. -/
structure SkeletonIntegral (D : RadialCellDissection X)
    (I : {P Q : X} → Path P Q → ℂ) : Prop where
  refl : ∀ P ∈ D.skeleton, I (Path.refl P) = 0
  symm : ∀ {P Q} (p : Path P Q), (∀ t, p t ∈ D.skeleton) → I p.symm = -I p
  trans : ∀ {P Q R} (p : Path P Q) (q : Path Q R),
    (∀ t, p t ∈ D.skeleton) → (∀ t, q t ∈ D.skeleton) → I (p.trans q) = I p + I q

theorem integral_cast (I : {P Q : X} → Path P Q → ℂ)
    {P Q P' Q' : X} (p : Path P Q) (hP : P' = P) (hQ : Q' = Q) :
    I (p.cast hP hQ) = I p := by
  subst hP
  subst hQ
  rfl

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialEdgePaths
