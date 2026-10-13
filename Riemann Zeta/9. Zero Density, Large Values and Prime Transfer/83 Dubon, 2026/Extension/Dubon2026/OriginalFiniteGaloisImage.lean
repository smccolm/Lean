import Dubon2026.OriginalFiniteGaloisContinuousInflation
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # The literal image of an original finite Galois field

This retains the original field inside the closure used by the normalized
local invariant. The equivalence and scalar towers are constructed from
the actual embedding, so the local character pairing does not require an
independent image or compatibility premise on DUB-17's sum-zero route.
-/
namespace Dubon2026
noncomputable section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L]

/-- The genuine finite Galois image of the original coefficient field in the same ambient field. -/
def originalFiniteGaloisImage : FiniteGaloisIntermediateField K Ω := by
  let φ := IsScalarTower.toAlgHom K L Ω
  let F := φ.fieldRange
  let e : L ≃ₐ[K] F := AlgEquiv.ofInjective φ φ.injective
  letI : FiniteDimensional K F := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K F := IsGalois.of_algEquiv e
  exact ⟨F⟩

/-- The original field identifies with its actual embedded image. -/
def originalFiniteGaloisImageEquiv : L ≃ₐ[K] originalFiniteGaloisImage K L Ω :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω) (IsScalarTower.toAlgHom K L Ω).injective

/-- The image equivalence preserves the literal original embedding. -/
theorem originalFiniteGaloisImageEquiv_algebraMap (x : L) :
    algebraMap (originalFiniteGaloisImage K L Ω) Ω
      (originalFiniteGaloisImageEquiv K L Ω x) = algebraMap L Ω x := rfl

/-- The actual image of an original cyclic Galois field still has cyclic Galois group. -/
theorem originalFiniteGaloisImage_isCyclic [IsCyclic Gal(L/K)] :
    IsCyclic Gal(originalFiniteGaloisImage K L Ω/K) := by
  exact (originalFiniteGaloisImageEquiv K L Ω).autCongr.isCyclic.mp inferInstance

/-- The original image equivalence supplies the actual original scalar action. -/
abbrev originalFiniteGaloisImageAlgebra : Algebra L (originalFiniteGaloisImage K L Ω) :=
  (originalFiniteGaloisImageEquiv K L Ω).toRingHom.toAlgebra

/-- The constructed image embedding retains the original base-field scalar tower. -/
theorem originalFiniteGaloisImage_baseTower :
    letI := originalFiniteGaloisImageAlgebra K L Ω
    IsScalarTower K L (originalFiniteGaloisImage K L Ω) := by
  letI := originalFiniteGaloisImageAlgebra K L Ω
  exact IsScalarTower.of_algHom (originalFiniteGaloisImageEquiv K L Ω).toAlgHom

/-- The constructed image embedding retains the literal original ambient embedding. -/
theorem originalFiniteGaloisImage_ambientTower :
    letI := originalFiniteGaloisImageAlgebra K L Ω
    IsScalarTower L (originalFiniteGaloisImage K L Ω) Ω := by
  letI := originalFiniteGaloisImageAlgebra K L Ω
  exact IsScalarTower.of_algebraMap_eq' rfl

end
end Dubon2026
