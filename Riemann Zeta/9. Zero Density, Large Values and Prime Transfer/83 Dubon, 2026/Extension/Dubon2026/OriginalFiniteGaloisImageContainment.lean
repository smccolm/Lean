import Dubon2026.OriginalFiniteGaloisImage

/-! # Original finite images retain the containing field

The two-primary cyclic descent supplies a subfield of a full cyclotomic
field. Their actual images in the arithmetic union retain that inclusion.
DUB-17 needs it to apply the proved conductor-two principal identity to
the descended class without assuming that the full cyclotomic field is cyclic.
-/
namespace Dubon2026
noncomputable section

variable (K E F Ω : Type) [Field K] [Field E] [Field F] [Field Ω]
  [Algebra K E] [Algebra K F] [Algebra K Ω]
  [Algebra E F] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower K E Ω] [IsScalarTower K F Ω]
  [IsScalarTower E F Ω] [FiniteDimensional K E] [FiniteDimensional K F]
  [IsGalois K E] [IsGalois K F]

/-- Literal finite Galois images preserve the original scalar-tower inclusion. -/
theorem originalFiniteGaloisImage_le_of_tower :
    (originalFiniteGaloisImage K E Ω).toIntermediateField ≤
      (originalFiniteGaloisImage K F Ω).toIntermediateField := by
  intro z hz
  change z ∈ (IsScalarTower.toAlgHom K E Ω).fieldRange at hz
  obtain ⟨x, rfl⟩ := hz
  change ∃ y : F, (IsScalarTower.toAlgHom K F Ω) y = (IsScalarTower.toAlgHom K E Ω) x
  exact ⟨algebraMap E F x, (IsScalarTower.algebraMap_apply E F Ω x).symm⟩

end
end Dubon2026
