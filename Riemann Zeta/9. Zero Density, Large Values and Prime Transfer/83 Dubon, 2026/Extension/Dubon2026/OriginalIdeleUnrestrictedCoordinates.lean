import Dubon2026.OriginalIdeleH2SupportedLift
import Dubon2026.OriginalSupportedH2Unrestricted

/-! # Literal unrestricted coordinates of original full ideles

The original full idele coefficient maps to the existing local completion
product on any stable finite support. This agrees with supported inclusion
and unrestricted projection, providing the source-entry comparison for
DUB-17's global H2 detection and arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual original full-idele coordinate at an unrestricted original place. -/
def originalFullUnrestrictedCoordinate (p : SUnitLogPlace L S) :
    originalFullIdeleRep K L →ₗ[ℤ] supportedUnrestrictedUnitModule L S p := by
  cases p with
  | inl w => exact (numberFieldIdeleInfiniteComponent L w).toAdditive.toIntLinearMap
  | inr w => exact (numberFieldIdeleFiniteComponent L w.val).toAdditive.toIntLinearMap

/-- The original full idele coefficient mapped to its actual unrestricted local coordinates. -/
def originalFullUnrestrictedRepHom :
    originalFullIdeleRep K L ⟶ supportedUnrestrictedUnitRep K L S hS := by
  letI := sUnitLogPlaceAction K L S hS
  refine Rep.ofHom ⟨LinearMap.pi (originalFullUnrestrictedCoordinate K L S), ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  funext p
  cases p with
  | inl w =>
    apply Additive.toMul.injective
    apply Units.ext
    exact numberFieldInfiniteAdeleGaloisMap_apply K L σ a.toMul.val.1
      (σ⁻¹ • w) w (smul_inv_smul σ w)
  | inr w =>
    letI := sUnitStableFinitePlaceAction K L S hS
    apply Additive.toMul.injective
    apply Units.ext
    exact numberFieldFiniteAdeleGaloisMap_apply K L σ a.toMul.val.2
      (σ⁻¹ • w).val w.val (congrArg Subtype.val (smul_inv_smul σ w))

/-- Supported inclusion followed by actual full-idele coordinates equals the original unrestricted projection. -/
theorem originalSupportedFull_unrestricted_composition :
    originalSupportedFullIdeleInclusion K L S hS ≫ originalFullUnrestrictedRepHom K L S hS =
      originalSupportedUnrestrictedProjection K L S hS := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  funext p
  cases p <;> rfl

end
end Dubon2026
