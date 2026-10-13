import Dubon2026.NumberFieldSupportedIdeleEquivariantSequence
import Dubon2026.SUnitLogarithmicRepresentation

/-! # The original supported ideles and idele classes as representations

The existing original Galois actions on units of the actual adele ring
and its principal quotient define the coefficient representations. The
proved original equivariance laws make the same principal S-unit and
class maps morphisms of these representations. This is the required
entry into original cohomology for DUB-17's global norm-index argument.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original actual idele-class coefficient representation. -/
def originalIdeleClassRep : Rep ℤ Gal(L/K) := by
  letI := numberFieldIdeleClassGaloisAction K L
  exact Rep.ofMulDistribMulAction Gal(L/K) (OriginalNumberFieldIdeleClassGroup L)

/-- The original actual supported-idele coefficient representation. -/
def originalSupportedIdeleRep : Rep ℤ Gal(L/K) := by
  letI := numberFieldSupportedIdeleGaloisAction K L S hS
  exact Rep.ofMulDistribMulAction Gal(L/K) (numberFieldSupportedIdeles L S)

/-- The actual principal S-unit inclusion as an original representation morphism. -/
def originalSupportedPrincipalRepHom :
    sUnitOriginalRep K L S hS ⟶ originalSupportedIdeleRep K L S hS :=
  Rep.ofHom ⟨(numberFieldSupportedPrincipalIdele L S).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (numberFieldSupportedPrincipalIdele_galois K L S hS σ x.toMul)⟩

/-- The actual supported class projection as an original representation morphism. -/
def originalSupportedClassRepHom :
    originalSupportedIdeleRep K L S hS ⟶ originalIdeleClassRep K L :=
  Rep.ofHom ⟨(numberFieldSupportedIdeleClassMap L S).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (numberFieldSupportedIdeleClassMap_galois K L S hS σ x.toMul)⟩

/-- The representation inclusion is the literal original principal S-unit map. -/
theorem originalSupportedPrincipalRepHom_apply
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    (originalSupportedPrincipalRepHom K L S hS).hom x =
      Additive.ofMul (numberFieldSupportedPrincipalIdele L S x.toMul) := rfl

/-- The representation projection is the literal original supported-idele class map. -/
theorem originalSupportedClassRepHom_apply (x : Additive (numberFieldSupportedIdeles L S)) :
    (originalSupportedClassRepHom K L S hS).hom x =
      Additive.ofMul (numberFieldSupportedIdeleClassMap L S x.toMul) := rfl

end
end Dubon2026
