import Dubon2026.OriginalClassOutsideH2TowerSquare
import Dubon2026.OriginalClassesModOutsideH2Comparison

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E L w ∈ S)


/-- Actual finite class H2 inflation remains injective after taking the
outside-unit quotients, using their proved original H2 isomorphisms. -/
theorem originalClassesModOutsideH2Inflation_injective
    (huE : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (huL : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Injective (groupCohomology.map
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
      (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST) 2) := by
  letI : FiniteDimensional K E := FiniteDimensional.left K E L
  let eE := originalClassesModOutsideH2Iso K E S hS huE
  let eL := originalClassesModOutsideH2Iso K L T hT huL
  intro x y hxy
  obtain ⟨u, rfl⟩ := eE.toLinearEquiv.surjective x
  obtain ⟨v, rfl⟩ := eE.toLinearEquiv.surjective y
  apply congrArg eE.toLinearEquiv
  apply originalIdeleClassH2Inflation_injective K E L
  apply eL.toLinearEquiv.injective
  exact (originalClassOutsideH2_tower_square K E L S T hS hT hST u).symm.trans
    (hxy.trans (originalClassOutsideH2_tower_square K E L S T hS hT hST v))

end
end Dubon2026
