import Dubon2026.NumberFieldSupportedIdeleGaloisAction
import Dubon2026.NumberFieldGaloisStableIdeleSupport

/-! # The constructed original equivariant supported-idele exact sequence

For every prescribed finite support, the actual finite Galois orbit
enlargement supplies the original injective principal S-unit map,
its exact image kernel, the surjective original idele-class map and
equivariance for both maps. This closes the algebraic sequence input
to DUB-17's Herbrand-quotient and global norm-index argument; those
cohomological and reciprocity conclusions are not asserted here.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- A constructed finite stable support supplies the exact original sequence with both actual equivariance laws. -/
theorem numberField_exists_equivariant_supported_idele_sequence
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v,
        v ∈ (S : Set (HeightOneSpectrum (𝓞 L))) ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
      Function.Injective (numberFieldSupportedPrincipalIdele L S) ∧
      (numberFieldSupportedIdeleClassMap L S).ker =
        (numberFieldSupportedPrincipalIdele L S).range ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
      (letI := numberFieldSUnitGaloisAction K L S hS
       letI := numberFieldSupportedIdeleGaloisAction K L S hS
       ∀ (σ : Gal(L/K)) (x : (S : Set (HeightOneSpectrum (𝓞 L))).unit L),
         numberFieldSupportedPrincipalIdele L S (σ • x) =
           σ • numberFieldSupportedPrincipalIdele L S x) ∧
      (letI := numberFieldSupportedIdeleGaloisAction K L S hS
       letI := numberFieldIdeleClassGaloisAction K L
       ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
         numberFieldSupportedIdeleClassMap L S (σ • a) =
           σ • numberFieldSupportedIdeleClassMap L S a) := by
  obtain ⟨S, hS₀, hS, hsurj⟩ := numberField_exists_galoisStable_idele_support K L S₀
  exact ⟨S, hS₀, hS, numberFieldSupportedPrincipalIdele_injective L S,
    numberFieldSupportedIdeleClassMap_ker L S, hsurj,
    numberFieldSupportedPrincipalIdele_galois K L S hS,
    numberFieldSupportedIdeleClassMap_galois K L S hS⟩

end
end Dubon2026
