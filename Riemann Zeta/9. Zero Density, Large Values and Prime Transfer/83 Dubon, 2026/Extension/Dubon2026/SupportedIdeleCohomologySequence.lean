import Dubon2026.SupportedIdeleRepresentations

/-! # The actual supported-idele sequence in original cohomology

The original principal S-unit and class maps form a representation
complex, and their already proved kernel and surjectivity results give
short exactness. The existing support-enlargement theorem constructs
such a finite stable support above any prescribed one. This provides
the actual original sequence required to combine the S-unit and
supported-idele cohomological factors in DUB-17's norm-index argument.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original principal S-units, supported ideles and idele classes form this actual representation complex. -/
def originalSupportedIdeleShortComplex : ShortComplex (Rep ℤ Gal(L/K)) where
  X₁ := sUnitOriginalRep K L S hS
  X₂ := originalSupportedIdeleRep K L S hS
  X₃ := originalIdeleClassRep K L
  f := originalSupportedPrincipalRepHom K L S hS
  g := originalSupportedClassRepHom K L S hS
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change numberFieldSupportedPrincipalIdele L S x.toMul ∈ (numberFieldSupportedIdeleClassMap L S).ker
    rw [numberFieldSupportedIdeleClassMap_ker]
    exact ⟨x.toMul, rfl⟩

/-- The exact original kernel and actual supported class surjection prove short exactness of the original coefficient sequence. -/
theorem originalSupportedIdeleShortComplex_shortExact
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S)) :
    (originalSupportedIdeleShortComplex K L S hS).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr ?_
    epi_g := (Rep.epi_iff_surjective _).mpr ?_ }
  · apply ((originalSupportedIdeleShortComplex K L S hS).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext a
    change (∃ x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L),
      Additive.ofMul (numberFieldSupportedPrincipalIdele L S x.toMul) = a) ↔
        numberFieldSupportedIdeleClassMap L S a.toMul = 1
    change _ ↔ a.toMul ∈ (numberFieldSupportedIdeleClassMap L S).ker
    rw [numberFieldSupportedIdeleClassMap_ker]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.toMul, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  · intro x y h
    apply Additive.toMul.injective
    exact numberFieldSupportedPrincipalIdele_injective L S (congrArg Additive.toMul h)
  · intro a
    obtain ⟨x, hx⟩ := hsurj a.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-- Every prescribed original support has a constructed finite stable enlargement giving an actual short exact supported-idele representation sequence. -/
theorem original_exists_supportedIdele_shortExact [FiniteDimensional K L]
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      ∃ hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S,
        (originalSupportedIdeleShortComplex K L S hS).ShortExact := by
  obtain ⟨S, hsub, hS, hsurj⟩ := numberField_exists_galoisStable_idele_support K L S₀
  exact ⟨S, hsub, hS, originalSupportedIdeleShortComplex_shortExact K L S hS hsurj⟩

end
end Dubon2026
