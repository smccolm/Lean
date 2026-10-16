import Dubon2026.OriginalIntegerPrimeTower

/-! # Original primes over a rational prime form the actual Galois orbit

Reuse the pinned integral Galois prime-transitivity theorem directly over
the integers. This is the prime-surjectivity input for indexing DUB-17's
Mackey summands through a finite Galois cover of the original global field;
the actual local restriction/decomposition comparison remains separate.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (L : Type) [Field L] [NumberField L] [Algebra ℚ L]

/-- Integral Galois restriction over the original integers is the literal original integer-ring automorphism. -/
theorem originalRationalIntegerGalRestrict_eq (σ : Gal(L/ℚ)) :
    (galRestrict ℤ ℚ L (𝓞 L) σ).toRingHom =
      (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingHom := by
  ext r
  exact algebraMap_galRestrict_apply ℤ σ r

/-- The actual rational integer prime below a finite place is unchanged by the original Galois action. -/
theorem originalIntegerPrimeBelow_rationalGalois (σ : Gal(L/ℚ)) (w : HeightOneSpectrum (𝓞 L)) :
    originalIntegerPrimeBelow L (numberFieldGaloisPlaceEquiv ℚ L σ w) = originalIntegerPrimeBelow L w := by
  apply HeightOneSpectrum.ext
  ext r
  change NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
    (algebraMap ℤ (𝓞 L) r) ∈ w.asIdeal ↔ algebraMap ℤ (𝓞 L) r ∈ w.asIdeal
  have hr : NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
      (algebraMap ℤ (𝓞 L) r) = algebraMap ℤ (𝓞 L) r := by
    apply NumberField.RingOfIntegers.ext
    exact map_intCast σ.symm r
  rw [hr]

/-- Over a finite Galois rational field, equality of the original integer prime below is exactly membership in the original Galois orbit. -/
theorem originalIntegerPrimeBelow_eq_iff_rationalOrbit [IsGalois ℚ L]
    (w₁ w₂ : HeightOneSpectrum (𝓞 L)) :
    originalIntegerPrimeBelow L w₁ = originalIntegerPrimeBelow L w₂ ↔
      ∃ σ : Gal(L/ℚ), numberFieldGaloisPlaceEquiv ℚ L σ w₁ = w₂ := by
  constructor
  · intro h
    let p := (originalIntegerPrimeBelow L w₁).asIdeal
    haveI : w₁.asIdeal.LiesOver p := ⟨rfl⟩
    haveI : w₂.asIdeal.LiesOver p := by
      rw [show p = (originalIntegerPrimeBelow L w₂).asIdeal from congrArg HeightOneSpectrum.asIdeal h]
      exact ⟨rfl⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq ℤ ℚ L (𝓞 L)
      (p := p) (P₁ := w₂.asIdeal) (P₂ := w₁.asIdeal) ⟨inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance⟩
    refine ⟨σ, HeightOneSpectrum.ext ?_⟩
    rw [numberFieldGaloisPlaceEquiv_asIdeal]
    have hh := congrArg (Ideal.map (galRestrict ℤ ℚ L (𝓞 L) σ)) hσ
    rw [Ideal.map_comap_of_surjective _ (galRestrict ℤ ℚ L (𝓞 L) σ).surjective] at hh
    change Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingHom w₁.asIdeal = w₂.asIdeal
    rw [← originalRationalIntegerGalRestrict_eq L σ]
    exact hh.symm
  · rintro ⟨σ, rfl⟩
    exact (originalIntegerPrimeBelow_rationalGalois L σ w₁).symm

end
end Dubon2026
