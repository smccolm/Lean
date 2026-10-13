import Dubon2026.OriginalDecompositionTower

/-! # Restriction of the original prime stabilizers

Restriction of automorphisms commutes with contraction of the original
prime ideals. Lifting a lower stabilizer and adjusting it in the actual
upper-prime orbit makes the decomposition restriction surjective. Thus
containment in the original restriction kernel forces splitting in the
prescribed subextension, as required by DUB-17's prime-selection argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Contraction of actual original primes commutes with normal restriction. -/
theorem originalFinitePrimeBelow_restrictNormal
    (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    originalFinitePrimeBelow E L (numberFieldGaloisPlaceEquiv K L σ w) =
      numberFieldGaloisPlaceEquiv K E (AlgEquiv.restrictNormalHom E σ)
        (originalFinitePrimeBelow E L w) := by
  apply HeightOneSpectrum.ext
  ext a
  change NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
    (algebraMap (𝓞 E) (𝓞 L) a) ∈ w.asIdeal ↔
    algebraMap (𝓞 E) (𝓞 L)
      (NumberField.RingOfIntegers.mapRingHom
        (AlgEquiv.restrictNormalHom E σ).symm.toRingHom a) ∈ w.asIdeal
  have ha : NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
      (algebraMap (𝓞 E) (𝓞 L) a) =
      algebraMap (𝓞 E) (𝓞 L) (NumberField.RingOfIntegers.mapRingHom
        (AlgEquiv.restrictNormalHom E σ).symm.toRingHom a) := by
    apply NumberField.RingOfIntegers.ext
    have h := AlgEquiv.restrictNormal_commutes σ.symm E (a : E)
    have he : AlgEquiv.restrictNormalHom E σ.symm =
        (AlgEquiv.restrictNormalHom E σ).symm := map_inv (AlgEquiv.restrictNormalHom E) σ
    change (AlgEquiv.restrictNormalHom E σ.symm (a : E) : L) = σ.symm (a : L) at h
    rw [he] at h
    exact h.symm
  rw [ha]

omit [NumberField L] in
/-- Every automorphism fixing the lower original prime lifts to one fixing
the given upper original prime. -/
theorem originalFiniteDecomposition_restrict_surjective
    (w : HeightOneSpectrum (𝓞 L))
    (τ : Gal(E/K)) (hτ : τ ∈ OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w)) :
    ∃ σ : Gal(L/K), σ ∈ OriginalFiniteDecompositionGroup K L w ∧
      AlgEquiv.restrictNormalHom E σ = τ := by
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := E) L τ
  have hBelow : originalFinitePrimeBelow E L (numberFieldGaloisPlaceEquiv K L σ w) =
      originalFinitePrimeBelow E L w := by
    rw [originalFinitePrimeBelow_restrictNormal K L E, hσ]
    exact hτ
  obtain ⟨ρ, hρ⟩ := (originalFinitePrimeBelow_eq_iff_orbit E L
    (numberFieldGaloisPlaceEquiv K L σ w) w).mp hBelow
  refine ⟨ρ.restrictScalars K * σ, ?_, ?_⟩
  · change numberFieldGaloisPlaceEquiv K L (ρ.restrictScalars K * σ) w = w
    rw [numberFieldGaloisPlaceEquiv_mul, originalFinitePlace_restrictScalars]
    exact hρ
  · rw [map_mul, hσ]
    have hρone : AlgEquiv.restrictNormalHom E (ρ.restrictScalars K) = 1 := by
      apply AlgEquiv.ext
      intro a
      apply E.val.injective
      change (AlgEquiv.restrictNormalHom E (ρ.restrictScalars K) a : L) = (a : L)
      rw [AlgEquiv.restrictNormalHom_apply]
      exact ρ.commutes a
    rw [hρone, one_mul]

omit [NumberField L] in
/-- Containment of the upper original stabilizer in the normal restriction
kernel forces trivial decomposition in the original subextension. -/
theorem originalFiniteDecomposition_below_eq_bot_of_le_ker
    (w : HeightOneSpectrum (𝓞 L))
    (hD : OriginalFiniteDecompositionGroup K L w ≤ (AlgEquiv.restrictNormalHom E).ker) :
    OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro τ hτ
  obtain ⟨σ, hσ, hRestrict⟩ := originalFiniteDecomposition_restrict_surjective K L E w τ hτ
  have he := hD hσ
  change AlgEquiv.restrictNormalHom E σ = 1 at he
  exact Subgroup.mem_bot.mpr (hRestrict.symm.trans he)

end
end Dubon2026
