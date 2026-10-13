import Dubon2026.OriginalDecompositionTower

/-! # Original prime restriction along the actual Kummer inclusion

The prescribed field and the S-unit Kummer field are both subfields of the
same ambient algebraic closure. Their inclusion supplies an actual algebra
tower, rather than a nested subtype. This version of original prime
restriction consumes precisely that inclusion and proves splitting in the
original prescribed field, avoiding transport through a replacement prime
space. It serves the same-field assembly of DUB-17's selected-prime theorem.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K L] [IsGalois K E]

omit [NumberField K] [NumberField E] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Contraction of actual original primes commutes with normal restriction. -/
theorem originalFinitePrimeBelow_restrictNormal_algebraTower
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
    change algebraMap E L (AlgEquiv.restrictNormalHom E σ.symm (a : E)) = σ.symm (algebraMap E L (a : E)) at h
    rw [he] at h
    exact h.symm
  rw [ha]

omit [NumberField K] [NumberField L] in
/-- Every automorphism fixing the lower original prime lifts to one fixing
the given upper original prime. -/
theorem originalFiniteDecomposition_restrict_surjective_algebraTower
    (w : HeightOneSpectrum (𝓞 L))
    (τ : Gal(E/K)) (hτ : τ ∈ OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w)) :
    ∃ σ : Gal(L/K), σ ∈ OriginalFiniteDecompositionGroup K L w ∧
      AlgEquiv.restrictNormalHom E σ = τ := by
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  letI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := E) L τ
  have hBelow : originalFinitePrimeBelow E L (numberFieldGaloisPlaceEquiv K L σ w) =
      originalFinitePrimeBelow E L w := by
    rw [originalFinitePrimeBelow_restrictNormal_algebraTower K E L, hσ]
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
      apply (algebraMap E L).injective
      change algebraMap E L ((ρ.restrictScalars K).restrictNormal E a) = algebraMap E L a
      rw [AlgEquiv.restrictNormal_commutes]
      exact ρ.commutes a
    rw [hρone, one_mul]

omit [NumberField K] [NumberField L] in
/-- Containment of the upper original stabilizer in the normal restriction
kernel forces trivial decomposition in the original subextension. -/
theorem originalFiniteDecomposition_below_eq_bot_of_le_ker_algebraTower
    (w : HeightOneSpectrum (𝓞 L))
    (hD : OriginalFiniteDecompositionGroup K L w ≤ (AlgEquiv.restrictNormalHom E).ker) :
    OriginalFiniteDecompositionGroup K E (originalFinitePrimeBelow E L w) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro τ hτ
  obtain ⟨σ, hσ, hRestrict⟩ := originalFiniteDecomposition_restrict_surjective_algebraTower K E L w τ hτ
  have he := hD hσ
  change AlgEquiv.restrictNormalHom E σ = 1 at he
  exact Subgroup.mem_bot.mpr (hRestrict.symm.trans he)

end
end Dubon2026
