import Dubon2026.NumberFieldGaloisPlaces
import Dubon2026.FinitePrimeBaseChange
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Original base primes and original Galois orbits

The local fixed-field descent must be assembled over the original finite
places of the base field. These comparisons supply precisely that indexing
for DUB-17's original finite-idele descent and native class norm quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The actual nonzero prime obtained by contracting an original upper finite place. -/
def originalFinitePrimeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  w.under (𝓞 K)

omit [NumberField K] [NumberField L] in
/-- The original upper prime lies over its original contraction. -/
theorem originalFinitePrimeBelow_liesOver (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (originalFinitePrimeBelow K L w).asIdeal := ⟨rfl⟩

omit [NumberField L] in
/-- The standard integral Galois restriction is the actual original integer-ring automorphism. -/
theorem originalIntegerGalRestrict_eq [FiniteDimensional K L] (σ : Gal(L/K)) :
    (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingHom =
      (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingHom := by
  ext r
  exact algebraMap_galRestrict_apply (𝓞 K) σ r

omit [NumberField K] [NumberField L] in
/-- Contraction of an original finite place is unchanged by the original Galois action. -/
theorem originalFinitePrimeBelow_galois (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    originalFinitePrimeBelow K L (numberFieldGaloisPlaceEquiv K L σ w) =
      originalFinitePrimeBelow K L w := by
  apply HeightOneSpectrum.ext
  ext r
  change NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
    (algebraMap (𝓞 K) (𝓞 L) r) ∈ w.asIdeal ↔
      algebraMap (𝓞 K) (𝓞 L) r ∈ w.asIdeal
  have hr : NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
      (algebraMap (𝓞 K) (𝓞 L) r) = algebraMap (𝓞 K) (𝓞 L) r := by
    apply NumberField.RingOfIntegers.ext
    exact σ.symm.commutes (r : K)
  rw [hr]

omit [NumberField L] in
/-- Two original primes over the same base prime are in the same actual Galois orbit. -/
theorem originalFinitePrimeBelow_eq_iff_orbit [FiniteDimensional K L] [IsGalois K L]
    (w₁ w₂ : HeightOneSpectrum (𝓞 L)) :
    originalFinitePrimeBelow K L w₁ = originalFinitePrimeBelow K L w₂ ↔
      ∃ σ : Gal(L/K), numberFieldGaloisPlaceEquiv K L σ w₁ = w₂ := by
  constructor
  · intro h
    let p := (originalFinitePrimeBelow K L w₁).asIdeal
    haveI : w₁.asIdeal.LiesOver p := originalFinitePrimeBelow_liesOver K L w₁
    haveI : w₂.asIdeal.LiesOver p := by
      rw [show p = (originalFinitePrimeBelow K L w₂).asIdeal from congrArg HeightOneSpectrum.asIdeal h]
      exact originalFinitePrimeBelow_liesOver K L w₂
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K L (𝓞 L)
      (p := p) (P₁ := w₂.asIdeal) (P₂ := w₁.asIdeal) ⟨inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance⟩
    refine ⟨σ, HeightOneSpectrum.ext ?_⟩
    rw [numberFieldGaloisPlaceEquiv_asIdeal]
    have hh := congrArg (Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) σ)) hσ
    rw [Ideal.map_comap_of_surjective _ (galRestrict (𝓞 K) K L (𝓞 L) σ).surjective] at hh
    change Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingHom w₁.asIdeal = w₂.asIdeal
    rw [← originalIntegerGalRestrict_eq K L σ]
    exact hh.symm
  · rintro ⟨σ, rfl⟩
    exact (originalFinitePrimeBelow_galois K L σ w₁).symm

omit [NumberField K] [NumberField L] in
/-- Every original base finite place has an original upper finite place above it. -/
theorem originalFinitePrimeBelow_surjective : Function.Surjective (originalFinitePrimeBelow K L) := by
  intro v
  obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  haveI := P.property.1
  haveI := P.property.2
  let w : HeightOneSpectrum (𝓞 L) :=
    ⟨P.val, P.property.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.val⟩
  refine ⟨w, HeightOneSpectrum.ext ?_⟩
  exact (Ideal.over_def P.val v.asIdeal).symm

/-- An original finite exceptional set has finite preimage under actual prime contraction. -/
theorem originalFinitePrimeBelow_preimage_finite
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 L) | originalFinitePrimeBelow K L w ∈ S}.Finite := by
  exact heightOneUnder_preimage_finite S hS

end
end Dubon2026
