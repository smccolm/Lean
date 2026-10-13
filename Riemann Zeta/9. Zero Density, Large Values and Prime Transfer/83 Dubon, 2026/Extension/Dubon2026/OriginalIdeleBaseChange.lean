import Dubon2026.OriginalAdeleBaseChange

/-! # Actual original idele base change and fixed-point descent

Taking units of the proved original adele comparison identifies actual
fixed ideles with the original base ideles. This removes the idele descent
assumption in the original norm quotient comparison, on DUB-17's global
duality, numerical Selmer and automorphy dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The actual base-change homomorphism on the original full ideles. -/
def originalIdeleBaseChangeMap : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (originalAdeleBaseChangeMap K L).toMonoidHom

/-- Original idele base change is injective. -/
theorem originalIdeleBaseChangeMap_injective : Function.Injective (originalIdeleBaseChangeMap K L) := by
  intro a b hab
  apply Units.ext
  exact originalAdeleBaseChangeMap_injective K L (congrArg Units.val hab)

/-- Original idele base change agrees with the actual embedding of principal ideles. -/
theorem originalIdeleBaseChangeMap_principal (x : Kˣ) :
    originalIdeleBaseChangeMap K L (numberFieldPrincipalIdele K x) =
      numberFieldPrincipalIdele L (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  exact originalAdeleBaseChangeMap_algebraMap K L x.val

/-- Every original base idele is fixed by the actual original Galois action. -/
theorem originalIdeleBaseChangeMap_fixed (σ : Gal(L/K)) (a : (AdeleRing (𝓞 K) K)ˣ) :
    numberFieldIdeleGaloisMap K L σ (originalIdeleBaseChangeMap K L a) =
      originalIdeleBaseChangeMap K L a := by
  apply Units.ext
  exact originalAdeleBaseChangeMap_fixed K L σ a.val

/-- Every actual fixed original idele descends to an actual original base idele. -/
theorem originalIdeleBaseChangeMap_surjective_fixed [FiniteDimensional K L] [IsGalois K L]
    (a : (AdeleRing (𝓞 L) L)ˣ) (ha : ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a) :
    ∃ b : (AdeleRing (𝓞 K) K)ˣ, originalIdeleBaseChangeMap K L b = a := by
  obtain ⟨b, hb⟩ := originalAdeleBaseChangeMap_surjective_fixed K L a.val
    (fun σ => congrArg Units.val (ha σ))
  have hi (σ : Gal(L/K)) : numberFieldIdeleGaloisMap K L σ a⁻¹ = a⁻¹ := by
    rw [map_inv, ha]
  obtain ⟨c, hc⟩ := originalAdeleBaseChangeMap_surjective_fixed K L a.inv
    (fun σ => congrArg Units.val (hi σ))
  have hbc : b * c = 1 := by
    apply originalAdeleBaseChangeMap_injective K L
    rw [map_mul, hb, hc, map_one]
    exact a.val_inv
  have hcb : c * b = 1 := by
    apply originalAdeleBaseChangeMap_injective K L
    rw [map_mul, hb, hc, map_one]
    exact a.inv_val
  exact ⟨⟨b, c, hbc, hcb⟩, Units.ext hb⟩

/-- The actual original fixed ideles are exactly the original base-idele image. -/
theorem originalIdeleBaseChangeMap_range_iff_fixed [FiniteDimensional K L] [IsGalois K L]
    (a : (AdeleRing (𝓞 L) L)ˣ) :
    a ∈ Set.range (originalIdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a = a := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact originalIdeleBaseChangeMap_fixed K L σ b
  · exact originalIdeleBaseChangeMap_surjective_fixed K L a

end
end Dubon2026
