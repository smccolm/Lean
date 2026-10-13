import Dubon2026.OriginalIdeleBaseChange
import Dubon2026.OriginalInvariantIdeleClassLifting
import Dubon2026.GaloisUnitInvariantBaseDescent

/-! # Original idele-class base change and invariant descent

The actual original idele inclusion preserves principal ideles. Existing
field-unit fixed descent reflects principal membership, while existing
fixed-class lifting and actual idele descent give surjectivity onto fixed
classes. This identifies the actual base class group needed for DUB-17's
norm quotient and subsequent global duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Actual original idele inclusion preserves original principal membership. -/
theorem originalIdeleBaseChangeMap_preserves_principal :
    (numberFieldPrincipalIdele K).range ≤
      ((numberFieldPrincipalIdele L).range).comap (originalIdeleBaseChangeMap K L) := by
  rintro a ⟨x, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom x, (originalIdeleBaseChangeMap_principal K L x).symm⟩

/-- The actual inclusion of original base-field idele classes. -/
def originalIdeleClassBaseChangeMap :
    OriginalNumberFieldIdeleClassGroup K →* OriginalNumberFieldIdeleClassGroup L :=
  QuotientGroup.map _ _ (originalIdeleBaseChangeMap K L)
    (originalIdeleBaseChangeMap_preserves_principal K L)

/-- The actual class inclusion is induced by the original idele inclusion. -/
theorem originalIdeleClassBaseChangeMap_mk (a : (AdeleRing (𝓞 K) K)ˣ) :
    originalIdeleClassBaseChangeMap K L (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a) =
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range (originalIdeleBaseChangeMap K L a) :=
  QuotientGroup.map_mk' _ _ _ _ a

/-- The actual base classes are fixed by the actual original Galois action. -/
theorem originalIdeleClassBaseChangeMap_fixed (σ : Gal(L/K)) (c : OriginalNumberFieldIdeleClassGroup K) :
    numberFieldIdeleClassGaloisMap K L σ (originalIdeleClassBaseChangeMap K L c) =
      originalIdeleClassBaseChangeMap K L c := by
  induction c using QuotientGroup.induction_on
  rename_i a
  change numberFieldIdeleClassGaloisMap K L σ
    (originalIdeleClassBaseChangeMap K L (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a)) = _
  rw [originalIdeleClassBaseChangeMap_mk, numberFieldIdeleClassGaloisMap_mk,
    originalIdeleBaseChangeMap_fixed]
  rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- Actual original idele inclusion reflects principal membership by proved global field-unit descent. -/
theorem originalIdeleBaseChangeMap_reflects_principal (a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : originalIdeleBaseChangeMap K L a ∈ (numberFieldPrincipalIdele L).range) :
    a ∈ (numberFieldPrincipalIdele K).range := by
  obtain ⟨x, hx⟩ := ha
  have hfix (σ : Gal(L/K)) : σ • x = x := by
    apply numberFieldPrincipalIdele_injective L
    rw [← numberFieldPrincipalIdele_galois, hx, originalIdeleBaseChangeMap_fixed]
  obtain ⟨u, hu⟩ := galoisUnitInvariant_exists_base (K := K) (L := L)
    (Rep.toAdditive.symm (Additive.ofMul x)) (fun σ => hfix σ)
  change Units.map (algebraMap K L).toMonoidHom u = x at hu
  refine ⟨u, originalIdeleBaseChangeMap_injective K L ?_⟩
  rw [originalIdeleBaseChangeMap_principal, hu, hx]

/-- The actual original class inclusion is injective for the original finite Galois extension. -/
theorem originalIdeleClassBaseChangeMap_injective : Function.Injective (originalIdeleClassBaseChangeMap K L) := by
  apply (injective_iff_map_eq_one _).mpr
  intro c hc
  induction c using QuotientGroup.induction_on
  rename_i a
  change originalIdeleClassBaseChangeMap K L (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a) = 1 at hc
  rw [originalIdeleClassBaseChangeMap_mk] at hc
  exact (QuotientGroup.eq_one_iff a).mpr
    (originalIdeleBaseChangeMap_reflects_principal K L a ((QuotientGroup.eq_one_iff _).mp hc))

/-- Every actual original fixed class descends to an actual original base-field class. -/
theorem originalIdeleClassBaseChangeMap_surjective_fixed (c : OriginalNumberFieldIdeleClassGroup L)
    (hc : ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c) :
    ∃ b : OriginalNumberFieldIdeleClassGroup K, originalIdeleClassBaseChangeMap K L b = c := by
  obtain ⟨a, ha, hfix⟩ := original_ideleClass_fixed_has_fixed_representative K L c hc
  obtain ⟨b, hb⟩ := originalIdeleBaseChangeMap_surjective_fixed K L a hfix
  refine ⟨QuotientGroup.mk' (numberFieldPrincipalIdele K).range b, ?_⟩
  rw [originalIdeleClassBaseChangeMap_mk, hb, ha]

/-- The actual original base class image is precisely the actual original fixed class set. -/
theorem originalIdeleClassBaseChangeMap_range_iff_fixed (c : OriginalNumberFieldIdeleClassGroup L) :
    c ∈ Set.range (originalIdeleClassBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c = c := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact originalIdeleClassBaseChangeMap_fixed K L σ b
  · exact originalIdeleClassBaseChangeMap_surjective_fixed K L c

end
end Dubon2026
