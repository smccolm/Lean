import Dubon2026.OriginalIdeleNorm

/-! # The actual original idele-class norm

The original idele norm preserves principal ideles by the actual field
norm formula. It therefore descends to the original class groups, with
its literal Galois-product comparison and extension-degree power law.
These are required for DUB-17's native norm-index and reciprocity chain.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual original idele norm sends principal ideles to principal ideles. -/
theorem originalIdeleNorm_preserves_principal :
    (numberFieldPrincipalIdele L).range ≤
      ((numberFieldPrincipalIdele K).range).comap (originalIdeleNorm K L) := by
  rintro a ⟨x, rfl⟩
  exact ⟨Units.map (Algebra.norm K (S := L)) x, (originalIdeleNorm_principal K L x).symm⟩

/-- The actual original class norm induced by the original idele norm. -/
def originalIdeleClassNorm :
    OriginalNumberFieldIdeleClassGroup L →* OriginalNumberFieldIdeleClassGroup K :=
  QuotientGroup.map _ _ (originalIdeleNorm K L) (originalIdeleNorm_preserves_principal K L)

/-- The actual original class norm retains the norm of every original idele representative. -/
theorem originalIdeleClassNorm_mk (a : (AdeleRing (𝓞 L) L)ˣ) :
    originalIdeleClassNorm K L (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a) =
      QuotientGroup.mk' (numberFieldPrincipalIdele K).range (originalIdeleNorm K L a) :=
  QuotientGroup.map_mk' _ _ _ _ a

/-- The original class norm maps to exactly the product of the original Galois conjugate classes. -/
theorem originalIdeleClassBaseChangeMap_norm (c : OriginalNumberFieldIdeleClassGroup L) :
    originalIdeleClassBaseChangeMap K L (originalIdeleClassNorm K L c) =
      ∏ σ : Gal(L/K), numberFieldIdeleClassGaloisMap K L σ c := by
  induction c using QuotientGroup.induction_on
  rename_i a
  change originalIdeleClassBaseChangeMap K L
    (originalIdeleClassNorm K L (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a)) = _
  rw [originalIdeleClassNorm_mk, originalIdeleClassBaseChangeMap_mk, originalIdeleBaseChangeMap_norm,
    map_prod]
  exact Finset.prod_congr rfl (fun σ _ => (numberFieldIdeleClassGaloisMap_mk K L σ a).symm)

/-- The original class norm of a base class is its extension-degree power. -/
theorem originalIdeleClassNorm_baseChange (c : OriginalNumberFieldIdeleClassGroup K) :
    originalIdeleClassNorm K L (originalIdeleClassBaseChangeMap K L c) = c ^ Module.finrank K L := by
  induction c using QuotientGroup.induction_on
  rename_i a
  change originalIdeleClassNorm K L
    (originalIdeleClassBaseChangeMap K L (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a)) = _
  rw [originalIdeleClassBaseChangeMap_mk, originalIdeleClassNorm_mk, originalIdeleNorm_baseChange,
    map_pow]
  rfl

end
end Dubon2026
