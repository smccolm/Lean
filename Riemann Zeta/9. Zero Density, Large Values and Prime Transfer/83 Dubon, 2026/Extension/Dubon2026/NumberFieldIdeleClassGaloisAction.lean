import Dubon2026.NumberFieldIdeleGaloisAction
import Dubon2026.NumberFieldSupportedIdeleExact

/-! # The actual Galois action on the original global idele classes

Equivariance of the original principal embedding allows the actual
idele action to descend to its original quotient. This supplies the
quotient coefficient action in DUB-17's supported exact sequence.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The actual Galois map preserves the original principal-idele image. -/
theorem numberFieldIdeleGaloisMap_preserves_principal (σ : Gal(L/K)) :
    (numberFieldPrincipalIdele L).range ≤
      ((numberFieldPrincipalIdele L).range).comap (numberFieldIdeleGaloisMap K L σ) := by
  rintro a ⟨x, rfl⟩
  exact ⟨σ • x, (numberFieldPrincipalIdele_galois K L σ x).symm⟩

/-- The actual Galois map induced on the original global idele class group. -/
def numberFieldIdeleClassGaloisMap (σ : Gal(L/K)) :
    OriginalNumberFieldIdeleClassGroup L →* OriginalNumberFieldIdeleClassGroup L :=
  QuotientGroup.map _ _ (numberFieldIdeleGaloisMap K L σ)
    (numberFieldIdeleGaloisMap_preserves_principal K L σ)

/-- The original quotient map intertwines the original Galois maps. -/
theorem numberFieldIdeleClassGaloisMap_mk (σ : Gal(L/K)) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleClassGaloisMap K L σ (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a) =
      QuotientGroup.mk' (numberFieldPrincipalIdele L).range (numberFieldIdeleGaloisMap K L σ a) :=
  QuotientGroup.map_mk' _ _ _ _ a

/-- Identity acts identically on the original global idele classes. -/
theorem numberFieldIdeleClassGaloisMap_one (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L 1 a = a := by
  induction a using QuotientGroup.induction_on
  rename_i a
  change numberFieldIdeleClassGaloisMap K L 1
    (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a) = _
  rw [numberFieldIdeleClassGaloisMap_mk, numberFieldIdeleGaloisMap_one]
  rfl

/-- Products of original automorphisms compose their maps of original global idele classes. -/
theorem numberFieldIdeleClassGaloisMap_mul (σ τ : Gal(L/K))
    (a : OriginalNumberFieldIdeleClassGroup L) :
    numberFieldIdeleClassGaloisMap K L (σ * τ) a =
      numberFieldIdeleClassGaloisMap K L σ (numberFieldIdeleClassGaloisMap K L τ a) := by
  induction a using QuotientGroup.induction_on
  rename_i a
  change numberFieldIdeleClassGaloisMap K L (σ * τ)
    (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a) =
      numberFieldIdeleClassGaloisMap K L σ (numberFieldIdeleClassGaloisMap K L τ
        (QuotientGroup.mk' (numberFieldPrincipalIdele L).range a))
  rw [numberFieldIdeleClassGaloisMap_mk, numberFieldIdeleClassGaloisMap_mk,
    numberFieldIdeleClassGaloisMap_mk, numberFieldIdeleGaloisMap_mul]

/-- The actual original Galois action on original global idele classes. -/
@[reducible]
def numberFieldIdeleClassGaloisAction : MulDistribMulAction Gal(L/K)
    (OriginalNumberFieldIdeleClassGroup L) where
  smul σ a := numberFieldIdeleClassGaloisMap K L σ a
  one_smul := numberFieldIdeleClassGaloisMap_one K L
  mul_smul := numberFieldIdeleClassGaloisMap_mul K L
  smul_one σ := map_one (numberFieldIdeleClassGaloisMap K L σ)
  smul_mul σ := map_mul (numberFieldIdeleClassGaloisMap K L σ)

end
end Dubon2026
