import Dubon2026.ArithmeticOrbitRepresentativeEmbedding
import Dubon2026.ArithmeticOrbitPrimeCompletion

/-! # Literal local-field inclusions for an original finite-field cover

Project an upper coset using its actual representative. The lower field's
literal generators then lie in the upper orbit field, and the induced local
inclusion retains the original global inclusion. This supplies the precise
map consumed by DUB-17's prime contraction comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H)

include hFH in
/-- The lower coset's literal generated field lies in the upper coset's generated field. -/
theorem rationalArithmeticOrbitLocalField_subfield_le :
    rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk c.out) ≤
      rationalArithmeticOrbitLocalField a p hp H c := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨x, rfl⟩
  change rationalArithmeticOrbitEmbedding a p hp F (QuotientGroup.mk c.out)
    (x : rationalUnramifiedExtension a) ∈ _
  rw [rationalArithmeticOrbitEmbedding_mk]
  exact rationalArithmeticOrbitEmbedding_mem a p hp H c ⟨x, hFH x.property⟩

/-- The exact generated-field inclusion induced by the original finite-field inclusion. -/
def rationalArithmeticOrbitSubfieldMap :
    rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk c.out) →ₐ[rationalPrimeLocalField p hp]
      rationalArithmeticOrbitLocalField a p hp H c :=
  IntermediateField.inclusion (rationalArithmeticOrbitLocalField_subfield_le a p hp F H hFH c)

/-- The local inclusion preserves precisely the actual global finite-field inclusion. -/
theorem rationalArithmeticOrbitSubfieldMap_global (x : F) :
    rationalArithmeticOrbitSubfieldMap a p hp F H hFH c
      (rationalArithmeticOrbitFieldInclusion a p hp F (QuotientGroup.mk c.out) x) =
        rationalArithmeticOrbitFieldInclusion a p hp H c (IntermediateField.inclusion hFH x) := by
  apply Subtype.ext
  exact rationalArithmeticOrbitEmbedding_mk a p hp F c.out x

end
end Dubon2026
