import Dubon2026.ArithmeticOrbitFieldEmbedding

/-! # Consistent coset representatives in an actual arithmetic field tower

The upper fixing subgroup is contained in the lower one. The original
quotient relation therefore preserves the lower coset on projection.
This keeps DUB-17's localized original cocycle and its finite global
stage on the same lower embedding when using completed towers.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H)

include hFH in
/-- Projecting an upper representative retains the original lower coset of the specified arithmetic automorphism. -/
theorem rationalArithmeticOrbitCoset_project_mk (σ : rationalArithmeticGaloisGroup a) :
    (QuotientGroup.mk
      (QuotientGroup.mk σ : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H).out :
        rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) =
      QuotientGroup.mk σ := by
  apply QuotientGroup.eq.mpr
  exact IntermediateField.fixingSubgroup_le hFH
    (QuotientGroup.eq.mp (Quotient.out_eq'
      (QuotientGroup.mk σ : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H)))

include hFH in
/-- The original lower coset is unchanged after lifting its chosen representative to the upper field and projecting back. -/
theorem rationalArithmeticOrbitCoset_project_out
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    (QuotientGroup.mk
      (QuotientGroup.mk c.out : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H).out :
        rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) = c :=
  (rationalArithmeticOrbitCoset_project_mk a F H hFH c.out).trans (Quotient.out_eq' c)

end
end Dubon2026
