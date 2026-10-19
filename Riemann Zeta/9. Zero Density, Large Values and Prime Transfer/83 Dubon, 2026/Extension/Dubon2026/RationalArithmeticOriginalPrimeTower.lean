import Dubon2026.RationalArithmeticOriginalCompletionTower
import Dubon2026.ArithmeticOrbitPrimeContraction

/-! The prime selected by the original arithmetic embedding contracts
to the same selected prime in a smaller finite field. This fixes the
prime index in DUB-17's finite-correction localization comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (M L : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hML : M.toIntermediateField ≤ L.toIntermediateField)

include hML in
/-- The projected identity coset is the same identity coset over the smaller
field; this identifies both the chosen prime and its completion embedding. -/
theorem rationalArithmeticIdentityCoset_tower :
    let c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a L.toIntermediateField :=
      QuotientGroup.mk 1
    (QuotientGroup.mk c.out :
      rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a M.toIntermediateField) =
      QuotientGroup.mk 1 := by
  let c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a L.toIntermediateField :=
    QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  have he := QuotientGroup.eq.mp (Quotient.out_eq' c)
  exact IntermediateField.fixingSubgroup_le hML he

/-- The actual chosen arithmetic primes are compatible with finite-field inclusion. -/
theorem rationalArithmeticOriginalPrime_under :
    letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
    originalFinitePrimeBelow M L (rationalArithmeticOriginalPrime a p hp L) =
      rationalArithmeticOriginalPrime a p hp M := by
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  let c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a L.toIntermediateField :=
    QuotientGroup.mk 1
  have hc := rationalArithmeticIdentityCoset_tower a M L hML
  exact (rationalArithmeticOrbitPrime_under a p hp M.toIntermediateField L.toIntermediateField hML c).trans
    (congrArg (rationalArithmeticOrbitPrime a p hp M.toIntermediateField) hc)

end
end Dubon2026
