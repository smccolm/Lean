import Dubon2026.ArithmeticOrbitRepresentativeEmbedding

/-! # A normal global stage has the same actual generated local field for every coset

Reuse the pinned normal-field image theorem. Only the original global
embedding changes; the generated local subfield is unchanged. This is
the field comparison needed to apply actual global prime transitivity
on the finite Galois cover in DUB-17's prime-surjectivity proof.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))

/-- Retain the actual intermediate field's rational scalar structure for normality. -/
local instance arithmeticOrbitNormalSubfieldAlgebra : Algebra ℚ F := F.algebra'

variable [hNormal : Normal ℚ F]

include hNormal in
/-- Every coset twists a normal original stage onto exactly its original field image. -/
theorem rationalArithmeticOrbitRepresentative_range
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    Set.range (fun x : F => rationalArithmeticOrbitRepresentative a F c (x : rationalUnramifiedExtension a)) =
      (F : Set (rationalUnramifiedExtension a)) :=
  congrArg (fun E : IntermediateField ℚ (rationalUnramifiedExtension a) =>
    (E : Set (rationalUnramifiedExtension a)))
      (AlgHom.fieldRange_of_normal (E := F)
        ((rationalArithmeticOrbitRepresentative a F c).toAlgHom.comp F.val))

include hNormal in
/-- All cosets of a normal original stage generate the same actual local intermediate field. -/
theorem rationalArithmeticOrbitLocalField_eq_of_normal
    (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    rationalArithmeticOrbitLocalField a p hp F c = rationalArithmeticOrbitLocalField a p hp F c' := by
  let i := rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
  change IntermediateField.adjoin (rationalPrimeLocalField p hp)
    (Set.range (i ∘ fun x : F => rationalArithmeticOrbitRepresentative a F c (x : rationalUnramifiedExtension a))) =
      IntermediateField.adjoin (rationalPrimeLocalField p hp)
        (Set.range (i ∘ fun x : F => rationalArithmeticOrbitRepresentative a F c' (x : rationalUnramifiedExtension a)))
  rw [Set.range_comp, Set.range_comp, rationalArithmeticOrbitRepresentative_range,
    rationalArithmeticOrbitRepresentative_range]

end
end Dubon2026
