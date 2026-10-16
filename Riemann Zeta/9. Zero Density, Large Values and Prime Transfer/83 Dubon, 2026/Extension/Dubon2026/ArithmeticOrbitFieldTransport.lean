import Dubon2026.ArithmeticOrbitCosetEmbedding

/-! # The actual local Galois action transports the generated orbit fields

The field equivalence follows by mapping the literal generators. It is
the remaining local-field comparison needed for representative-independent
prime indexing in DUB-17's reciprocity argument.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  (d : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  (h : rationalPrimeArithmeticRestriction a p hp d • c = c')

include h in
/-- The local automorphism maps one actual generated field onto the other. -/
theorem rationalArithmeticOrbitLocalField_map :
    (rationalArithmeticOrbitLocalField a p hp F c).map d.toAlgHom =
      rationalArithmeticOrbitLocalField a p hp F c' := by
  change (IntermediateField.adjoin (rationalPrimeLocalField p hp)
    (Set.range fun x : F => rationalArithmeticOrbitEmbedding a p hp F c
      (x : rationalUnramifiedExtension a))).map d.toAlgHom =
    IntermediateField.adjoin (rationalPrimeLocalField p hp)
      (Set.range fun x : F => rationalArithmeticOrbitEmbedding a p hp F c'
        (x : rationalUnramifiedExtension a))
  rw [IntermediateField.adjoin_map, ← Set.range_comp]
  apply congrArg (IntermediateField.adjoin (rationalPrimeLocalField p hp))
  apply congrArg (fun f : F → rationalPrimeLocalClosure p hp => Set.range f)
  funext x
  exact (rationalArithmeticOrbitCoset_smul_iff a p hp F c c' d).mp h x

/-- The literal local-closure action restricts to an equivalence of the actual orbit fields. -/
def rationalArithmeticOrbitFieldTransport :
    rationalArithmeticOrbitLocalField a p hp F c ≃ₐ[rationalPrimeLocalField p hp]
      rationalArithmeticOrbitLocalField a p hp F c' :=
  ((rationalArithmeticOrbitLocalField a p hp F c).equivMap d.toAlgHom).trans
    (IntermediateField.equivOfEq (rationalArithmeticOrbitLocalField_map a p hp F c c' d h))

/-- The transported field equivalence retains the exact original global generators. -/
theorem rationalArithmeticOrbitFieldTransport_global (x : F) :
    rationalArithmeticOrbitFieldTransport a p hp F c c' d h
      (rationalArithmeticOrbitFieldInclusion a p hp F c x) =
        rationalArithmeticOrbitFieldInclusion a p hp F c' x := by
  apply Subtype.ext
  exact (rationalArithmeticOrbitCoset_smul_iff a p hp F c c' d).mp h x

end
end Dubon2026
