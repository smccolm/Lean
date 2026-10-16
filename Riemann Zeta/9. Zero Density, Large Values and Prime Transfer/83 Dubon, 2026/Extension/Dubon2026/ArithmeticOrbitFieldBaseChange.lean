import Dubon2026.ArithmeticOrbitFieldAction
import Dubon2026.GaloisFixingSubgroupUnitCohomology

/-! # Literal Galois base change into the arithmetic orbit field

The actual coset-twisted embedding supplies the scalar towers. The
restriction from the orbit's local Galois group is exactly the conjugation
map used in Mackey transfer. This removes a field-action assumption from
the comparison needed for DUB-17's arbitrary-number-field reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The actual coset-twisted embedding defines the upper-field algebra. -/
abbrev arithmeticOrbitUpperAlgebra :
    Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
  (rationalArithmeticOrbitEmbedding a p hp F c).toAlgebra

/-- The actual global field embeds into its generated orbit local field. -/
abbrev arithmeticOrbitBaseAlgebra :
    Algebra F (rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitFieldInclusion a p hp F c).toAlgebra

/-- Retain the same actual global-field embedding into the local closure. -/
abbrev arithmeticOrbitBaseClosureAlgebra : Algebra F (rationalPrimeLocalClosure p hp) :=
  ((rationalArithmeticOrbitEmbedding a p hp F c).comp F.val).toAlgebra

/-- The original arithmetic union remains Galois over the actual subfield. -/
local instance arithmeticOrbitUpperGalois : IsGalois F (rationalUnramifiedExtension a) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  exact IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension a)

/-- The local closure is Galois over the actual generated local field. -/
local instance arithmeticOrbitLocalGalois :
    IsGalois (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
  IsGalois.tower_top_of_isGalois (rationalPrimeLocalField p hp)
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp)

/-- Regard the literal orbit stabilizer as the Galois group of the
actual generated local field, using the proved equality of subgroups. -/
def rationalArithmeticOrbitLocalAutomorphism
    (d : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c) :
    Gal(rationalPrimeLocalClosure p hp / rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitLocalField a p hp F c).fixingSubgroupEquiv
    ⟨d.val, by rw [rationalArithmeticOrbitLocalField_fixingSubgroup]; exact d.property⟩

/-- The actual Galois restriction for the literal coset-twisted field
embedding, with both scalar towers constructed from those embeddings. -/
def rationalArithmeticOrbitBaseChange :
    Gal(rationalPrimeLocalClosure p hp / rationalArithmeticOrbitLocalField a p hp F c) →*
      Gal(rationalUnramifiedExtension a / F) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalArithmeticOrbitLocalField a p hp F c) :=
    arithmeticOrbitBaseAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : SMul F (rationalArithmeticOrbitLocalField a p hp F c) :=
    (arithmeticOrbitBaseAlgebra a p hp F c).toSMul
  letI hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI hLocal : IsScalarTower F (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact @galoisBaseChangeRestriction F (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) _ _ _ _
    (arithmeticOrbitBaseAlgebra a p hp F c) F.toAlgebra
    (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F c).toAlgebra
    (arithmeticOrbitUpperAlgebra a p hp F c) hLocal hUpper inferInstance

/-- Genuine restriction from the orbit local field equals the literal
Mackey conjugation, with the original field automorphisms preserved. -/
theorem rationalArithmeticOrbitBaseChangeRestriction
    (d : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c) :
    rationalArithmeticOrbitBaseChange a p hp F c
        (rationalArithmeticOrbitLocalAutomorphism a p hp F c d) =
      F.fixingSubgroupEquiv
        (cosetOrbitSubgroupMap (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
          (rationalArithmeticOrbitFixingSubgroup a F) c d) := by
  letI : Algebra (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    arithmeticOrbitUpperAlgebra a p hp F c
  letI : Algebra F (rationalArithmeticOrbitLocalField a p hp F c) :=
    arithmeticOrbitBaseAlgebra a p hp F c
  letI : Algebra F (rationalPrimeLocalClosure p hp) := arithmeticOrbitBaseClosureAlgebra a p hp F c
  letI : SMul F (rationalArithmeticOrbitLocalField a p hp F c) :=
    (arithmeticOrbitBaseAlgebra a p hp F c).toSMul
  letI hUpper : IsScalarTower F (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI hLocal : IsScalarTower F (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply AlgEquiv.ext
  intro x
  apply (rationalArithmeticOrbitEmbedding a p hp F c).injective
  have h := @galoisBaseChangeRestriction_commutes F (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalUnramifiedExtension a) (rationalPrimeLocalClosure p hp) _ _ _ _
    (arithmeticOrbitBaseAlgebra a p hp F c) F.toAlgebra
    (arithmeticOrbitBaseClosureAlgebra a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F c).toAlgebra
    (arithmeticOrbitUpperAlgebra a p hp F c) hLocal hUpper inferInstance
    (rationalArithmeticOrbitLocalAutomorphism a p hp F c d) x
  exact h.trans (rationalArithmeticOrbitEmbedding_equivariant a p hp F c d x).symm

end
end Dubon2026
