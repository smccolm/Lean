import Dubon2026.OriginalLocalCompletionSurjective
import Dubon2026.OriginalLocalCompletionValuation
import Dubon2026.ArithmeticOrbitFieldBaseChange
import Dubon2026.ArithmeticOrbitLocalStructure

/-! # The actual arithmetic orbit field is an original prime completion

Construct the finite prime by pulling back the actual valuation maximal
ideal. The proved generated-field comparison identifies its genuine
completion with the orbit field and preserves the original global values.
This discharges the individual-field comparison on DUB-17's route to the
number-field reciprocity sum. The orbit/prime indexing remains separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The original finite arithmetic subfield is a number field. -/
local instance arithmeticOrbitCompletionNumberField : NumberField F := NumberField.of_module_finite ℚ F
/-- Retain the literal global-field inclusion into the orbit field. -/
local instance arithmeticOrbitCompletionBaseAlgebra :
    Algebra F (rationalArithmeticOrbitLocalField a p hp F c) := arithmeticOrbitBaseAlgebra a p hp F c
/-- The orbit valuation is obtained from the proved spectral local-field construction. -/
local instance arithmeticOrbitCompletionValuation :
    ValuativeRel (rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F c).choose
/-- Retain the topology from that same constructed local-field structure. -/
local instance arithmeticOrbitCompletionTopology :
    TopologicalSpace (rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F c).choose_spec.choose
/-- The constructed orbit field is a nonarchimedean local field. -/
local instance arithmeticOrbitCompletionLocalField :
    IsNonarchimedeanLocalField (rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F c).choose_spec.choose_spec.1
/-- The constructed valuation extends the original rational-prime valuation. -/
local instance arithmeticOrbitCompletionValuationExtension :
    (ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F c)) :=
  (rationalArithmeticOrbitLocalField_exists_structure a p hp F c).choose_spec.choose_spec.2
/-- Use the uniformity of the original additive topological group. -/
local instance arithmeticOrbitCompletionUniformity :
    UniformSpace (rationalArithmeticOrbitLocalField a p hp F c) := IsTopologicalAddGroup.rightUniformSpace _
/-- The selected uniformity is compatible with the original addition. -/
local instance arithmeticOrbitCompletionUniformAdd :
    IsUniformAddGroup (rationalArithmeticOrbitLocalField a p hp F c) := isUniformAddGroup_of_addCommGroup

/-- The actual finite prime cut out by the coset-twisted embedding. -/
def rationalArithmeticOrbitPrime : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
  originalLocalEmbeddingPrime F (rationalArithmeticOrbitLocalField a p hp F c) p hp

/-- The constructed original finite prime lies over the original rational prime. -/
theorem rationalArithmeticOrbitPrime_below :
    originalIntegerPrimeBelow F (rationalArithmeticOrbitPrime a p hp F c) = rationalPrimePlace p hp :=
  originalLocalEmbeddingPrime_below F (rationalArithmeticOrbitLocalField a p hp F c) p hp

/-- The actual number-field completion is the orbit field, by the proved generation identity. -/
def rationalArithmeticOrbitCompletionEquiv :
    (rationalArithmeticOrbitPrime a p hp F c).adicCompletion F ≃+*
      rationalArithmeticOrbitLocalField a p hp F c :=
  originalLocalCompletionEquiv F (rationalArithmeticOrbitLocalField a p hp F c) p hp
    (rationalArithmeticOrbitField_ranges a p hp F c)

/-- The comparison preserves the literal global field inclusion into the orbit field. -/
theorem rationalArithmeticOrbitCompletionEquiv_algebraMap (x : F) :
    rationalArithmeticOrbitCompletionEquiv a p hp F c
      (algebraMap F ((rationalArithmeticOrbitPrime a p hp F c).adicCompletion F) x) =
        rationalArithmeticOrbitFieldInclusion a p hp F c x :=
  originalLocalCompletionEquiv_algebraMap F (rationalArithmeticOrbitLocalField a p hp F c) p hp
    (rationalArithmeticOrbitField_ranges a p hp F c) x

/-- In the original local closure the comparison is exactly the coset-twisted arithmetic embedding. -/
theorem rationalArithmeticOrbitCompletionEquiv_coe (x : F) :
    (rationalArithmeticOrbitCompletionEquiv a p hp F c
      (algebraMap F ((rationalArithmeticOrbitPrime a p hp F c).adicCompletion F) x) :
        rationalPrimeLocalClosure p hp) =
      rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a) := by
  rw [rationalArithmeticOrbitCompletionEquiv_algebraMap]
  exact rationalArithmeticOrbitFieldInclusion_coe a p hp F c x

/-- The actual completion identification preserves the original norm valuation relation. -/
theorem rationalArithmeticOrbitCompletion_hasExtension :
    let W := (rationalArithmeticOrbitPrime a p hp F c).adicCompletion F
    letI : Algebra W (rationalArithmeticOrbitLocalField a p hp F c) :=
      (rationalArithmeticOrbitCompletionEquiv a p hp F c).toRingHom.toAlgebra
    letI : ValuativeRel W := ValuativeRel.ofValuation (NormedField.valuation (K := W))
    (ValuativeRel.valuation W).HasExtension
      (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F c)) :=
  originalLocalCompletionMap_hasExtension F (rationalArithmeticOrbitLocalField a p hp F c) p hp

end
end Dubon2026
