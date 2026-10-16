import Dubon2026.ArithmeticOrbitPrimeCompletion

/-! # Original closure and valuation structures over the actual completion

The proved completion equivalence supplies the literal coefficient-closure
embedding, scalar tower and Galois structure. These discharge the structural
premises for DUB-17's normalized invariant comparison at each original prime.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitLocalGalois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The source is the genuine completion at the constructed original finite prime. -/
abbrev rationalArithmeticOrbitPrimeCompletion :=
  (rationalArithmeticOrbitPrime a p hp F c).adicCompletion F

/-- The actual completion equivalence defines the original orbit-field algebra. -/
local instance arithmeticOrbitCompletionTargetAlgebra :
    Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitLocalField a p hp F c) :=
  (rationalArithmeticOrbitCompletionEquiv a p hp F c).toRingHom.toAlgebra

/-- The completion embeds in the same original local coefficient closure. -/
local instance arithmeticOrbitCompletionClosureAlgebra :
    Algebra (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp) :=
  ((rationalArithmeticOrbitLocalField a p hp F c).val.toRingHom.comp
    (rationalArithmeticOrbitCompletionEquiv a p hp F c).toRingHom).toAlgebra

/-- The original closure embedding factors through the same actual orbit field. -/
local instance arithmeticOrbitCompletionClosureTower :
    IsScalarTower (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitLocalField a p hp F c) (rationalPrimeLocalClosure p hp) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Retain the original completion's norm valuation relation. -/
local instance arithmeticOrbitCompletionSourceValuation :
    ValuativeRel (rationalArithmeticOrbitPrimeCompletion a p hp F c) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := rationalArithmeticOrbitPrimeCompletion a p hp F c))

/-- The actual completion is a local field in its original topology. -/
local instance arithmeticOrbitCompletionSourceLocalField :
    IsNonarchimedeanLocalField (rationalArithmeticOrbitPrimeCompletion a p hp F c) :=
  originalAdic_isNonarchimedeanLocalField F (rationalArithmeticOrbitPrime a p hp F c)

/-- The actual completion equivalence extends that original valuation relation. -/
local instance arithmeticOrbitCompletionSourceExtension :
    (ValuativeRel.valuation (rationalArithmeticOrbitPrimeCompletion a p hp F c)).HasExtension
      (ValuativeRel.valuation (rationalArithmeticOrbitLocalField a p hp F c)) :=
  rationalArithmeticOrbitCompletion_hasExtension a p hp F c

/-- The same separable coefficient closure is Galois over the actual prime completion. -/
local instance arithmeticOrbitCompletionSourceGalois :
    IsGalois (rationalArithmeticOrbitPrimeCompletion a p hp F c) (rationalPrimeLocalClosure p hp) := by
  let e := rationalArithmeticOrbitCompletionEquiv a p hp F c
  apply IsGalois.of_equiv_equiv (F := rationalArithmeticOrbitLocalField a p hp F c)
    (E := rationalPrimeLocalClosure p hp) (f := e.symm) (g := RingEquiv.refl _)
  apply RingHom.ext
  intro x
  change ((e (e.symm x) : rationalArithmeticOrbitLocalField a p hp F c) : rationalPrimeLocalClosure p hp) = x
  rw [e.apply_symm_apply]

/-- The literal completion-to-orbit algebra map is onto, by the proved original field comparison. -/
theorem rationalArithmeticOrbitCompletion_algebraMap_surjective :
    Function.Surjective (algebraMap (rationalArithmeticOrbitPrimeCompletion a p hp F c)
      (rationalArithmeticOrbitLocalField a p hp F c)) :=
  (rationalArithmeticOrbitCompletionEquiv a p hp F c).surjective

end
end Dubon2026
