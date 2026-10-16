import Dubon2026.ArithmeticOriginalPrimeInvariant
import Dubon2026.ArithmeticOrbitRelativeStageInvariantSupport

/-! # Actual relative-stage reciprocity

Retain the original finite extension and its literal arithmetic-union
inflation using only Galoisness over its base. This removes the extra
rational-normality assumption from the auxiliary cyclic stage required
by DUB-17's full-order class transfer.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual inflated finite-stage class has finite support in the genuine original lower primes. -/
theorem rationalArithmeticRelativePrimeInvariant_exists_support
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ∀ w ∉ T,
      rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticRelativeStageInflation a F H hFH y) w = 0 := by
  obtain ⟨T, hT⟩ := rationalArithmeticOrbitRelativeStage_invariant_exists_support a F H hFH y
  refine ⟨T, ?_⟩
  intro w hw
  let p := rationalArithmeticOriginalPrimeBase a F w
  let v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F v = rationalPrimePlace p.val p.property} :=
    ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩
  let e := rationalArithmeticOrbitPrimeEquiv a p.val p.property F
  have he : rationalArithmeticOrbitPrime a p.val p.property F (e.symm v).out = w :=
    (rationalArithmeticOrbitPrimeEquiv_out a p.val p.property F (e.symm v)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply v))
  exact hT p.val p.property (e.symm v).out (fun h => hw (he ▸ h))

end
end Dubon2026
