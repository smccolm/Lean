import Dubon2026.ArithmeticOriginalPrimeInvariant
import Dubon2026.ArithmeticOrbitFiniteStageInvariantSupport

/-! # Finite support at the genuine original primes

The already proved finite-stage localization support applies to the exact
coset selected by the original-prime equivalence. This discharges the
individual-prime support premise of DUB-17's total reciprocity sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The actual inflated finite-stage class has finite support in the genuine original lower primes. -/
theorem rationalArithmeticOriginalPrimeInvariant_exists_support
    (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ∀ w ∉ T,
      rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w = 0 := by
  obtain ⟨T, hT⟩ := rationalArithmeticOrbitFiniteStage_invariant_exists_support a F H hFH y
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
