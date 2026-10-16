import Dubon2026.ArithmeticFiniteStageIdeleInvariantSupport
import Dubon2026.ArithmeticOriginalPrimeInvariant

/-! # Full-idele invariants indexed by the genuine original primes

The same proved prime equivalence selects each actual completion exactly
once. Its principal value is the original-prime invariant already used
in reciprocity, and its support is derived for every actual idele class.
This is the finite-support family required for DUB-17's total class map.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The actual full-idele invariant at the specified original lower prime. -/
def rationalArithmeticFiniteStageIdelePrimeInvariant
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    rationalArithmeticFiniteStageIdeleH2 a F H hFH →+ AddCircle (1 : ℚ) :=
  let p := rationalArithmeticOriginalPrimeBase a F w
  rationalArithmeticFiniteStageIdeleOrbitInvariant a p.val p.property F H hFH
    ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩).out

/-- The actual principal value at each original prime is exactly the original global invariant of the same finite-stage cocycle. -/
theorem rationalArithmeticFiniteStageIdelePrimeInvariant_principal
    (y : rationalArithmeticFiniteStageCocycles a F H hFH)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w
      (rationalArithmeticFiniteStagePrincipalClass a F H hFH y) =
      rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticFiniteStageInflation a F H hFH y) w :=
  rationalArithmeticFiniteStageIdeleOrbitInvariant_principal a
    (rationalArithmeticOriginalPrimeBase a F w).val (rationalArithmeticOriginalPrimeBase a F w).property
    F H hFH _ y

/-- Each genuine finite-stage full-idele class has finite support over the actual original lower primes. -/
theorem rationalArithmeticFiniteStageIdelePrimeInvariant_exists_support
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ∀ w ∉ T,
      rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w x = 0 := by
  obtain ⟨T, hT⟩ := rationalArithmeticFiniteStageIdeleOrbitInvariant_exists_support a F H hFH x
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

/-- The actual full-idele invariant family has finite function support, justifying its finite total. -/
theorem rationalArithmeticFiniteStageIdelePrimeInvariant_hasFiniteSupport
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    (Function.support (fun w => rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w x)).Finite := by
  obtain ⟨T, hT⟩ := rationalArithmeticFiniteStageIdelePrimeInvariant_exists_support a F H hFH x
  apply T.finite_toSet.subset
  intro w hw
  by_contra h
  exact hw (hT w h)

end
end Dubon2026
