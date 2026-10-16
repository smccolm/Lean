import Dubon2026.ArithmeticRelativeStageIdeleInvariantSupport
import Dubon2026.ArithmeticOriginalPrimeInvariant

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual full-idele invariant at the specified original lower prime. -/
def rationalArithmeticRelativeStageIdelePrimeInvariant
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    rationalArithmeticRelativeStageIdeleH2 a F H hFH →+ AddCircle (1 : ℚ) :=
  let p := rationalArithmeticOriginalPrimeBase a F w
  rationalArithmeticRelativeStageIdeleOrbitInvariant a p.val p.property F H hFH
    ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩).out

/-- The actual principal value at each original prime is exactly the original global invariant of the same finite-stage cocycle. -/
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_principal
    (y : rationalArithmeticRelativeStageCocycles a F H hFH)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w
      (rationalArithmeticRelativeStagePrincipalClass a F H hFH y) =
      rationalArithmeticOriginalPrimeInvariant a F
        (rationalArithmeticRelativeStageInflation a F H hFH y) w :=
  rationalArithmeticRelativeStageIdeleOrbitInvariant_principal a
    (rationalArithmeticOriginalPrimeBase a F w).val (rationalArithmeticOriginalPrimeBase a F w).property
    F H hFH _ y

/-- Each genuine finite-stage full-idele class has finite support over the actual original lower primes. -/
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_exists_support
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ∀ w ∉ T,
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x = 0 := by
  obtain ⟨T, hT⟩ := rationalArithmeticRelativeStageIdeleOrbitInvariant_exists_support a F H hFH x
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
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_hasFiniteSupport
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    (Function.support (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x)).Finite := by
  obtain ⟨T, hT⟩ := rationalArithmeticRelativeStageIdelePrimeInvariant_exists_support a F H hFH x
  apply T.finite_toSet.subset
  intro w hw
  by_contra h
  exact hw (hT w h)

end
end Dubon2026
