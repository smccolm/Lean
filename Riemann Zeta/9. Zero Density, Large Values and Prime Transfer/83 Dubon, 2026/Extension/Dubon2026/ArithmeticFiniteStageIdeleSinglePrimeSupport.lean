import Dubon2026.ArithmeticFiniteStageIdelePrimeInvariant

/-! # Single-prime localization gives single-prime total-invariant support

The actual selected upper prime contracts to the lower original prime
used by the invariant. Thus a single-prime original idele H2 lift has
exactly the support needed to evaluate DUB-17's full-idele total.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- An actual idele H2 class localized only at one original upper prime has zero normalized invariant at every other contracted original prime. -/
theorem rationalArithmeticFiniteStageIdelePrimeInvariant_single_support
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 H))
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH)
    (hx : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H), t ≠ u →
        originalFullIdeleAdicH2 F H t x = 0)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      w ≠ originalFinitePrimeBelow F H u) :
    rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH w x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  let p := rationalArithmeticOriginalPrimeBase a F w
  let v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F v = rationalPrimePlace p.val p.property} :=
    ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩
  let e := rationalArithmeticOrbitPrimeEquiv a p.val p.property F
  let c := (e.symm v).out
  have he : rationalArithmeticOrbitPrime a p.val p.property F c = w :=
    (rationalArithmeticOrbitPrimeEquiv_out a p.val p.property F (e.symm v)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply v))
  have hbelow : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p.val p.property H.toIntermediateField (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p.val p.property F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H.toIntermediateField hFH c] using
      rationalArithmeticOrbitPrime_under a p.val p.property F H.toIntermediateField hFH (QuotientGroup.mk c.out)
  have ht : rationalArithmeticOrbitPrime a p.val p.property H.toIntermediateField (QuotientGroup.mk c.out) ≠ u := by
    intro h
    rw [h] at hbelow
    exact hw ((hbelow.trans he).symm)
  exact rationalArithmeticFiniteStageIdeleOrbitInvariant_eq_zero_of_adic a p.val p.property F H hFH c x (hx _ ht)

end
end Dubon2026
