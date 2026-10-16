import Dubon2026.ArithmeticRelativeStageIdelePrimeInvariant
import Dubon2026.OriginalSinglePrimeIdeleH2Lift

/-! # Canonical prime support from support in an original base-prime fibre

The single-prime trace lift is supported on a Galois orbit. Contraction
has the same value on that orbit, so this support condition suffices to make
every other canonical base-prime coordinate zero. This is the exact finite
sum support clause needed for DUB-17's local normalization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The original local trace lift has zero localization over every other base prime, by invariance of prime contraction under the genuine Galois action. -/
theorem originalSinglePrimeIdeleH2Lift_other_base
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w v : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]
    (hv : originalFinitePrimeBelow K L v ≠ originalFinitePrimeBelow K L w)
    (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleAdicH2 K L v (originalSinglePrimeIdeleH2Lift K L w x) = 0 := by
  exact originalSinglePrimeIdeleH2Lift_outside_orbit K L w v
    (fun σ h => hv ((congrArg (originalFinitePrimeBelow K L) h).symm.trans
      (originalFinitePrimeBelow_galois K L σ w))) x

attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageUpperTopology arithmeticRelativeStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- An actual idele H2 class supported over one original base prime has zero canonical invariant at every other base prime. -/
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_base_support
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 H))
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (hx : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
        originalFinitePrimeBelow F H t ≠ originalFinitePrimeBelow F H u →
        originalFullIdeleAdicH2 F H t x = 0)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      w ≠ originalFinitePrimeBelow F H u) :
    rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
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
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p.val p.property F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH c] using
      rationalArithmeticOrbitPrime_under a p.val p.property F H hFH (QuotientGroup.mk c.out)
  have ht : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)) ≠
      originalFinitePrimeBelow F H u := by
    intro h
    exact hw ((hbelow.trans he).symm.trans h)
  exact rationalArithmeticRelativeStageIdeleOrbitInvariant_eq_zero_of_adic a p.val p.property F H hFH c x (hx _ ht)

end
end Dubon2026
