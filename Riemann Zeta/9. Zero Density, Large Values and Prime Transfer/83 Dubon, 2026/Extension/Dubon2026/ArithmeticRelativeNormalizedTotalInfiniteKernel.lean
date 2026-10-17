import Dubon2026.ArithmeticRelativeNormalizedOrbitInfiniteKernel
import Dubon2026.ArithmeticRelativeStageIdeleNormalizedOrbitClass
import Dubon2026.ArithmeticRelativeStageIdeleSinglePrimeSupport
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant
import Dubon2026.OriginalFullDecompositionPrimeUnique
import Dubon2026.OriginalCyclicPrimePowerFullDecomposition

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
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

/-- The normalized witness is constructed with zero original infinite localization.
Every actual cyclic prime-power stage has a full-idele H2 class whose genuine original-prime total is the positive reciprocal of the actual global degree. -/
theorem rationalArithmeticRelativeStage_exists_normalized_idele_total_infinite_zero
    (q r : ℕ) (hq : q.Prime)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    ∃ x : rationalArithmeticRelativeStageIdeleH2 a F H hFH,
      rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x =
        (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
        ∀ v : NumberField.InfinitePlace H, originalFullIdeleInfiniteH2 F H v x = 0) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : IsCyclic Gal(H/F) := hcyclic
  obtain ⟨u, _, hu⟩ := original_cyclicPrimePower_exists_fullDecomposition_outside F H
    q (r + 1) hq (by omega) hdegree ∅
  let w := originalFinitePrimeBelow F H u
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
  have htu : rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out) = u :=
    originalFullDecomposition_prime_unique F H u _ hu (hbelow.trans he).symm
  have hfull : OriginalFiniteDecompositionGroup F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out)) = ⊤ :=
    htu.symm ▸ hu
  obtain ⟨x, hx, hs, hi⟩ := rationalArithmeticRelativeStageIdeleOrbitInvariant_exists_normalized_infinite_zero
    a p.val p.property F H hFH c (q ^ (r + 1)) hdegree hfull
  have hsupport : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H), t ≠ u →
      originalFullIdeleAdicH2 F H t x = 0 := by
    intro t ht
    exact hs t (fun h => ht (h.trans htu))
  have hzero : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v ≠ w →
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH v x = 0 :=
    fun v hv => rationalArithmeticRelativeStageIdelePrimeInvariant_single_support a F H hFH u x hsupport v hv
  refine ⟨x, ?_, hi⟩
  rw [rationalArithmeticRelativeStageIdeleTotalInvariant_apply]
  exact (finsum_eq_single _ w hzero).trans hx

end
end Dubon2026
