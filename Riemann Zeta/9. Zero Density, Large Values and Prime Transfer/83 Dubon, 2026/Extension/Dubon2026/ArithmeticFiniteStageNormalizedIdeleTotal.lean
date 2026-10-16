import Dubon2026.ArithmeticFiniteStageIdeleNormalizedOrbitClass
import Dubon2026.ArithmeticFiniteStageIdeleSinglePrimeSupport
import Dubon2026.ArithmeticFiniteStageIdeleTotalInvariant
import Dubon2026.OriginalFullDecompositionPrimeUnique
import Dubon2026.OriginalCyclicPrimePowerFullDecomposition

/-! # A reciprocal-degree value of the actual original-prime idele total

The proved cyclic prime-power selection supplies a full-decomposition
prime. Its uniqueness identifies the actual arithmetic chosen completion.
The local normalized class then has a single nonzero lower-prime term,
so its total is the reciprocal global degree. This is the required witness
for DUB-17's full-order idele-class construction, before quotient descent.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup
  arithmeticFiniteStageUpperTopology arithmeticFiniteStageUpperDiscrete arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- Every actual cyclic prime-power stage has a full-idele H2 class whose genuine original-prime total is the positive reciprocal of the actual global degree. -/
theorem rationalArithmeticFiniteStage_exists_normalized_idele_total
    (q r : ℕ) (hq : q.Prime)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    ∃ x : rationalArithmeticFiniteStageIdeleH2 a F H hFH,
      rationalArithmeticFiniteStageIdeleTotalInvariant a F H hFH x =
        (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
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
      (rationalArithmeticOrbitPrime a p.val p.property H.toIntermediateField (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p.val p.property F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H.toIntermediateField hFH c] using
      rationalArithmeticOrbitPrime_under a p.val p.property F H.toIntermediateField hFH (QuotientGroup.mk c.out)
  have htu : rationalArithmeticOrbitPrime a p.val p.property H.toIntermediateField (QuotientGroup.mk c.out) = u :=
    originalFullDecomposition_prime_unique F H u _ hu (hbelow.trans he).symm
  have hfull : OriginalFiniteDecompositionGroup F H
      (rationalArithmeticOrbitPrime a p.val p.property H.toIntermediateField (QuotientGroup.mk c.out)) = ⊤ :=
    htu.symm ▸ hu
  obtain ⟨x, hx, hs⟩ := rationalArithmeticFiniteStageIdeleOrbitInvariant_exists_normalized
    a p.val p.property F H hFH c (q ^ (r + 1)) hdegree hfull
  have hsupport : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H), t ≠ u →
      originalFullIdeleAdicH2 F H t x = 0 := by
    intro t ht
    exact hs t (fun h => ht (h.trans htu))
  have hzero : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v ≠ w →
      rationalArithmeticFiniteStageIdelePrimeInvariant a F H hFH v x = 0 :=
    fun v hv => rationalArithmeticFiniteStageIdelePrimeInvariant_single_support a F H hFH u x hsupport v hv
  refine ⟨x, ?_⟩
  rw [rationalArithmeticFiniteStageIdeleTotalInvariant_apply]
  exact (finsum_eq_single _ w hzero).trans hx

end
end Dubon2026
