import Dubon2026.ArithmeticOriginalPrimeInvariantSum
import Dubon2026.ArithmeticPrimePowerUnitInvariantSum

/-! # Actual original-prime reciprocity with its real corestriction term

Reuse the exact original-prime fiber comparison and finite-support
reindexing, then apply the proved rational prime-power finite-plus-real
sum. This removes the odd-prime restriction while retaining the actual
real corestriction term needed by DUB-17's full-idele principal kernel.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionClosureTower
  arithmeticOrbitCompletionSourceValuation arithmeticOrbitCompletionSourceLocalField
  arithmeticOrbitCompletionSourceExtension arithmeticOrbitCompletionSourceGalois
  arithmeticOrbitUpperGalois arithmeticOrbitLocalGalois arithmeticGlobalUnitContinuousSMul
  orbitUnitComparisonGlobalGalois orbitUnitComparisonRawTopology orbitUnitComparisonRawDiscrete
  arithmeticOrbitComparisonLocalFinite arithmeticOrbitComparisonLocalTopology arithmeticOrbitComparisonLocalDiscrete
  arithmeticOrbitCompletionCoefficientTopology arithmeticOrbitCompletionCoefficientDiscrete arithmeticOrbitCompletionCosets
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype
  arithmeticPrimeInvariantUnitTopology arithmeticPrimeInvariantUnitDiscrete
  arithmeticOrbitNormalSubfieldAlgebra arithmeticOriginalPrimeFiberFintype

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits ℝ ℂ)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- Every prime-power original class has zero sum of its genuine finite
prime invariants and the actual real invariant of field corestriction. -/
theorem rationalArithmeticOriginalPrimeInvariant_prime_power_sum_add_real_zero
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (hy : q ^ (r + 1) • (Submodule.Quotient.mk y : GaloisUnitContinuousH2
      (K := F) (Ω := rationalUnramifiedExtension a)) = 0)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : ∀ w ∉ T, rationalArithmeticOriginalPrimeInvariant a F y w = 0) :
    (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F y w) +
      originalRealUnitH2Invariant (rationalArithmeticRealUnitH2Restriction a
        (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
          (Submodule.Quotient.mk y))) = 0 := by
  classical
  let x := galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)
  let P := T.image (rationalArithmeticOriginalPrimeBase a F)
  have hx : q ^ (r + 1) • x = 0 := by
    change q ^ (r + 1) • (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F
      (Submodule.Quotient.mk y)) = 0
    rw [← map_nsmul, hy, map_zero]
  have hP : ∀ p ∉ P, rationalArithmeticUnitPrimeInvariant a p.val p.property x = 0 := by
    intro p hp
    rw [rationalArithmeticOriginalPrimeInvariant_fiber_sum a F y p]
    apply Finset.sum_eq_zero
    intro w _
    exact hT w.val (fun hw => hp (Finset.mem_image.mpr
      ⟨w.val, hw, rationalArithmeticOriginalPrimeBase_eq a F p w.val w.property⟩))
  have hz := rationalArithmeticUnitInvariant_prime_power_sum_zero a q r hq hqa x hx P hP
  have he : (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F y w) =
      ∑ p ∈ P, rationalArithmeticUnitPrimeInvariant a p.val p.property x := by
    calc
      _ = ∑ p ∈ P, ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
            originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property},
            rationalArithmeticOriginalPrimeInvariant a F y w.val :=
        (rationalArithmeticOriginalPrimeFiber_sum a F
          (rationalArithmeticOriginalPrimeInvariant a F y) T hT).symm
      _ = ∑ p ∈ P, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
        Finset.sum_congr rfl (fun p _ => (rationalArithmeticOriginalPrimeInvariant_fiber_sum a F y p).symm)
  exact (congrArg (fun v => v + originalRealUnitH2Invariant
    (rationalArithmeticRealUnitH2Restriction a x)) he).trans hz

end
end Dubon2026
