import Dubon2026.ArithmeticOriginalPrimeFiberSum
import Dubon2026.ArithmeticOddPrimaryInvariantSum

/-! # Odd-primary reciprocity over every genuine original prime

The actual field corestriction has the proved original-prime Mackey sum.
Individual finite support permits finite fiberwise reindexing, so the
proved rational odd-primary reciprocity theorem gives the total original
number-field prime sum. This is the reciprocity input on DUB-17's route
to a full-order class and reverse localization; no invariant-sum premise
is introduced.
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
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The original field-corestriction invariant equals the sum of the indexed genuine original-prime invariants. -/
theorem rationalArithmeticOriginalPrimeInvariant_fiber_sum
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (p : Nat.Primes) :
    rationalArithmeticUnitPrimeInvariant a p.val p.property
      (galoisUnitContinuousCorestriction ℚ (rationalUnramifiedExtension a) F (Submodule.Quotient.mk y)) =
      ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
        originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property},
        rationalArithmeticOriginalPrimeInvariant a F y w.val := by
  exact (rationalArithmeticUnitCorestriction_primeInvariant_originalPrimes a p.val p.property F y).trans
    (Finset.sum_congr rfl (fun w _ => (rationalArithmeticOriginalPrimeInvariant_fiber a F y p w.val w.property).symm))

/-- The sum over any finite support of the genuine original-prime invariants of an actual odd-primary class vanishes. -/
theorem rationalArithmeticOriginalPrimeInvariant_sum_zero
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (hy : q ^ (r + 1) • (Submodule.Quotient.mk y : GaloisUnitContinuousH2
      (K := F) (Ω := rationalUnramifiedExtension a)) = 0)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hT : ∀ w ∉ T, rationalArithmeticOriginalPrimeInvariant a F y w = 0) :
    (∑ w ∈ T, rationalArithmeticOriginalPrimeInvariant a F y w) = 0 := by
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
  have hz := rationalArithmeticUnitPrimeInvariant_sum_zero a q r hq hq2 hqa x hx P hP
  calc
    _ = ∑ p ∈ P, ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
          originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property},
          rationalArithmeticOriginalPrimeInvariant a F y w.val :=
      (rationalArithmeticOriginalPrimeFiber_sum a F
        (rationalArithmeticOriginalPrimeInvariant a F y) T hT).symm
    _ = ∑ p ∈ P, rationalArithmeticUnitPrimeInvariant a p.val p.property x :=
      Finset.sum_congr rfl (fun p _ => (rationalArithmeticOriginalPrimeInvariant_fiber_sum a F y p).symm)
    _ = 0 := hz

end
end Dubon2026
