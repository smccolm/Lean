import Dubon2026.ArithmeticRelativeFullDecompositionRepresentative
import Dubon2026.ArithmeticRelativeNormalizedRepresentativeLift
import Dubon2026.ArithmeticRelativeStageIdeleRepresentativeValues

/-! # Construct the actual auxiliary class with all representative values

The full-decomposition prime and its arithmetic representative are proved
to exist. Lift the normalized local class at that prime and use actual
prime support and closure independence to compute every representative
value. This supplies DUB-17's auxiliary class for canonical total assembly
without assuming its normalization or its values at other primes.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Every actual cyclic prime-power relative stage has a constructed single-prime idele class whose value at every arithmetic representative is exactly the reciprocal-degree indicator of its original base prime. -/
theorem rationalArithmeticRelativeStage_exists_single_prime_invariant_lift
    (q r : ℕ) (hq : q.Prime)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ (r + 1)) :
    ∃ (p₀ : ℕ) (hp₀ : p₀.Prime) (σ₀ : rationalArithmeticGaloisGroup a)
      (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH),
      ∃ hw : (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra;
        OriginalFiniteDecompositionGroup F H
          (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) = ⊤),
      (∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
        rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x =
          if rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ) =
              rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀) then
            (↑((1 : ℚ) / (q ^ (r + 1) : ℕ)) : AddCircle (1 : ℚ)) else 0) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra;
        ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
          t ≠ rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀) →
            originalFullIdeleAdicH2 F H t x = 0) ∧
      (letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
        ∃ y : groupCohomology (originalAdicUnitRep F H
            (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀))) 2,
          x = originalFullDecompositionIdeleH2Lift F H
            (rationalArithmeticOrbitPrime a p₀ hp₀ H (QuotientGroup.mk σ₀)) hw y) := by
  obtain ⟨p₀, hp₀, σ₀, hw⟩ := rationalArithmeticRelativeStage_exists_fullDecomposition_representative
    a F H hFH q (r + 1) hq (by omega) hcyclic hdegree
  obtain ⟨x, hx, hs, hy⟩ := rationalArithmeticRelativeStageIdeleRepresentativeInvariant_exists_normalized_lift
    a p₀ hp₀ F H hFH σ₀ (q ^ (r + 1)) hdegree hw
  refine ⟨p₀, hp₀, σ₀, x, hw, ?_, hs, hy⟩
  intro p hp σ
  by_cases h : rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ) =
      rationalArithmeticOrbitPrime a p₀ hp₀ F (QuotientGroup.mk σ₀)
  · rw [if_pos h]
    exact (rationalArithmeticRelativeStageIdeleRepresentativeInvariant_same_base
      a F H hFH p₀ hp₀ σ₀ p hp σ hw h x).trans hx
  · rw [if_neg h]
    exact rationalArithmeticRelativeStageIdeleRepresentativeInvariant_other_base
      a F H hFH p₀ hp₀ σ₀ p hp σ x hs h

end
end Dubon2026
