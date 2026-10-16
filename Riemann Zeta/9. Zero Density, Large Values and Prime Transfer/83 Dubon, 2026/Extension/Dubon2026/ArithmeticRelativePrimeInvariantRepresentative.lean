import Dubon2026.ArithmeticRelativeIdeleRepresentativeIndependence
import Dubon2026.ArithmeticRelativeStageIdelePrimeRepresentative

/-! # The canonical prime invariant at every arithmetic representative

Prime-choice independence identifies the canonical original-prime value
with every representative over that prime. This supplies DUB-17's
normalization comparison without a full-decomposition hypothesis.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- The actual canonical prime invariant equals the actual representative invariant at every representative over that prime. -/
theorem rationalArithmeticRelativeStageIdelePrimeInvariant_eq_representative
    (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a)
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)) x =
        rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x := by
  obtain ⟨p₀, hp₀, σ₀, hv, hi⟩ :=
    rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative a F H hFH
      (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ))
  exact (congrArg (fun f => f x) hi).trans
    (rationalArithmeticRelativeStageIdeleRepresentativeInvariant_prime_independent
      a F H hFH p hp σ p₀ hp₀ σ₀ hv x)

end
end Dubon2026
