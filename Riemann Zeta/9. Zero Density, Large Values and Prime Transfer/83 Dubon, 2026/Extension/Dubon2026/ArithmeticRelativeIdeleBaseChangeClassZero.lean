import Dubon2026.ArithmeticRelativeIdeleBaseChangeZeroTotal
import Dubon2026.ArithmeticRelativeStageClassProjection

/-! # Vanishing of the actual scaled auxiliary class

The proved canonical zero total and the injective original class invariant
kill the same actual scaled base change. This is the class-level premise
needed by DUB-17 before comparison with subgroup restriction.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- In an actual odd-primary cyclic target stage, the scaled base change of the source single-prime class has zero original idele-class image. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_scaled_class_zero
    (q r : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsCyclic Gal(M/E))
    (hdegree : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ n)
    (hx : ∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x =
        if rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) = v then
          (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) else 0) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    rationalArithmeticRelativeStageClassProjection a E M hEM
      ((n / Module.finrank K E) •
        rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact rationalArithmeticRelativeStageClassProjection_zero_of_total
    a E M hEM q r hq hq2 hqa hcyclic hdegree _
    (rationalArithmeticRelativeStageIdeleBaseChange_scaled_total_zero
      a K E L M hKE hKL hEM hLM x v n hn hd hx)

end
end Dubon2026
