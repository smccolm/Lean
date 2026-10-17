import Dubon2026.ArithmeticRelativeAllPrimeClassInvariant
import Dubon2026.ArithmeticDivisorBaseChangeZeroTotal
import Dubon2026.ArithmeticRelativeStageClassProjection

/-! # Kill the scaled primary class in the actual auxiliary field

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
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

/-- In an actual prime-power cyclic target stage, the scaled base change of the source single-prime class has zero original idele-class image. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_divisor_class_zero_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hcyclic : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsCyclic Gal(M/E))
    (hdegree : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ (r + 1))
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (d n : ℕ) (hn : 0 < n) (hdn : d ∣ n)
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      d ∣ Module.finrank K E)
    (hx : ∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp K L hKL σ x =
        if rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) = v then
          (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) else 0)
    (hInf : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      ∀ v : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 E M v
        (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    rationalArithmeticRelativeStageClassProjection a E M hEM
      ((n / d) •
        rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  apply (rationalArithmeticRelativeStage_class_zero_iff_total_of_infinite
    a E M hEM q r hq hqa hcyclic hdegree _ ?_).mpr
  · exact rationalArithmeticRelativeStageIdeleBaseChange_divisor_scaled_total_zero
      a K E L M hKE hKL hEM hLM x v d n hn hdn hd hx
  · intro w
    exact (map_nsmul (originalFullIdeleInfiniteH2 E M w).hom (n / d)
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x)).trans
      ((congrArg (fun z => (n / d) • z) (hInf w)).trans (nsmul_zero _))

end
end Dubon2026
