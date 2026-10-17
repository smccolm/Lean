import Dubon2026.ArithmeticNonNormalBaseChangeTotal
import Dubon2026.ArithmeticOddPrimePowerTotalDetectsClass

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup

/-- A zero canonical total gives zero of the actual class image after
restriction to an odd prime-power intermediate-field extension of the same
Galois upper field. No normality of the lower intermediate field is assumed.
The required Sylow fixed field supplies the prime-power degree in the source
obstruction argument; its total still must be identified with the local cup sum. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_odd_primary_class_zero
    (a : 𝓞 ℚ) (K E M : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] [FiniteDimensional ℚ M]
    (hKE : K ≤ E) (hEM : E ≤ M)
    [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
      IsGalois K M]
    [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      IsGalois E M]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
      letI : Module E M := Algebra.toModule
      Module.finrank E M = q ^ t)
    (x : rationalArithmeticRelativeStageIdeleH2 a K M (hKE.trans hEM))
    (hx : rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM) x = 0) :
    letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      (rationalArithmeticRelativeStageIdeleBaseChange a K E M M hKE (hKE.trans hEM) hEM le_rfl x) = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  let y := rationalArithmeticRelativeStageIdeleBaseChange a K E M M
    hKE (hKE.trans hEM) hEM le_rfl x
  have ht := rationalArithmeticRelativeStageIdeleBaseChange_total_in_galois_overfield
    (hGalKM := hGalKM) (hGalEM := hGalEM) a K E M hKE hEM x
  have hy : rationalArithmeticRelativeStageIdeleTotalInvariant a E M hEM y = 0 :=
    ht.trans ((congrArg (fun z => Module.finrank K E • z) hx).trans (nsmul_zero _))
  exact (rationalArithmeticRelativeOddPrimePower_total_zero_iff_class_zero
    (hGalKE := hGalEM) a E M hEM q t hq hq2 hqa hdegree y).mp hy

end
end Dubon2026
