import Dubon2026.ArithmeticRelativeStageIdelePrimeRepresentative
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

/-! # The canonical total of the constructed single-prime class

Compute the total of the same class from its proved representative
values. This supplies the normalization needed to prove full order of
DUB-17's chosen auxiliary class, rather than choosing an unrelated class.
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

/-- The canonical total of the actual single-prime class equals its one nonzero representative value. -/
theorem rationalArithmeticRelativeStageIdeleTotalInvariant_of_representative_values
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z : AddCircle (1 : ℚ))
    (hx : ∀ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      rationalArithmeticRelativeStageIdeleRepresentativeInvariant a p hp F H hFH σ x =
        if rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ) = v then z else 0) :
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH x = z := by
  have hf (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH w x =
        if w = v then z else 0 := by
    obtain ⟨p, hp, σ, hw, hi⟩ :=
      rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative a F H hFH w
    rw [hi, hx p hp σ, hw]
  calc
    _ = rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH v x := by
      rw [rationalArithmeticRelativeStageIdeleTotalInvariant_apply]
      apply finsum_eq_single
      intro w hw
      rw [hf, if_neg hw]
    _ = z := (hf v).trans (if_pos rfl)

end
end Dubon2026
