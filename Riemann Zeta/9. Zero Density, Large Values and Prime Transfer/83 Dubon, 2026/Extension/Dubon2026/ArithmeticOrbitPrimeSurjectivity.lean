import Dubon2026.ArithmeticOrbitNormalPrimeSurjectivity
import Dubon2026.ArithmeticOrbitPrimeContraction

/-! # Every original prime of an arbitrary finite arithmetic field occurs

Take the finite normal closure inside the same original unramified union.
The existing lying-over theorem and the proved normal-stage surjectivity
give an upper coset; the literal contraction comparison gives the required
lower coset. This removes the remaining prime-surjectivity premise on
DUB-17's route from the rational Mackey formula to number-field reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- Every original prime above the chosen rational prime is induced by an actual coset, without assuming the finite global field is normal. -/
theorem rationalArithmeticOrbitPrime_surjective
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : originalIntegerPrimeBelow F w = rationalPrimePlace p hp) :
    ∃ c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F,
      rationalArithmeticOrbitPrime a p hp F c = w := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  let H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a) :=
    ⟨IntermediateField.normalClosure ℚ F (rationalUnramifiedExtension a)⟩
  have hFH : F ≤ H.toIntermediateField := IntermediateField.le_normalClosure F
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : NumberField H := NumberField.of_module_finite ℚ H
  obtain ⟨v, hv⟩ := originalFinitePrimeBelow_surjective F H w
  have hvp : originalIntegerPrimeBelow H v = rationalPrimePlace p hp :=
    (originalIntegerPrimeBelow_tower F H v).symm.trans
      ((congrArg (originalIntegerPrimeBelow F) hv).trans hw)
  obtain ⟨c, hc⟩ := rationalArithmeticOrbitPrime_surjective_of_normal a p hp H.toIntermediateField v hvp
  refine ⟨QuotientGroup.mk c.out, ?_⟩
  exact (rationalArithmeticOrbitPrime_under a p hp F H.toIntermediateField hFH c).symm.trans
    ((congrArg (originalFinitePrimeBelow F H) hc).trans hv)

end
end Dubon2026
