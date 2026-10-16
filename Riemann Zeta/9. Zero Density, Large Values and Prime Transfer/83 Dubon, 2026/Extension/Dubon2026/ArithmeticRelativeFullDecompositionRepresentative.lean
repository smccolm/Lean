import Dubon2026.ArithmeticRelativeStageCocycles
import Dubon2026.ArithmeticOriginalPrimeInvariant
import Dubon2026.ArithmeticOrbitPrimeSurjectivity
import Dubon2026.OriginalCyclicPrimePowerFullDecomposition

/-! # A genuine full-decomposition prime with an arithmetic representative

The native cyclic prime-power theorem constructs the upper prime. The
already proved arbitrary-field prime-surjectivity theorem realizes that
same prime by an actual arithmetic automorphism. This is the source
prime for DUB-17's normalized auxiliary class; no prime is postulated.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- An actual cyclic prime-power relative stage has a full-decomposition prime selected by an actual arithmetic representative. -/
theorem rationalArithmeticRelativeStage_exists_fullDecomposition_representative
    (q n : ℕ) (hq : q.Prime) (hn : 0 < n)
    (hcyclic : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsCyclic Gal(H/F))
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ n) :
    ∃ (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a),
      letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      OriginalFiniteDecompositionGroup F H
        (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)) = ⊤ := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : IsCyclic Gal(H/F) := hcyclic
  obtain ⟨w, _, hw⟩ := original_cyclicPrimePower_exists_fullDecomposition_outside F H
    q n hq hn hdegree ∅
  let p := rationalArithmeticOriginalPrimeBase a H w
  obtain ⟨c, hc⟩ := rationalArithmeticOrbitPrime_surjective a p.val p.property H w
    (rationalArithmeticOriginalPrimeBase_below a H w)
  have hrep : (QuotientGroup.mk c.out :
      rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H) = c :=
    Quotient.out_eq' c
  have he : rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out) = w :=
    (congrArg (rationalArithmeticOrbitPrime a p.val p.property H) hrep).trans hc
  refine ⟨p.val, p.property, c.out, ?_⟩
  exact he.symm ▸ hw

end
end Dubon2026
