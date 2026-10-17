import Dubon2026.OriginalPrimeDegreeStageNormRoots
import Dubon2026.ArithmeticRelativeOutsideClassSupport

/-! # Actual arithmetic enlarged-stage invariant norm roots

The original finite subfield of the fixed arithmetic union supplies its
ramification condition and its literal ambient embedding. The constructed
norm field and cyclotomic enlargement therefore give invariant roots of
every actual quotient norm at a genuine enlarged stage, with coefficient
prime dividing the relative degree. This is the finite-stage norm-root
input to DUB-17's relation extension; no norm-field, normalization,
ramification, placement or degree-divisibility certificate is supplied.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The original arithmetic finite base has an actual enlarged Galois
stage with prime-divisible relative degree and invariant roots of every
literal outside-unit quotient norm, preserving the original embedding. -/
theorem rationalArithmetic_exists_enlarged_stage_invariant_norm_roots
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
    (P : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ζ : F) (hζ : IsPrimitiveRoot ζ p) :
    let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)
    ∃ N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a,
      letI : Algebra ℚ N.val := N.val.algebra'
      ∃ j : F →ₐ[ℚ] N.val,
        (∀ x : F, (j x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ)) ∧
        P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
        letI : Algebra F N.val := j.toRingHom.toAlgebra
        letI : Module F N.val := Algebra.toModule
        letI : SMul F N.val := j.toRingHom.toAlgebra.toSMul
        letI : IsScalarTower ℚ F N.val := IsScalarTower.of_algHom j
        letI : FiniteDimensional F N.val := FiniteDimensional.right ℚ F N.val
        p ∣ Module.finrank F N.val ∧
          OriginalOutsideQuotientInvariantNormRoots F N.val S p := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.instIsAlgClosure ℚ
    rw [hAlg] at h
    exact h
  let i : F →ₐ[ℚ] AlgebraicClosure ℚ := (rationalUnramifiedExtension a).val.comp F.val
  letI : Algebra F (AlgebraicClosure ℚ) := i.toRingHom.toAlgebra
  letI : IsScalarTower ℚ F (AlgebraicClosure ℚ) := IsScalarTower.of_algHom i
  exact originalNumberField_exists_prime_degree_stage_norm_roots
    F (AlgebraicClosure ℚ) a ha P p hp2 hpa ζ hζ
    (originalUnramifiedUnion_finite_ramification a ha F)

end
end Dubon2026
