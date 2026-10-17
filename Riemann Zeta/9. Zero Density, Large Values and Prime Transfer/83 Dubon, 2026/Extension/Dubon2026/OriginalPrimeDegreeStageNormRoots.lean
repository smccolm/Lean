import Dubon2026.OriginalConstructedStageNormRoots
import Dubon2026.OriginalCyclotomicNormDegreeStage

/-! # The enlarged norm-root stage has prime-divisible relative degree

A proved cyclotomic stage contributes a sufficiently large prime-power
divisor to the absolute degree. Enlarge above that stage and the original
prescribed stage using the constructed norm field. The actual degree
tower forces prime divisibility of the relative degree, which is the
degree condition in DUB-17's finite relation-extension argument.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (E Ω : Type) [Field E] [NumberField E] [Field Ω]
  [Algebra ℚ Ω] [Algebra E Ω] [IsScalarTower ℚ E Ω] [IsAlgClosure ℚ Ω]

/-- The actual original norm-root stage can be chosen with the
coefficient prime dividing its relative degree, while preserving the
original base embedding and every prescribed earlier stage. -/
theorem originalNumberField_exists_prime_degree_stage_norm_roots
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (hBase : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 ℚ) (𝓞 E) a ∉ v.asIdeal →
      (v.asIdeal.under (𝓞 ℚ)).ramificationIdx v.asIdeal = 1) :
    let S := originalExceptionalIntegerSupport E (algebraMap (𝓞 ℚ) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      letI : Algebra ℚ N.val := N.val.algebra'
      ∃ j : E →ₐ[ℚ] N.val,
        (∀ x : E, (j x : Ω) = algebraMap E Ω x) ∧
        P.val.toIntermediateField ≤ N.val.toIntermediateField ∧
        letI : Algebra E N.val := j.toRingHom.toAlgebra
        letI : IsScalarTower ℚ E N.val := IsScalarTower.of_algHom j
        letI : FiniteDimensional E N.val := FiniteDimensional.right ℚ E N.val
        p ∣ Module.finrank E N.val ∧
          OriginalOutsideQuotientInvariantNormRoots E N.val S p := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨R, hR⟩ := originalCyclotomic_exists_norm_degree_stage Ω a ha p
    (Fact.out : p.Prime) hpa (Module.finrank ℚ E)
  let Q : OriginalUnramifiedGaloisStage (Ω := Ω) a :=
    ⟨R.val ⊔ P.val, finiteGalois_sup_unramified a ha R.val P.val R.property P.property⟩
  obtain ⟨N, j, hj, hQN, hRoots⟩ :=
    originalNumberField_exists_enlarged_stage_norm_roots E Ω a ha Q p hp2 ζ hζ hBase
  letI : Algebra ℚ N.val := N.val.algebra'
  letI : Algebra E N.val := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ E N.val := IsScalarTower.of_algHom j
  letI : FiniteDimensional E N.val := FiniteDimensional.right ℚ E N.val
  have hRN : R.val.toIntermediateField ≤ N.val.toIntermediateField := le_sup_left.trans hQN
  have hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField := le_sup_right.trans hQN
  letI : Algebra ℚ R.val := R.val.algebra'
  let i := IntermediateField.inclusion hRN
  letI : Algebra R.val N.val := i.toRingHom.toAlgebra
  letI : Module R.val N.val := Algebra.toModule
  letI : SMul R.val N.val := i.toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ R.val N.val := IsScalarTower.of_algHom i
  letI : FiniteDimensional R.val N.val := FiniteDimensional.right ℚ R.val N.val
  letI : Module.Free R.val N.val := Module.Free.of_divisionRing R.val N.val
  have hdvd : Module.finrank ℚ R.val ∣ Module.finrank ℚ N.val :=
    ⟨Module.finrank R.val N.val, (Module.finrank_mul_finrank ℚ R.val N.val).symm⟩
  have hbig := hR.trans hdvd
  rw [← Module.finrank_mul_finrank ℚ E N.val] at hbig
  exact ⟨N, j, hj, hPN,
    originalRelativeDegree_prime_dvd_of_absolute_power p (Module.finrank ℚ E)
      (Module.finrank E N.val) (Fact.out : p.Prime) Module.finrank_pos hbig, hRoots⟩

end
end Dubon2026
