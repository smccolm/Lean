import Dubon2026.OriginalPrimitiveRootNormBase
import Dubon2026.OriginalPrimeDegreeStageNormRoots

/-! # Constructed norm-root towers above the original arithmetic stage

The primitive root is now constructed in an actual enlarged Galois base.
The norm field then constructs a second actual stage with prime-divisible
relative degree and invariant quotient norm roots. The ambient embedding
identifies the returned map with literal intermediate-field inclusion.
These are the field and norm data needed for DUB-17's normal-subgroup
relation-extension argument; its coefficient and cohomology comparisons
remain separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/-- Above every original arithmetic stage are literal finite Galois
stages with the required prime-divisible relative degree and invariant
norm roots. No primitive root or auxiliary field is supplied. -/
theorem originalUnramifiedStage_exists_norm_root_tower
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a) :
    ∃ E N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      P.val.toIntermediateField ≤ E.val.toIntermediateField ∧
      ∃ hEN : E.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra ℚ E.val := E.val.algebra'
        letI : Algebra ℚ N.val := N.val.algebra'
        letI : Algebra E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
        letI : Module E.val N.val := Algebra.toModule
        letI : SMul E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra.toSMul
        letI : IsScalarTower ℚ E.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
        letI : FiniteDimensional E.val N.val := FiniteDimensional.right ℚ E.val N.val
        p ∣ Module.finrank E.val N.val ∧
          OriginalOutsideQuotientInvariantNormRoots E.val N.val
            (originalExceptionalIntegerSupport E.val (algebraMap (𝓞 ℚ) (𝓞 E.val) a)
              (originalIntegerMap_ne_zero (L := E.val) a ha)) p := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hPE, ζ, hζ⟩ := originalUnramifiedStage_exists_primitive_root_base Ω a ha P p
    (Fact.out : p.Prime) hpa
  have hEAlg : (E.val.algebra' : Algebra ℚ E.val) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have hBase := E.property
  rw [hEAlg] at hBase
  letI : Algebra ℚ E.val := DivisionRing.toRatAlgebra
  letI : IsScalarTower ℚ E.val Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have h := originalNumberField_exists_prime_degree_stage_norm_roots
    E.val Ω a ha E p hp2 hpa ζ hζ hBase
  rw [← hEAlg] at h
  letI : Algebra ℚ E.val := E.val.algebra'
  obtain ⟨N, j, hj, _, hdeg, hroot⟩ := h
  letI : Algebra ℚ N.val := N.val.algebra'
  have hEN : E.val.toIntermediateField ≤ N.val.toIntermediateField := by
    intro x hx
    have hz := (j ⟨x, hx⟩).property
    rw [hj] at hz
    exact hz
  have hjEq : j = IntermediateField.inclusion hEN := by
    ext x
    exact hj x
  subst j
  exact ⟨E, N, hPE, hEN, hdeg, hroot⟩

end
end Dubon2026
