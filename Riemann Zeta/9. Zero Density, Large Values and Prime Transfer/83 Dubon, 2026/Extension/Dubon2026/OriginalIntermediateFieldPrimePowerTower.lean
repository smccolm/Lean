import Dubon2026.OriginalCyclicAuxiliaryComposita

/-! # The actual prime-power degree of the common arithmetic tower

The standard tower formula proves the degree needed for principal
reciprocity in the common field. This discharges the remaining degree
premise in DUB-17's comparison of the target and auxiliary idele totals.
-/
namespace Dubon2026
noncomputable section
attribute [-instance] SubfieldClass.instSMulRat

/-- Literal intermediate fields with prime-power degrees in two successive steps have the required prime-power common-field degree. -/
theorem originalIntermediateField_primePower_tower_degree
    (U : Type) [Field U] [Algebra ℚ U]
    (K E M : IntermediateField ℚ U)
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] [FiniteDimensional ℚ M]
    (hKE : K ≤ E) (hEM : E ≤ M) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    letI : Module E M := Algebra.toModule
    letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    letI : Module K M := Algebra.toModule
    ∀ q t s : ℕ, Module.finrank K E = q ^ t → Module.finrank E M = q ^ s →
      Module.finrank K M = q ^ (t + s) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  intro q t s hKEdeg hEMdeg
  exact (Module.finrank_mul_finrank K E M).symm.trans (by rw [hKEdeg, hEMdeg, pow_add])

end
end Dubon2026
