import Dubon2026.LocalFieldFiniteStageFundamentalClass

/-! # Original relative fundamental classes under genuine field inflation -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Inflating the original relative fundamental class through a
finite tower multiplies the upper fundamental class by the relative
field degree. The map is the original cocycle inflation. -/
theorem localFieldFiniteStageFundamentalClass_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (localFieldFiniteStageFundamentalClass K Ω E) =
      Module.finrank E F • localFieldFiniteStageFundamentalClass K Ω F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  haveI : FiniteDimensional E F := FiniteDimensional.right K E F
  apply localFieldFiniteStageInvariant_injective K Ω F
  rw [localFieldFiniteStageInvariant_transition, map_nsmul,
    localFieldFiniteStageFundamentalClass_invariant, localFieldFiniteStageFundamentalClass_invariant]
  rw [← AddCircle.coe_nsmul]
  congr 1
  have hd := Module.finrank_mul_finrank K E F
  have he : (Module.finrank K E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hf : (Module.finrank E F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [← hd, Nat.cast_mul, nsmul_eq_mul]
  field_simp

end
end Dubon2026
