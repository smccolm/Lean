import Dubon2026.SpectralFiniteStageFundamentalClass

/-! # Original relative fundamental classes under genuine field inflation -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Genuine original inflation preserves the full finite-stage invariant. -/
theorem spectralFiniteStageFullInvariant_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    (x : GaloisUnitH2FiniteStage K Ω E) :
    spectralFiniteStageFullInvariant K Ω F (galoisUnitH2FiniteTransition K Ω E F hEF x) =
      spectralFiniteStageFullInvariant K Ω E x := by
  change spectralContinuousH2InvariantLinear K Ω
    (galoisUnitH2FiniteStageMap K Ω F (galoisUnitH2FiniteTransition K Ω E F hEF x)) = _
  rw [galoisUnitH2FiniteStageMap_transition]
  rfl

/-- Inflating the original relative fundamental class through a
finite tower multiplies the upper fundamental class by the relative
field degree. The map is the original cocycle inflation. -/
theorem spectralFiniteStageFundamentalClass_transition
    (E F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    galoisUnitH2FiniteTransition K Ω E F hEF (spectralFiniteStageFundamentalClass K Ω E) =
      Module.finrank E F • spectralFiniteStageFundamentalClass K Ω F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  haveI : FiniteDimensional E F := FiniteDimensional.right K E F
  apply spectralFiniteStageFullInvariant_injective K Ω F
  rw [spectralFiniteStageFullInvariant_transition, map_nsmul,
    spectralFiniteStageFundamentalClass_invariant, spectralFiniteStageFundamentalClass_invariant]
  rw [← AddCircle.coe_nsmul]
  congr 1
  have hd := Module.finrank_mul_finrank K E F
  have he : (Module.finrank K E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hf : (Module.finrank E F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [← hd, Nat.cast_mul, nsmul_eq_mul]
  field_simp

end
end Dubon2026
