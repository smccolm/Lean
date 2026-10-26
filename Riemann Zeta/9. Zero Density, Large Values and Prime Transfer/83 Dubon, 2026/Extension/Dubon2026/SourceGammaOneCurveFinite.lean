import Dubon2026.SourceGammaOneFunctionFieldBaseChange

/-! DUB-17/18 -> arithmetic realization of original finite Gamma1 characters ->
actual Gamma1 and Hecke-correspondence function fields. Native congruence
subgroup facts discharge finite index and the translation condition. The
coordinate is the original j, over the actual rational or scalar-extended
integral-ratio field. No geometric Galois comparison is asserted here. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField CongruenceSubgroup
open scoped MatrixGroups

theorem gamma1_finite_coordinate (M : ℕ) [NeZero M]
    (L : Type*) [Field L] [Algebra ℚ L] :
    ∃ x : laurentBaseChange L (x1FunctionField M), Transcendental L x ∧
      FiniteDimensional
        (IntermediateField.adjoin L
          ({x} : Set (laurentBaseChange L (x1FunctionField M))))
        (laurentBaseChange L (x1FunctionField M)) := by
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  exact ⟨jCoordinateOver (Gamma1 M) L, transcendental_jCoordinateOver (Gamma1 M) L,
    finiteDimensional_jCoordinateOver hT L⟩

theorem gamma1_hecke_finite_coordinate (M t : ℕ) [NeZero M] [NeZero t]
    (L : Type*) [Field L] [Algebra ℚ L] :
    ∃ x : laurentBaseChange L (x1x0FunctionFieldC ℚ M t), Transcendental L x ∧
      FiniteDimensional
        (IntermediateField.adjoin L
          ({x} : Set (laurentBaseChange L (x1x0FunctionFieldC ℚ M t))))
        (laurentBaseChange L (x1x0FunctionFieldC ℚ M t)) := by
  have hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 t := by
    constructor <;> simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]
  exact ⟨jCoordinateOver (Gamma1 M ⊓ Gamma0 t) L,
    transcendental_jCoordinateOver (Gamma1 M ⊓ Gamma0 t) L,
    finiteDimensional_jCoordinateOver hT L⟩

/-- The actual scalar-extended inclusion underlying the first Hecke map. -/
theorem gamma1_hecke_baseChange_le (M t : ℕ)
    (L : Type*) [Field L] [Algebra ℚ L] :
    laurentBaseChange L (x1FunctionField M) ≤
      laurentBaseChange L (x1x0FunctionFieldC ℚ M t) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L ((x1FunctionFieldC_le_x1x0 ℚ M t) hy)

end
end Dubon2026.SourceFunctionField.GammaOne
