import Dubon2026.SourceOriginalResidueFullCuspChart
import Dubon2026.SourceResidueAllLevelInduction

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> comparison with the actual full-base cusp.
The native all-level two-generator theorem makes the two proved coordinates
sufficient to identify the restriction of the original residue cusp map. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open CongruenceSubgroup GammaOne IntegralDiamond
open scoped MatrixGroups

theorem fullBase_algHom_ext (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
    (hN : (N : K) ≠ 0) {L : Type*} [Field L] [Algebra K L]
    (φ ψ : modularFunctionFieldCoeff N K →ₐ[K] L)
    (hj : φ (jCoeff N K) = ψ (jCoeff N K))
    (hjN : φ ⟨jqNModC K N, jqd_mem_coeff_field N K (dvd_refl N)⟩ =
      ψ ⟨jqNModC K N, jqd_mem_coeff_field N K (dvd_refl N)⟩) : φ = ψ := by
  apply IntermediateField.algHom_ext_of_eq_adjoin K (residue_full_generation_and_degree N hN).1
  rintro x (rfl | hx)
  · exact hj
  · rcases hx with rfl
    exact hjN

end
end Dubon2026.SourceFunctionField.IntegralSlash
