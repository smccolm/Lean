import Dubon2026.SourceWeightTwoJacobiInversion
import Dubon2026.SourceGammaOneRealPeriodMap

/-! DUB17/18 -> actual Gamma1 Picard-period comparison -> Jacobi inversion.
The already proved finiteness of the actual real period map supplies the
finite complex cusp basis. Every functional on the original Gamma1 cusp
space is therefore an actual finite degree-zero divisor endpoint integral. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

theorem exists_analytic_divisor_endpoint_functional (N : ℕ) [NeZero N]
    (u : Module.Dual ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)) :
    ∃ c : ℍ →₀ ℤ, c.sum (fun _ a => a) = 0 ∧
      c.sum (fun τ a => a • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) = u := by
  classical
  let V := CuspForm ((Gamma1 N).map (mapGL ℝ)) 2
  letI := sourceGamma1CuspForm_finite_real N
  letI : IsScalarTower ℝ ℂ V := ⟨fun r z f => by
      ext τ
      simp only [smul_assoc]⟩
  letI : Module.Finite ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  exact SourceWeightTwoJacobi.exists_degree_zero_endpoint_functional
    (Gamma1 N) (Module.finBasis ℂ V) u

end
end Dubon2026.SourceFunctionField.GammaOne
