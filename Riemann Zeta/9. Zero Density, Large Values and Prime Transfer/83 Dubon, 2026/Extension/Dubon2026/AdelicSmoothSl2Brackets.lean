import Dubon2026.RealSmoothSl2Brackets
import Dubon2026.AdelicSmoothGeodesicBrackets

/-! # All original sl2 infinitesimal operators on the actual adelic smooth subspace -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- Original adelic upper and lower smooth infinitesimals have bracket twice the original geodesic action. -/
theorem adelicSmoothInfinitesimal_upper_lower {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff *
        adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff -
      adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff *
        adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff =
      (2 : ℂ) • adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal_upper_lower (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl)

/-- The actual original adelic compact derivative is exactly upper minus lower on every genuine smooth vector. -/
theorem adelicSmoothInfinitesimal_compact {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff =
      adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff -
        adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal_compact (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl)

end
end Dubon2026
