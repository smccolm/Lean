import Dubon2026.AdelicSmoothSl2Brackets
import Dubon2026.Sl2CasimirAlgebra

/-! # Actual normalized second-order operator commutation on original adelic smooth vectors -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

local notation "A" => adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff
local notation "U" => adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff
local notation "F" => adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff

/-- The original actual second-order endomorphism is precisely the normalized sl2 quadratic expression. -/
theorem adelicSmoothCasimirOperator_eq_normalized :
    adelicSmoothCasimirOperator f = normalizedSl2Casimir A U F :=
  normalizedSl2Casimir_eq_compact A U F
    (adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff)
    (adelicSmoothInfinitesimal_compact f)

/-- The original second-order endomorphism commutes with each original real infinitesimal generator on the full actual smooth subspace. -/
theorem adelicSmoothCasimirOperator_commutes :
    Commute (adelicSmoothCasimirOperator f) A ∧
      Commute (adelicSmoothCasimirOperator f) U ∧ Commute (adelicSmoothCasimirOperator f) F := by
  have hUF : U * F - F * U = A + A :=
    (adelicSmoothInfinitesimal_upper_lower f).trans (two_smul ℂ A)
  have he := normalizedSl2Casimir_commutes A U F
    (adelicSmoothInfinitesimal_geodesic_upper f) (adelicSmoothInfinitesimal_geodesic_lower f) hUF
  simpa only [adelicSmoothCasimirOperator_eq_normalized] using he

end
end Dubon2026
