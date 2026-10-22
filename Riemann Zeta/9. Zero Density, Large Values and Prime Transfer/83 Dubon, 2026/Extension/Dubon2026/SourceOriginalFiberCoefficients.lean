import Dubon2026.SourceOriginalNonconstantDifferential
import Dubon2026.SourceOriginalSimpleFiberSum

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> the simple-fiber residue sum. Select coefficients for
the given finite family of actual regular differentials relative to Df,
retaining their proved regularity. Nonvanishing of Df is already derived
from nonconstancy, rather than supplied as a further hypothesis.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The native module structure on original differentials, retained for contour coefficient elaboration. -/
abbrev originalFiberDifferentialModule : Module F Ω[F⁄ℂ] := inferInstance

theorem original_regular_fiber_coefficients {n : ℕ}
    (b : Fin n → regularDifferentials ℂ F) {f : F}
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) :
    ∃ h : Fin n → F, (∀ i, (b i : Ω[F⁄ℂ]) = h i • D ℂ F f) ∧
      ∀ i, h i • D ℂ F f ∈ regularDifferentials ℂ F := by
  choose h hh using fun i => original_differential_eq_smul_D N hfc (b i : Ω[F⁄ℂ])
  exact ⟨h, hh, fun i => (hh i) ▸ (b i).property⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
