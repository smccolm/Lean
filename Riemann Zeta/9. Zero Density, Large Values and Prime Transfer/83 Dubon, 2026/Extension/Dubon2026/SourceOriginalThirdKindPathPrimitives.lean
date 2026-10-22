import Dubon2026.SourceOriginalRegularPathPrimitives
import Dubon2026.SourceOriginalPrescribedResidues

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
period correction and meromorphic exponential. The actual prescribed-residue
differential has a primitive along every path avoiding its divisor support.
Both the differential and the local regularity along those paths are
derived. The remaining loop-period normalization is a separate obligation.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem exists_original_third_kind_with_path_primitives
    (D : Divisor ℂ F) (hD : Divisor.degree D = 0) :
    ∃ η : Ω[F⁄ℂ], (∀ v : Place ℂ F, -1 ≤ v.ordDifferential η ∧
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ)) ∧
      ∀ (P Q : Place ℂ F) (γ : Path P Q), (∀ t, D (γ t) = 0) →
        ∃ g, IsPrimitiveAlong N η γ g := by
  obtain ⟨η, hη, hres⟩ := exists_original_differential_with_prescribed_residues N D hD
  refine ⟨η, fun v => ⟨hη v,
    (originalDifferentialResidue_simplePole N v η (hη v)).symm.trans (hres v)⟩, ?_⟩
  intro P Q γ hγ
  apply exists_isPrimitiveAlong_of_simplePole_residue_zero N η hη γ
  intro t
  rw [hres, hγ, Int.cast_zero]

end
end Dubon2026.SourceFunctionField.OriginalChart
