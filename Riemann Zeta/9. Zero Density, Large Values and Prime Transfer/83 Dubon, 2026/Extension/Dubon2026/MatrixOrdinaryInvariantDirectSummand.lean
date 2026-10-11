import Dubon2026.MatrixTwoOrdinaryInvariantLine
import Dubon2026.SubmoduleCoordinateLineSplitting
import Dubon2026.MatrixAdjointSchur

/-! # Original ordinary relations yield a genuine free rank-one invariant direct summand -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R K : Type*} [Group G] [CommRing R] [Field K]

/-- For the actual original column representation, ordinary matrix relations and a nonidentity residual element derive a free rank-one module of invariants and an actual complementary submodule of the original two-dimensional coefficient module. -/
theorem matrixOrdinary_invariants_rankOne_directSummand (r : R →+* K) [IsLocalHom r]
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (g₀ : G) (hρ : GeneralLinearGroup.map r (ρ g₀) ≠ 1)
    (hrel : ∀ g, ((ρ g).val - 1) *
      ((ρ g₀).val - (GeneralLinearGroup.det (ρ g₀) : R) • (1 : Matrix (Fin 2) (Fin 2) R)) = 0) :
    Nonempty ((matrixStandardRepresentation ρ).invariants ≃ₗ[R] R) ∧
      ∃ N : Submodule R (Fin 2 → R), IsCompl (matrixStandardRepresentation ρ).invariants N := by
  obtain ⟨U, hU⟩ := matrixTwo_invariant_line_of_ordinary_relations r ρ g₀ hρ hrel
  let e : (Fin 2 → R) ≃ₗ[R] R × R :=
    (GeneralLinearGroup.toLin U⁻¹).toLinearEquiv.trans (LinearEquiv.finTwoArrow R R)
  apply submodule_rankOne_split_of_coordinates (matrixStandardRepresentation ρ).invariants e
  intro v
  exact hU v

end
end Dubon2026
