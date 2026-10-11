import Dubon2026.MatrixOrdinaryInvariantDirectSummand
import Dubon2026.MatrixTwoOrdinaryRelationConverse
import Dubon2026.SubmoduleRankOnePrimitiveVector

/-! # The actual original ordinary invariant-summand condition and its exact matrix relations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R K : Type*} [Group G] [CommRing R] [IsLocalRing R] [Field K]

/-- For an actual original two-dimensional representation and a genuinely nonidentity residual element, the literal ordinary matrix relations are equivalent to its entire original invariant submodule being free of rank one and an actual direct summand. -/
theorem matrixOrdinary_relations_iff_invariants_split (r : R →+* K) [IsLocalHom r]
    (ρ : G →* GeneralLinearGroup (Fin 2) R)
    (g₀ : G) (hρ : GeneralLinearGroup.map r (ρ g₀) ≠ 1) :
    (∀ g, ((ρ g).val - 1) *
      ((ρ g₀).val - (GeneralLinearGroup.det (ρ g₀) : R) •
        (1 : Matrix (Fin 2) (Fin 2) R)) = 0) ↔
      (Nonempty ((matrixStandardRepresentation ρ).invariants ≃ₗ[R] R) ∧
        ∃ N : Submodule R (Fin 2 → R), IsCompl (matrixStandardRepresentation ρ).invariants N) := by
  constructor
  · exact matrixOrdinary_invariants_rankOne_directSummand r ρ g₀ hρ
  · rintro ⟨⟨e⟩, N, hN⟩
    obtain ⟨v, hv, hvunit⟩ := submodule_rankOne_exists_primitive_vector
      (matrixStandardRepresentation ρ).invariants N hN e
    have hfix : ∀ g, (ρ g).val *ᵥ v = v := hv
    obtain ⟨U, hU⟩ := matrixTwo_invariant_line_of_primitive_vector r ρ g₀ hρ v hvunit hfix
    intro g
    exact matrixTwo_ordinary_relations_of_invariant_line ρ U hU g₀ g

end
end Dubon2026
