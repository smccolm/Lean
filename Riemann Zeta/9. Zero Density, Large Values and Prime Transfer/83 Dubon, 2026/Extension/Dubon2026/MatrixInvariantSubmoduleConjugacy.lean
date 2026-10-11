import Dubon2026.MatrixAdjointSchur
import Dubon2026.MatrixConjugateFixedVectors
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The original invariant submodule and its rank-one splitting under genuine basis change -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original invertible basis change maps the entire original invariant submodule onto the invariant submodule of the conjugate representation. -/
theorem matrix_invariants_map_of_conjugacy
    (ρ τ : G →* GeneralLinearGroup ι R) (U : GeneralLinearGroup ι R)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) :
    (matrixStandardRepresentation ρ).invariants.map
      (GeneralLinearGroup.toLin U).toLinearEquiv.toLinearMap =
        (matrixStandardRepresentation τ).invariants := by
  let e := (GeneralLinearGroup.toLin U).toLinearEquiv
  have hmove (v : ι → R) : e v ∈ (matrixStandardRepresentation τ).invariants ↔
      v ∈ (matrixStandardRepresentation ρ).invariants := by
    change (∀ g, (τ g).val *ᵥ (U.val *ᵥ v) = U.val *ᵥ v) ↔
      ∀ g, (ρ g).val *ᵥ v = v
    apply forall_congr'
    intro g
    simpa only [hc g, inv_inv] using matrix_conjugate_fixed_iff (ρ g) U⁻¹ v
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hmove v).mpr hv
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    apply (hmove (e.symm w)).mp
    simpa only [e.apply_symm_apply] using hw

private theorem invariant_split_of_conjugacy
    (ρ τ : G →* GeneralLinearGroup ι R) (U : GeneralLinearGroup ι R)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹)
    (hρ : Nonempty ((matrixStandardRepresentation ρ).invariants ≃ₗ[R] R) ∧
      ∃ N : Submodule R (ι → R), IsCompl (matrixStandardRepresentation ρ).invariants N) :
    Nonempty ((matrixStandardRepresentation τ).invariants ≃ₗ[R] R) ∧
      ∃ N : Submodule R (ι → R), IsCompl (matrixStandardRepresentation τ).invariants N := by
  let e := (GeneralLinearGroup.toLin U).toLinearEquiv
  have he := matrix_invariants_map_of_conjugacy ρ τ U hc
  obtain ⟨⟨f⟩, N, hN⟩ := hρ
  refine ⟨⟨(e.ofSubmodules _ _ he).symm.trans f⟩, N.map e.toLinearMap, ?_⟩
  have h := (Submodule.orderIsoMapComap e).isCompl hN
  change IsCompl ((matrixStandardRepresentation ρ).invariants.map e.toLinearMap)
    (N.map e.toLinearMap) at h
  rw [he] at h
  exact h

/-- A genuine basis change preserves the actual invariant submodule being free of rank one and a direct summand of the original ambient module. -/
theorem matrix_invariants_rankOne_split_conjugacy_iff
    (ρ τ : G →* GeneralLinearGroup ι R) (U : GeneralLinearGroup ι R)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) :
    (Nonempty ((matrixStandardRepresentation ρ).invariants ≃ₗ[R] R) ∧
      ∃ N : Submodule R (ι → R), IsCompl (matrixStandardRepresentation ρ).invariants N) ↔
    (Nonempty ((matrixStandardRepresentation τ).invariants ≃ₗ[R] R) ∧
      ∃ N : Submodule R (ι → R), IsCompl (matrixStandardRepresentation τ).invariants N) := by
  constructor
  · exact invariant_split_of_conjugacy ρ τ U hc
  · apply invariant_split_of_conjugacy τ ρ U⁻¹
    intro g
    rw [hc g]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end
end Dubon2026
