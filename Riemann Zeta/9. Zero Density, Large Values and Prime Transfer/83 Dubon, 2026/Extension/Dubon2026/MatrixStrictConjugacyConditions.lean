import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Genuine determinant and original subgroup conditions survive strict conjugacy -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R K : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing K]

/-- The actual determinant of every original whole matrix is unchanged by the original strict conjugator. -/
theorem matrixStrictlyConjugate_det (r : R →+* K)
    (ρ τ : G →* GeneralLinearGroup ι R) (h : MatrixStrictlyConjugate r ρ τ) (g : G) :
    GeneralLinearGroup.det (τ g) = GeneralLinearGroup.det (ρ g) := by
  obtain ⟨U, _hU, hc⟩ := h
  rw [hc g, map_mul, map_mul, map_inv]
  rw [mul_comm (GeneralLinearGroup.det U) (GeneralLinearGroup.det (ρ g)),
    mul_assoc, mul_inv_cancel, mul_one]

/-- Strict conjugacy preserves the actual whole representation kernel, so in particular it preserves every genuine original inertia-killing condition. -/
theorem matrixStrictlyConjugate_ker (r : R →+* K)
    (ρ τ : G →* GeneralLinearGroup ι R) (h : MatrixStrictlyConjugate r ρ τ) :
    ρ.ker = τ.ker := by
  obtain ⟨U, _hU, hc⟩ := h
  apply Subgroup.ext
  intro g
  change ρ g = 1 ↔ τ g = 1
  rw [hc g]
  constructor
  · intro hg
    rw [hg]
    simp only [mul_one, mul_inv_cancel]
  · intro hg
    have he := congrArg (fun x : GeneralLinearGroup ι R => U⁻¹ * x * U) hg
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using he

end
end Dubon2026
