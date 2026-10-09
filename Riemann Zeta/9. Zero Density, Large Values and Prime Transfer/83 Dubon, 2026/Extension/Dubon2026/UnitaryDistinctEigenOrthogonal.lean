import Dubon2026.UnitaryEigenCoordinate

/-! # Orthogonality of genuinely distinct unitary eigenvalues -/

namespace Dubon2026

/-- Distinct actual unitary eigenvalues force orthogonality of their original vectors. -/
theorem unitary_distinct_eigen_inner_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : Module.End ℂ V) (hT : ∀ v w, inner ℂ (T v) (T w) = inner ℂ v w)
    (v w : V) (μ ν : ℂ) (hμ : ‖μ‖ = 1) (hne : μ ≠ ν)
    (hv : T v = μ • v) (hw : T w = ν • w) : inner ℂ v w = 0 := by
  have he := unitary_eigen_coordinate T hT v μ hμ hv w
  rw [hw, inner_smul_right] at he
  have hz : (ν - μ) * inner ℂ v w = 0 := by rw [sub_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne.symm)

end Dubon2026
