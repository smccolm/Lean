import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! DUB-17/18 -> residual Frobenius association -> transport the original
field characteristic polynomial through the already constructed lattice
basis comparison. Native linear-equivalence conjugacy preserves it. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_intertwiner_charpoly (A B : Matrix n n K)
    (e : (n → K) ≃ₗ[K] (n → K))
    (he : ∀ v, A *ᵥ e v = e (B *ᵥ v)) : A.charpoly = B.charpoly := by
  have h : A.toLin' = e.conj B.toLin' := by
    apply LinearMap.ext
    intro v
    simpa using he (e.symm v)
  rw [← Matrix.charpoly_toLin' A, h, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem matrix_intertwiner_one (A : Matrix n n K)
    (e : (n → K) ≃ₗ[K] (n → K))
    (he : ∀ v, A *ᵥ e v = e v) : A = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simpa using he (e.symm v)

end
end Dubon2026
