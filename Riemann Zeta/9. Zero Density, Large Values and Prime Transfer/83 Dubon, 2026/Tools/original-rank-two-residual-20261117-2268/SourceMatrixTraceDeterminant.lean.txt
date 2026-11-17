import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! DUB-17/18 -> actual rank-two realization -> exact determinant.
For a genuine two-by-two representation, the proved dimension-two trace
identity determines the determinant over the original characteristic-zero
field. This avoids a separate Cayley-Hamilton reconstruction detour. -/
namespace Dubon2026
noncomputable section

/-- The two-dimensional trace relation determines the determinant of an
actual two-by-two matrix over the original characteristic-zero field. -/
theorem matrixTwo_det_of_trace_relation
    {K : Type*} [Field K] [CharZero K] (M : Matrix (Fin 2) (Fin 2) K) (d : K)
    (h : Matrix.trace M * Matrix.trace M = Matrix.trace (M * M) + 2 * d) :
    M.det = d := by
  have hi : 2 * M.det = Matrix.trace M * Matrix.trace M - Matrix.trace (M * M) := by
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  apply mul_left_cancel₀ (show (2 : K) ≠ 0 by norm_num)
  linear_combination hi + h

/-- A genuine original matrix representation with the original trace has
exactly the determinant supplied by the original trace identities. -/
theorem matrixTwoRepresentation_det_of_trace
    {G K : Type*} [Group G] [Field K] [CharZero K]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K) (t : G → K) (D : G →* K)
    (hOne : t 1 = 2)
    (hProd : ∀ g h, t g * t h = t (g * h) + t (g * h⁻¹) * D h)
    (hTrace : ∀ g, Matrix.trace (ρ g).val = t g) (g : G) : (ρ g).val.det = D g := by
  apply matrixTwo_det_of_trace_relation
  rw [hTrace]
  have he : (ρ g).val * (ρ g).val = (ρ (g * g)).val := by rw [map_mul]; rfl
  rw [he, hTrace]
  simpa only [mul_inv_cancel, hOne] using hProd g g

end
end Dubon2026
