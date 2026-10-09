import Dubon2026.FiniteAdelicProjectiveCharacters

/-! # The genuine inverse diagonal differs from its coordinate conjugate by its actual scalar -/

namespace Dubon2026

noncomputable section
open Matrix

/-- An original diagonal with entries one and a unit has the exact scalar-conjugate inverse. -/
theorem gl2SecondDiagonal_inverse_swap {R : Type*} [CommRing R] (u : Rˣ)
    (g : GeneralLinearGroup (Fin 2) R) (hg : g.val = !![1, 0; 0, (u : R)]) :
    g⁻¹ = GeneralLinearGroup.scalar (Fin 2) u⁻¹ *
      gl2CoordinateSwap * g * gl2CoordinateSwap⁻¹ := by
  apply (mul_left_cancel_iff (a := g)).mp
  rw [mul_inv_cancel]
  apply Units.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hg, gl2CoordinateSwap, GeneralLinearGroup.scalar, Matrix.scalar,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The genuine coordinate swap has order two over the original ring. -/
theorem gl2CoordinateSwap_inv {R : Type*} [CommRing R] :
    (gl2CoordinateSwap : GeneralLinearGroup (Fin 2) R)⁻¹ = gl2CoordinateSwap := by
  apply Units.ext
  rfl

end
end Dubon2026
