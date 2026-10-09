import Dubon2026.GL2DiagonalSwap

/-! # Literal coordinate permutations placing an original matrix entry in the first position -/

namespace Dubon2026

noncomputable section
open Matrix

/-- The genuine identity or coordinate swap sending the original selected coordinate to zero. -/
def gl2IndexSwap {R : Type*} [CommRing R] (i : Fin 2) : GeneralLinearGroup (Fin 2) R :=
  if i = 0 then 1 else gl2CoordinateSwap

/-- Each original index swap is its own genuine inverse. -/
theorem gl2IndexSwap_inv {R : Type*} [CommRing R] (i : Fin 2) :
    (gl2IndexSwap (R := R) i)⁻¹ = gl2IndexSwap i := by
  fin_cases i <;> simp [gl2IndexSwap, gl2CoordinateSwap_inv]

/-- Literal left and right swaps move precisely the selected original entry to the first pivot. -/
theorem gl2IndexSwap_pivot {R : Type*} [CommRing R]
    (g : GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    (gl2IndexSwap i * g * gl2IndexSwap j).val 0 0 = g.val i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gl2IndexSwap, gl2CoordinateSwap, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Every original permuted matrix entry is one of the actual original entries. -/
theorem gl2IndexSwap_entry {R : Type*} [CommRing R]
    (g : GeneralLinearGroup (Fin 2) R) (i j r s : Fin 2) :
    ∃ a b : Fin 2, (gl2IndexSwap i * g * gl2IndexSwap j).val r s = g.val a b := by
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [gl2IndexSwap, gl2CoordinateSwap, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

end
end Dubon2026
