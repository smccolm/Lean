import Dubon2026.MatrixTwoInvariantAxis
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Original residual nontriviality detects the whole invariant first axis -/

namespace Dubon2026
open Matrix

variable {G R K : Type*} [CommRing R] [Field K]

/-- A genuine residual nonidentity upper triangular matrix fixing the first axis has a unit in the original second-column difference. -/
theorem matrixTwo_unit_second_difference (r : R →+* K) [IsLocalHom r]
    (A : GeneralLinearGroup (Fin 2) R) (hfirst : A 0 0 = 1 ∧ A 1 0 = 0)
    (hA : GeneralLinearGroup.map r A ≠ 1) :
    IsUnit (A 0 1) ∨ IsUnit (A 1 1 - 1) := by
  by_contra h
  have h01 : r (A 0 1) = 0 := by
    by_contra hz
    exact h (Or.inl (isUnit_of_map_unit r _ (isUnit_iff_ne_zero.mpr hz)))
  have h11 : r (A 1 1 - 1) = 0 := by
    by_contra hz
    exact h (Or.inr (isUnit_of_map_unit r _ (isUnit_iff_ne_zero.mpr hz)))
  have h11' : r (A 1 1) = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using h11
  apply hA
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, hfirst.1, hfirst.2, h01, h11']

/-- An original matrix family fixing the first axis and nontrivial in the actual residue has exactly that invariant axis over the original local coefficients. -/
theorem matrixTwo_fixed_iff_second_zero_of_residue (r : R →+* K) [IsLocalHom r]
    (A : G → GeneralLinearGroup (Fin 2) R)
    (hfirst : ∀ g, A g 0 0 = 1 ∧ A g 1 0 = 0)
    (g₀ : G) (hA : GeneralLinearGroup.map r (A g₀) ≠ 1) (v : Fin 2 → R) :
    (∀ g, (A g).val *ᵥ v = v) ↔ v 1 = 0 := by
  exact matrixTwo_fixed_iff_second_zero (fun g => (A g).val) hfirst g₀
    (matrixTwo_unit_second_difference r (A g₀) (hfirst g₀) hA) v

end Dubon2026
