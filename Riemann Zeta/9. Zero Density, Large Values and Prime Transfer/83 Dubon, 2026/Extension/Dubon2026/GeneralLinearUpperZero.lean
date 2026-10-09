import Dubon2026.FiniteAdelicLevelResidue

/-! # The actual triangular subgroup in a two-dimensional general-linear group -/

namespace Dubon2026

noncomputable section
open Matrix

variable {K : Type*} [Field K]

/-- A genuine invertible two-by-two matrix with zero upper-right entry has the same zero in its actual inverse. -/
theorem gl2_upper_zero_inv (g : GeneralLinearGroup (Fin 2) K) (hg : g.val 0 1 = 0) :
    (g⁻¹).val 0 1 = 0 := by
  have hd := g.det_ne_zero
  rw [Matrix.det_fin_two, hg, zero_mul, sub_zero] at hd
  have h00 := (mul_ne_zero_iff.mp hd).1
  have hi := congrArg (fun m : Matrix (Fin 2) (Fin 2) K => m 0 1) g.val_inv
  have he : g.val 0 0 * (g⁻¹).val 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hg] using hi
  exact (mul_eq_zero.mp he).resolve_left h00

/-- The genuine lower-triangular subgroup, expressed by the literal vanishing upper-right matrix entry. -/
def gl2UpperZeroSubgroup (F : Type*) [Field F] : Subgroup (GeneralLinearGroup (Fin 2) F) where
  carrier g := g.val 0 1 = 0
  one_mem' := by
    change (1 : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
    simp
  mul_mem' {a b} ha hb := by
    change a.val 0 1 = 0 at ha
    change b.val 0 1 = 0 at hb
    change (a.val * b.val) 0 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' {g} hg := gl2_upper_zero_inv g hg

end
end Dubon2026
