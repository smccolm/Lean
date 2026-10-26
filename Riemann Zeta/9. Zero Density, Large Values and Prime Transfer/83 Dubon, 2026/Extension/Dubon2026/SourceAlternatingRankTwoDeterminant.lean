import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! DUB-17/18 -> primitive Frobenius determinant. A nondegenerate
alternating pairing on the two prescribed coefficient coordinates detects
the determinant, even with the literal vector-valued Weil target. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {E Z : Type*} [Field E] [AddCommGroup Z] [Module E Z]

theorem alternating_fin_two_formula
    (B : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] Z) (hB : B.IsAlt)
    (x y : Fin 2 → E) :
    B x y = (x 0 * y 1 - x 1 * y 0) • B ![1, 0] ![0, 1] := by
  have hd (z : Fin 2 → E) : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  have hs : B ![0, 1] ![1, 0] = -B ![1, 0] ![0, 1] := (hB.neg _ _).symm
  calc
    B x y = B (x 0 • ![1, 0] + x 1 • ![0, 1])
        (y 0 • ![1, 0] + y 1 • ![0, 1]) := congrArg₂ (fun u v => B u v) (hd x) (hd y)
    _ = _ := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        hB ![1, 0], hB ![0, 1], hs, smul_zero, zero_add, add_zero,
        smul_smul, smul_neg, sub_eq_add_neg]
      simp only [add_smul, neg_smul, mul_comm, add_comm]

theorem alternating_fin_two_basis_ne_zero
    (B : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] Z) (hB : B.IsAlt)
    (hi : Function.Injective B) : B ![1, 0] ![0, 1] ≠ 0 := by
  intro hz
  have hb : B ![1, 0] = B 0 := by
    apply LinearMap.ext
    intro y
    rw [alternating_fin_two_formula B hB, hz, smul_zero]
    simp
  have he := congrFun (hi hb) 0
  simp at he

theorem alternating_fin_two_matrix_basis
    (B : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] Z) (hB : B.IsAlt)
    (A : Matrix (Fin 2) (Fin 2) E) :
    B (A *ᵥ ![1, 0]) (A *ᵥ ![0, 1]) = A.det • B ![1, 0] ![0, 1] := by
  rw [alternating_fin_two_formula B hB]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, mul_comm]

theorem determinant_eq_alternating_multiplier
    (B : (Fin 2 → E) →ₗ[E] (Fin 2 → E) →ₗ[E] Z) (hB : B.IsAlt)
    (hi : Function.Injective B) (A : Matrix (Fin 2) (Fin 2) E) (c : E)
    (hc : ∀ x y, B (A *ᵥ x) (A *ᵥ y) = c • B x y) : A.det = c := by
  apply smul_left_injective E (alternating_fin_two_basis_ne_zero B hB hi)
  exact (alternating_fin_two_matrix_basis B hB A).symm.trans (hc _ _)

end
end Dubon2026
