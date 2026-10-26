import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.LinearAlgebra.BilinearMap

/-! DUB-17/18 -> primitive determinant -> Galois invariance of the actual
projector image. Native finite-sum and polynomial commutation preserve
the proved commutation with each original good-prime Hecke operator. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

theorem commute_shifted_squares {I : Type*} (G : Module.End E V)
    (s : Finset I) (H : I → Module.End E V) (a : I → E)
    (h : ∀ i ∈ s, Commute G (H i)) :
    Commute G (∑ i ∈ s, (H i - a i • 1) ^ 2) :=
  Commute.sum_right s _ G fun i hi =>
    ((h i hi).sub_right ((Commute.one_right G).smul_right (a i))).pow_right 2

theorem commute_aeval_of_commute (G H : Module.End E V) (h : Commute G H) (P : E[X]) :
    Commute G (aeval H P) := by
  rw [Polynomial.aeval_eq_smeval]
  exact (Polynomial.smeval_commute_left E P h.symm).symm

end
end Dubon2026
