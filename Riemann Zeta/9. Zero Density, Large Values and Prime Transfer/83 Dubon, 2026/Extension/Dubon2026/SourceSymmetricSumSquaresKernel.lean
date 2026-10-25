import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! DUB-17/18 -> the actual primitive-component projector. A finite sum of
squares of symmetric operators has exactly their common kernel. This is
the finite Hecke-equation reduction needed before polynomial projection. -/
namespace Dubon2026
noncomputable section
open scoped BigOperators
variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem symmetric_sum_squares_eq_zero_iff (s : Finset I) (A : I → Module.End ℂ V)
    (hA : ∀ i ∈ s, (A i).IsSymmetric) (x : V) :
    (∑ i ∈ s, A i ^ 2) x = 0 ↔ ∀ i ∈ s, A i x = 0 := by
  constructor
  · intro hx
    have hs : ∑ i ∈ s, ‖A i x‖ ^ 2 = 0 := by
      calc
        ∑ i ∈ s, ‖A i x‖ ^ 2 = ∑ i ∈ s, (inner ℂ x (A i (A i x))).re := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (inner_self_eq_norm_sq (𝕜 := ℂ) (A i x)).symm.trans
            (congrArg Complex.re (hA i hi x (A i x)))
        _ = (inner ℂ x ((∑ i ∈ s, A i ^ 2) x)).re := by
          simp only [LinearMap.sum_apply, pow_two, Module.End.mul_apply, inner_sum, Complex.re_sum]
        _ = 0 := by rw [hx]; simp
    intro i hi
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A j x‖)).mp hs i hi))
  · intro hx
    rw [LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i hi => by
      rw [pow_two, Module.End.mul_apply, hx i hi, map_zero]

end
end Dubon2026
