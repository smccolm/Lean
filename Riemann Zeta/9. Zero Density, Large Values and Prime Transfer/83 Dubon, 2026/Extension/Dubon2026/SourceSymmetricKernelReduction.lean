import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! DUB-17/18 -> the actual primitive projector. Positivity of the original
Petersson inner product excludes a nontrivial zero Jordan chain for the
finite good-prime annihilator. -/
namespace Dubon2026
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem symmetric_apply_eq_zero_of_square (H : Module.End ℂ V)
    (hH : H.IsSymmetric) (x : V) (hx : H (H x) = 0) : H x = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [hH x (H x), hx, inner_zero_right]

end Dubon2026
