import Dubon2026.PolarizedCocycleLift
import Dubon2026.FirstOrderMatrixDeterminant

/-! The actual polarized tangent cocycle is the right logarithmic first
order part of its original matrix coordinate. The existing factorization
into a strict point and a constant matrix avoids a new dual-number derivative calculation.
This is the evaluation identity needed for linearity of DUB-17's original
polarized coefficient-ring cotangent comparison. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original polarized cocycle is exactly the infinitesimal of the original GL_n matrix coordinate. -/
theorem polarizedFirstOrderCocycle_matrix (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedFirstOrderCocycle ρ τ g = dualMatrixInfinitesimal (τ.val g).left.1 := by
  have he := congrArg (fun x : PolarizedGaloisGroup ι (DualNumber R) => x.left.1)
    (polarizedFirstOrderCoordinate_reconstruct ρ τ g)
  change dualMatrixStrictUnit (polarizedFirstOrderCocycle ρ τ g) *
    constantDualMatrixUnit (ρ g).left.1 = (τ.val g).left.1 at he
  have hr := congrArg (fun x : PolarizedGaloisGroup ι R => x.left.1)
    (DFunLike.congr_fun τ.property.1 g)
  change dualMatrixReduction (τ.val g).left.1 = (ρ g).left.1 at hr
  have hf := dualMatrixUnit_factor (τ.val g).left.1
  rw [hr] at hf
  apply dualMatrixStrictUnit_injective
  apply mul_right_cancel (b := constantDualMatrixUnit (ρ g).left.1)
  exact he.trans hf

/-- The original polarized cocycle retains the literal epsilon matrix multiplied by the inverse residual matrix. -/
theorem polarizedFirstOrderCocycle_matrix_formula (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) (g : G) :
    polarizedFirstOrderCocycle ρ τ g =
      dualMatrixSnd (τ.val g).left.1.val * (ρ g).left.1.inv := by
  have hr := congrArg (fun x : PolarizedGaloisGroup ι R => x.left.1)
    (DFunLike.congr_fun τ.property.1 g)
  change dualMatrixReduction (τ.val g).left.1 = (ρ g).left.1 at hr
  rw [polarizedFirstOrderCocycle_matrix, dualMatrixInfinitesimal, hr]
  rfl

end
end Dubon2026
