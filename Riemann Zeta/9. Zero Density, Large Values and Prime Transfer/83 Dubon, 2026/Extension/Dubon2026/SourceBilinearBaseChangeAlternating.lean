import Dubon2026.SourceBilinearBaseChangeLaws
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-! DUB-17/18 -> primitive determinant -> alternation of the coefficient
extension of the actual Weil pairing. Tensor induction retains its target. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

theorem sourceBilinear_baseChange_alternating
    {R K V W : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (B : V →ₗ[R] V →ₗ[R] W) (hB : B.IsAlt) :
    (LinearMap.BilinMap.baseChange K B).IsAlt := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.BilinMap.baseChange_tmul, hB x, TensorProduct.tmul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    exact add_eq_zero_iff_eq_neg.mpr
      (sourceBilinear_baseChange_skew B (fun a b => (hB.neg b a).symm) y x)

end
end Dubon2026
