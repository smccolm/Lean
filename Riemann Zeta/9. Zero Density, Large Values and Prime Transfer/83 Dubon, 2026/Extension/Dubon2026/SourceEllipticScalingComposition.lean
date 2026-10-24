import Dubon2026.SourceEllipticShortStabilizer

/-! The exceptional subgroup-orbit comparison needs equality of the
actual stabilizer maps and their square. These identities use the
existing coordinate action and preserve the literal native point maps. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem stabilizerPointEquiv_congr (W : WeierstrassCurve K)
    {C D : VariableChange K} (he : C = D) (hC : C • W = W) (hD : D • W = W) :
    stabilizerPointEquiv W C hC = stabilizerPointEquiv W D hD := by
  subst D
  rfl

theorem pure_scaling_point_square (W : WeierstrassCurve K) (u : Kˣ)
    (hu : (⟨u, 0, 0, 0⟩ : VariableChange K) • W = W)
    (hu2 : (⟨u ^ 2, 0, 0, 0⟩ : VariableChange K) • W = W)
    (P : W.toAffine.Point) :
    stabilizerPointEquiv W ⟨u ^ 2, 0, 0, 0⟩ hu2 P =
      stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu
        (stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu P) := by
  apply xy_injective
  rw [xy_stabilizerPointEquiv, xy_stabilizerPointEquiv, xy_stabilizerPointEquiv]
  rcases xy P with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv, vcYInv, sub_zero, zero_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow,
      Option.some.injEq, Prod.mk.injEq]
    constructor <;> ring

theorem pure_scaling_subgroup_square (W : WeierstrassCurve K) (u : Kˣ)
    (hu : (⟨u, 0, 0, 0⟩ : VariableChange K) • W = W)
    (hu2 : (⟨u ^ 2, 0, 0, 0⟩ : VariableChange K) • W = W)
    (H : AddSubgroup W.toAffine.Point) :
    H.map (stabilizerPointEquiv W ⟨u ^ 2, 0, 0, 0⟩ hu2).toAddMonoidHom =
      (H.map (stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu).toAddMonoidHom).map
        (stabilizerPointEquiv W ⟨u, 0, 0, 0⟩ hu).toAddMonoidHom := by
  rw [AddSubgroup.map_map]
  apply congrArg H.map
  exact AddMonoidHom.ext (pure_scaling_point_square W u hu hu2)

end
end Dubon2026.SourceEllipticExceptional
