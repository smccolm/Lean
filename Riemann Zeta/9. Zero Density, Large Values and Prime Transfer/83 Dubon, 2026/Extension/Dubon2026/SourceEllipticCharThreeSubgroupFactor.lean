import Dubon2026.SourceEllipticCharThreeAffineAction
import Dubon2026.SourceEllipticCharThreeStabilizerBound

/-! Factor the actual affine stabilizer action on subgroups into its
scaling and one of three translation actions. These are the precise
subgroup maps used by the DUB-17/18 six-action census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 3]

omit [CharP K 3] in
theorem char_three_affine_subgroup_factor (u : Kˣ) (r : K)
    (hu : (⟨u, 0, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hr : (⟨1, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (hur : (⟨u, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (H : AddSubgroup (EA (-1 : K)).toAffine.Point) :
    H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨u, r, 0, 0⟩ hur).toAddMonoidHom =
      (H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨1, r, 0, 0⟩ hr).toAddMonoidHom).map
        (stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩ hu).toAddMonoidHom := by
  rw [AddSubgroup.map_map]
  congr 1
  exact AddMonoidHom.ext (char_three_affine_point_factor u r hu hr hur)

theorem char_three_translation_subgroup_cases (r : K) (hr3 : r ^ 3 = r)
    (hr : (⟨1, r, 0, 0⟩ : VariableChange K) • EA (-1 : K) = EA (-1 : K))
    (H : AddSubgroup (EA (-1 : K)).toAffine.Point) :
    H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨1, r, 0, 0⟩ hr).toAddMonoidHom = H ∨
      H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨1, r, 0, 0⟩ hr).toAddMonoidHom =
        H.map charThreeTranslation.toAddMonoidHom ∨
      H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨1, r, 0, 0⟩ hr).toAddMonoidHom =
        (H.map charThreeTranslation.toAddMonoidHom).map charThreeTranslation.toAddMonoidHom := by
  rcases (cube_eq_self_iff_three_values r).mp hr3 with rfl | rfl | rfl
  · left
    have hid : (stabilizerPointEquiv (EA (-1 : K)) ⟨1, 0, 0, 0⟩ hr).toAddMonoidHom =
        AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point _ hr)
    rw [hid, AddSubgroup.map_id]
  · exact Or.inr (Or.inl rfl)
  · right; right
    rw [AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext (char_three_translation_neg_one_point hr)

end
end Dubon2026.SourceEllipticExceptional
