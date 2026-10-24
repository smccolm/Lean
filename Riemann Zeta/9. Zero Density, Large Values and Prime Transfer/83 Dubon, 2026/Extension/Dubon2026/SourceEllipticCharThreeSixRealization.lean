import Dubon2026.SourceEllipticCharThreeSixSubgroupMaps

/-! Conversely, all six subgroup actions in the characteristic-three
census are realized by actual stabilizing coordinate changes. This
prevents replacing the literal stabilizer relation by only an inclusion. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 3]

theorem char_three_six_subgroup_maps_realized (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (H T : AddSubgroup (EA (-1 : K)).toAffine.Point)
    (hT : let α := (stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩
        (quartic_change_fixes u hu (-1))).toAddMonoidHom
      let β := (charThreeTranslation (K := K)).toAddMonoidHom
      T = H ∨ T = H.map α ∨ T = H.map β ∨ T = (H.map β).map β ∨
        T = (H.map β).map α ∨ T = ((H.map β).map β).map α) :
    ∃ (γ : VariableChange K) (hγ : γ • EA (-1 : K) = EA (-1 : K)),
      H.map (stabilizerPointEquiv (EA (-1 : K)) γ hγ).toAddMonoidHom = T := by
  dsimp only at hT
  have hu4 : (u : K) ^ 4 = 1 := by
    calc (u : K) ^ 4 = ((u : K) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h0 := char_three_affine_fixes (1 : Kˣ) (0 : K) (by simp) (by simp)
  have hm := char_three_affine_fixes (1 : Kˣ) (-1 : K) (by simp) (by ring)
  have hum := char_three_affine_fixes u (-1 : K) hu4 (by ring)
  have hu1 := char_three_affine_fixes u (1 : K) hu4 (by simp)
  have hmsq : H.map (stabilizerPointEquiv (EA (-1 : K)) ⟨1, -1, 0, 0⟩ hm).toAddMonoidHom =
      (H.map charThreeTranslation.toAddMonoidHom).map charThreeTranslation.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext (char_three_translation_neg_one_point hm)
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨1, 0, 0, 0⟩, h0, ?_⟩
    have hid : (stabilizerPointEquiv (EA (-1 : K)) ⟨1, 0, 0, 0⟩ h0).toAddMonoidHom =
        AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point _ h0)
    rw [hid, AddSubgroup.map_id]
  · exact ⟨⟨u, 0, 0, 0⟩, quartic_change_fixes u hu (-1), rfl⟩
  · exact ⟨⟨1, 1, 0, 0⟩, char_three_translation_fixes, rfl⟩
  · exact ⟨⟨1, -1, 0, 0⟩, hm, hmsq⟩
  · refine ⟨⟨u, 1, 0, 0⟩, hu1, ?_⟩
    rw [char_three_affine_subgroup_factor u 1 (quartic_change_fixes u hu (-1))
      char_three_translation_fixes hu1 H]
    rfl
  · refine ⟨⟨u, -1, 0, 0⟩, hum, ?_⟩
    rw [char_three_affine_subgroup_factor u (-1) (quartic_change_fixes u hu (-1)) hm hum H,
      hmsq]

end
end Dubon2026.SourceEllipticExceptional
