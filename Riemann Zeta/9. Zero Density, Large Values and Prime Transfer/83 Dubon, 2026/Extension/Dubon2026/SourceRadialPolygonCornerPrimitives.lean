import Dubon2026.SourceRadialPolygonPrimitiveEndpoints

/-! DUB-17/18 -> original Abel-Jacobi -> polygon-word jump formula.
Zero jumps on the actual dual tree identify primitive endpoint readings along
its corner paths. Consequently consecutive letters of the constructed polygon
have the matching primitive values required for telescoping. Adapted from the
verified Apache-2.0 source anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
open Set RadialCellDissection
variable {X : Type*} [TopologicalSpace X] {κ : Type*}
variable {𝒟 : RadialCellDissection X} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

theorem gvec_eq_of_link {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {v : 𝒟.ιV} {D D' : 𝒟.ιC} {g : 𝒟.ιE} (hg : g ∈ 𝒯s)
    (hDD' : ((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
      ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D))
    (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) :
    gvec 𝒟 Ψ (𝒟.vert v) D = gvec 𝒟 Ψ (𝒟.vert v) D' := by

  set Cp := 𝒟.cell (arcOf 𝒟 (g, true)).1 with hCp
  set kp := (arcOf 𝒟 (g, true)).2 with hkp
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ Icc (Cp.R.φs kp.castSucc) (Cp.R.φs kp.succ),
      Cp.bdry s = 𝒟.vert v := by
    have he := 𝒟.arc_ends (arcOf 𝒟 (g, true)).1 (arcOf 𝒟 (g, true)).2
    rw [side_arcOf] at he
    simp only [if_true] at he
    rcases hv with rfl | rfl
    · exact ⟨_, left_mem_Icc.2 (Cp.R.hmono Fin.castSucc_lt_succ).le, he.1⟩
    · exact ⟨_, right_mem_Icc.2 (Cp.R.hmono Fin.castSucc_lt_succ).le, he.2⟩
  have hkey : gvec 𝒟 Ψ (𝒟.vert v) (arcOf 𝒟 (g, true)).1 =
      gvec 𝒟 Ψ (𝒟.vert v) (arcOf 𝒟 (g, false)).1 := by
    funext i
    have h := hJ i g s hs
    rw [hJ0 g hg] at h
    simp only [Pi.zero_apply] at h
    simp only [gvec]
    rw [← hsx, (RadialCell.bdry_coordinates Cp s).2]
    exact sub_eq_zero.1 h
  rcases hDD' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hkey
  · exact hkey.symm

theorem Bvec_eq_gvec (q : 𝒟.ιE × Bool) :
    Bvec 𝒟 Ψ q = gvec 𝒟 Ψ (𝒟.vert (RadialDissectionPolygon.eV 𝒟 q)) (arcOf 𝒟 q).1 := by
  have he := (𝒟.arc_ends (arcOf 𝒟 q).1 (arcOf 𝒟 q).2).2
  rw [side_arcOf] at he
  funext i
  simp only [Bvec, gvec, RadialDissectionPolygon.eV]
  rw [← he, (RadialCell.bdry_coordinates _ _).2]

theorem Avec_eq_gvec (q : 𝒟.ιE × Bool) :
    Avec 𝒟 Ψ q = gvec 𝒟 Ψ (𝒟.vert (RadialDissectionPolygon.sV 𝒟 q)) (arcOf 𝒟 q).1 := by
  have he := (𝒟.arc_ends (arcOf 𝒟 q).1 (arcOf 𝒟 q).2).1
  rw [side_arcOf] at he
  funext i
  simp only [Avec, gvec, RadialDissectionPolygon.sV]
  rw [← he, (RadialCell.bdry_coordinates _ _).2]

theorem corner {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {q q' : 𝒟.ιE × Bool} (hv : RadialDissectionPolygon.eV 𝒟 q = RadialDissectionPolygon.sV 𝒟 q')
    (hcs : ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 q).1 ∧
      cs.getLast? = some (arcOf 𝒟 q').1 ∧
      cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
        (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
          ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
        (RadialDissectionPolygon.eV 𝒟 q = (𝒟.ends g).1 ∨ RadialDissectionPolygon.eV 𝒟 q = (𝒟.ends g).2))) :
    Bvec 𝒟 Ψ q = Avec 𝒟 Ψ q' := by
  obtain ⟨cs, hhd, hlast, hch⟩ := hcs
  rw [Bvec_eq_gvec, Avec_eq_gvec, ← hv]
  set x := 𝒟.vert (RadialDissectionPolygon.eV 𝒟 q) with hx
  have hall : ∀ D ∈ cs, gvec 𝒟 Ψ x D = gvec 𝒟 Ψ x (arcOf 𝒟 q).1 := by
    refine hch.induction (fun D => gvec 𝒟 Ψ x D = gvec 𝒟 Ψ x (arcOf 𝒟 q).1) cs ?_ ?_
    · rintro D D' ⟨g, hg, hDD', hvg⟩ hD
      rw [← hD]
      exact (gvec_eq_of_link hJ hJ0 hg hDD' hvg).symm
    · intro hne
      obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.1 hhd
      rfl
  exact (hall _ (List.mem_of_getLast? hlast)).symm

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
