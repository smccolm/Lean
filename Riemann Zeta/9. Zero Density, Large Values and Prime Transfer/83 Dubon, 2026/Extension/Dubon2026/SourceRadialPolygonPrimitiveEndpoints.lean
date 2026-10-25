import Dubon2026.SourceRadialPolygonPrimitiveData

/-! DUB-17/18 -> original Abel-Jacobi -> polygon-word jump formula.
The actual arc endpoint vectors differ by the signed edge integral, and an
actual jump is the difference of the two opposite endpoint vectors. These
identities supply the analytic terms of the polygon telescoping argument.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
open Set RadialCellDissection
variable {X : Type*} [TopologicalSpace X] {κ : Type*}
variable {𝒟 : RadialCellDissection X}
  {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

theorem jump_eq_Bvec_sub_Avec {J : 𝒟.ιE → κ → ℂ} (hJ : IsJump 𝒟 Ψ J) (j : 𝒟.ιE) :
    J j = Bvec 𝒟 Ψ (j, true) - Avec 𝒟 Ψ (j, false) := by
  funext i
  set Cp := 𝒟.cell (arcOf 𝒟 (j, true)).1 with hCp
  set kp := (arcOf 𝒟 (j, true)).2 with hkp
  have hb : Cp.R.φs kp.succ ∈ Icc (Cp.R.φs kp.castSucc) (Cp.R.φs kp.succ) :=
    right_mem_Icc.2 (Cp.R.hmono Fin.castSucc_lt_succ).le
  have h := hJ i j _ hb

  have hx : Cp.bdry (Cp.R.φs kp.succ) = 𝒟.vert (𝒟.ends j).2 := by
    have := (𝒟.arc_ends (arcOf 𝒟 (j, true)).1 (arcOf 𝒟 (j, true)).2).2
    rw [side_arcOf] at this; simpa using this
  have hx' : (𝒟.cell (arcOf 𝒟 (j, false)).1).bdry
      ((𝒟.cell (arcOf 𝒟 (j, false)).1).R.φs (arcOf 𝒟 (j, false)).2.castSucc) =
        𝒟.vert (𝒟.ends j).2 := by
    have := (𝒟.arc_ends (arcOf 𝒟 (j, false)).1 (arcOf 𝒟 (j, false)).2).1
    rw [side_arcOf] at this; simpa using this
  have hζ : (𝒟.cell (arcOf 𝒟 (j, false)).1).ζ (Cp.bdry (Cp.R.φs kp.succ)) =
      (𝒟.cell (arcOf 𝒟 (j, false)).1).R.loop
        ((𝒟.cell (arcOf 𝒟 (j, false)).1).R.φs (arcOf 𝒟 (j, false)).2.castSucc) := by
    rw [hx, ← hx']
    exact (RadialCell.bdry_coordinates _ _).2
  simp only [Pi.sub_apply, Bvec, Avec]
  rw [← h, hζ]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
