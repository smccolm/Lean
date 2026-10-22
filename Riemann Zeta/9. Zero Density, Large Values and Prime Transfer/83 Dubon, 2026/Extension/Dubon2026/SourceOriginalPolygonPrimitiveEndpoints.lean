import Dubon2026.SourceOriginalPolygonPrimitiveData
import Dubon2026.SourceOriginalSignedPrimitiveArcIntegral

/-! DUB-17/18 -> original Abel-Jacobi -> polygon-word jump formula.
The actual arc endpoint vectors differ by the signed edge integral, and an
actual jump is the difference of the two opposite endpoint vectors. These
identities supply the analytic terms of the polygon telescoping argument.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential CellDissection
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ
variable {𝒟 : CellDissection N} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
  {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

theorem endpoint_difference_eq_signed_integral (D : CellDissection N)
    (θs : κ → Ω[F⁄ℂ]) (U : D.ιC → Set ℂ) (P : κ → D.ιC → ℂ → ℂ)
    (hP : PrimData D θs U P) (q : D.ιE × Bool) :
    Bvec D P q - Avec D P q = (if q.2 then (1 : ℂ) else -1) • Ivec D θs q.1 :=
  funext fun i => D.signed_primitive_arc_integral (θs i) U (P i) hP.hKV (hP.hΨ i) (hP.hη i) q

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
    exact (Cell.bdry_coordinates _ _).2
  simp only [Pi.sub_apply, Bvec, Avec]
  rw [← h, hζ]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
