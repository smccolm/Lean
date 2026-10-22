import Dubon2026.SourceCellPowerArcPresentation

/-! DUB-17/18 -> original Abel-Jacobi -> C1 reversal of pole-cell arcs.
The already constructed reciprocal geometry gives the exact reversed
endpoints and loop evaluation of each reciprocal side.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
noncomputable section
open Set
open scoped Real

theorem ReciprocalGeometry.arc_presentation {W U : RadialRegion}
    (hrec : ReciprocalGeometry W U) (a : Fin U.N) :
    ∃ k : Fin W.N,
      U.φs a.castSucc = 2 * π - W.φs k.succ ∧
      U.φs a.succ = 2 * π - W.φs k.castSucc ∧
      (∀ t : ℝ, (U.loop t)⁻¹ = W.loop (2 * π - t)) ∧
      (fun u : ℂ => u⁻¹) '' U.arcSet a = W.arcSet k := by
  obtain ⟨_, _, _, _, _, hloop, σ, harc, himg⟩ := hrec
  obtain ⟨k, rfl⟩ := σ.surjective a
  have hIcc : Icc (U.φs (σ k).castSucc) (U.φs (σ k).succ) =
      (fun t : ℝ => (-1) * t + 2 * π) '' Icc (W.φs k.castSucc) (W.φs k.succ) := by
    rw [← RadialRegion.arcIcc, harc k]
    congr 1
    funext t
    ring
  obtain ⟨hs, ht⟩ := ArcAffine.endpoints_of_image_anti (by norm_num)
    (W.hmono Fin.castSucc_lt_succ).le hIcc
  refine ⟨k, ?_, ?_, ?_, himg k⟩
  · linarith
  · linarith
  · intro t
    rw [hloop, inv_inv]

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
