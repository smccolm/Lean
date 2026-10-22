import Dubon2026.SourceOriginalCellPrimitiveArcIntegral

/-! DUB-17/18 -> raw reciprocity -> signed primitive endpoint formula.
Apply the proved arc fundamental theorem and negative-edge reversal to a
single differential and primitive family on the actual dissection cells.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem CellDissection.signed_primitive_arc_integral (D : CellDissection N)
    (θ : Ω[F⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : D.ιC → ℂ → ℂ)
    (hKV : ∀ C, (D.cell C).R.K ⊆ V C)
    (hΨ : ∀ C, ∀ w ∈ V C, HasDerivAt (Ψ C) (coeffIn (D.cell C).ζ θ w) w)
    (hθ : ∀ P : Place ℂ F, 0 ≤ P.ordDifferential θ) (q : D.ιE × Bool) :
    Ψ (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ)) -
      Ψ (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc)) =
      (if q.2 then (1 : ℂ) else -1) * D.edgeInt θ q.1 := by
  obtain ⟨e, σ⟩ := q
  have hh := (D.cell (D.arcOf (e, σ)).1).primitive_arc_integral
    (D.arcOf (e, σ)).2 (hKV _) (hΨ _) (fun _ _ => hθ _)
  rw [← hh]
  cases σ
  · rw [D.negative_arc_integral e (fun _ _ => hθ _)]
    simp
  · simp [CellDissection.edgeInt]

end
end Dubon2026.SourceFunctionField.CellGeometry
