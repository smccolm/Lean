import Dubon2026.SourceRadialMeromorphicBoundaryJumps

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The exact reversed-arc jump already identifies both endpoint differences.
It gives the negative orientation directly, avoiding another substitution
theorem solely to obtain the additive quotient's signed-endpoint clause. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set
variable {X A : Type*} [TopologicalSpace X] [AddCommGroup A]

theorem IsJumpH.neg_endpoint_increment {D : RadialCellDissection X}
    {H : D.ιC → ℝ → A} {J : D.ιE → A} (hJ : IsJumpH D H J) (e : D.ιE) :
    H (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.succ) -
      H (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.castSucc) =
    -(H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ) -
      H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc)) := by
  obtain ⟨ψ, _, ha, hb, _, hJe⟩ := hJ e
  have hle := ((D.cell (D.arcOf (e, false)).1).R.hmono
    (Fin.castSucc_lt_succ (i := (D.arcOf (e, false)).2))).le
  have h1 := hJe _ (left_mem_Icc.2 hle)
  have h2 := hJe _ (right_mem_Icc.2 hle)
  rw [ha] at h1
  rw [hb] at h2
  calc _ =
      (H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ) -
        H (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.castSucc)) -
      (H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc) -
        H (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.succ)) -
      (H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ) -
        H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc)) := by abel
    _ = _ := by rw [h1, h2, sub_self, zero_sub]

theorem IsJumpH.signed_endpoint_increment {D : RadialCellDissection X}
    {H : D.ιC → ℝ → A} {J : D.ιE → A} (hJ : IsJumpH D H J) (I : D.ιE → A)
    (hpos : ∀ e, H (D.arcOf (e, true)).1
        ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ) -
      H (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc) = I e)
    (q : D.ιE × Bool) :
    H (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ) -
      H (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc) =
        if q.2 then I q.1 else -I q.1 := by
  rcases q with ⟨e, b⟩
  cases b
  · exact (hJ.neg_endpoint_increment e).trans (congrArg Neg.neg (hpos e))
  · exact hpos e

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
