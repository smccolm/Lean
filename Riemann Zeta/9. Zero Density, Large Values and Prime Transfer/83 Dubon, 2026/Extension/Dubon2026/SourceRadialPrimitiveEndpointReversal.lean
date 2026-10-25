import Dubon2026.SourceRadialCellBoundaryCoordinates

/-! DUB-17/18 -> cover period generation -> signed primitive arc values.
Constant paired-edge jumps identify the two endpoint differences with opposite
signs. This endpoint proof suffices for regular primitive arcs and avoids the
more general weighted meromorphic change-of-variables argument at this stage. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set
variable {X : Type*} [TopologicalSpace X]

theorem RadialCellDissection.primitive_endpoint_reversal (D : RadialCellDissection X)
    (Ψ : D.ιC → ℂ → ℂ) (e : D.ιE) (J : ℂ)
    (hJ : ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
      Ψ (D.arcOf (e, true)).1 ((D.cell (D.arcOf (e, true)).1).R.loop s) -
        Ψ (D.arcOf (e, false)).1 ((D.cell (D.arcOf (e, false)).1).ζ
          ((D.cell (D.arcOf (e, true)).1).bdry s)) = J) :
    let p := D.arcOf (e, true)
    let q := D.arcOf (e, false)
    Ψ q.1 ((D.cell q.1).R.loop ((D.cell q.1).R.φs q.2.succ)) -
      Ψ q.1 ((D.cell q.1).R.loop ((D.cell q.1).R.φs q.2.castSucc)) =
    -(Ψ p.1 ((D.cell p.1).R.loop ((D.cell p.1).R.φs p.2.succ)) -
      Ψ p.1 ((D.cell p.1).R.loop ((D.cell p.1).R.φs p.2.castSucc))) := by
  dsimp only
  let p := D.arcOf (e, true)
  let q := D.arcOf (e, false)
  have hp : D.side p.1 p.2 = (e, true) := D.side_arcOf _
  have hq : D.side q.1 q.2 = (e, false) := D.side_arcOf _
  obtain ⟨ψ, _, _, ha, hb, hbd⟩ := D.arc_rev p.1 p.2 q.1 q.2
    (by rw [hp, hq]) (by rw [hp]) (by rw [hq])
  have hqab := ((D.cell q.1).R.hmono (Fin.castSucc_lt_succ (i := q.2))).le
  have hpab := ((D.cell p.1).R.hmono (Fin.castSucc_lt_succ (i := p.2))).le
  have heA := hbd _ (left_mem_Icc.2 hqab)
  have heB := hbd _ (right_mem_Icc.2 hqab)
  rw [ha] at heA
  rw [hb] at heB
  have hA := hJ _ (left_mem_Icc.2 hpab)
  have hB := hJ _ (right_mem_Icc.2 hpab)
  change Ψ p.1 ((D.cell p.1).R.loop ((D.cell p.1).R.φs p.2.castSucc)) -
    Ψ q.1 ((D.cell q.1).ζ ((D.cell p.1).bdry ((D.cell p.1).R.φs p.2.castSucc))) = J at hA
  change Ψ p.1 ((D.cell p.1).R.loop ((D.cell p.1).R.φs p.2.succ)) -
    Ψ q.1 ((D.cell q.1).ζ ((D.cell p.1).bdry ((D.cell p.1).R.φs p.2.succ))) = J at hB
  rw [← heB, ((D.cell q.1).bdry_coordinates _).2] at hA
  rw [← heA, ((D.cell q.1).bdry_coordinates _).2] at hB
  linear_combination hB - hA

end Dubon2026.SourceFunctionField.CellGeometry
