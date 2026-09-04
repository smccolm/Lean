import GafniTao.HeathBrownIntegratedHolder
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Real lifts of coefficient-cell displacements

The coefficient cells live on `ℝ / ℤ`, whereas the second Abel step in
Heath-Brown's proof differentiates a real polynomial.  This file constructs
a centered real representative of every circle displacement and proves that
its absolute value is exactly the circle distance.  Thus membership in the
literal coefficient cell gives the exact bounds `|β_j| ≤ H^(-j)`.
-/

open Set Metric

namespace GafniTao

noncomputable section

theorem exists_unitAddCircle_centeredLift (u : UnitAddCircle) :
    ∃ x : ℝ, (x : UnitAddCircle) = u ∧ |x| = ‖u‖ := by
  induction u using Quotient.inductionOn with
  | _ x =>
      refine ⟨x - round x, ?_, ?_⟩
      · rw [AddCircle.coe_sub]
        simp
      · exact (UnitAddCircle.norm_eq (x := x)).symm

noncomputable def unitAddCircleCenteredLift (u : UnitAddCircle) : ℝ :=
  Classical.choose (exists_unitAddCircle_centeredLift u)

theorem coe_unitAddCircleCenteredLift (u : UnitAddCircle) :
    ((unitAddCircleCenteredLift u : ℝ) : UnitAddCircle) = u :=
  (Classical.choose_spec (exists_unitAddCircle_centeredLift u)).1

theorem abs_unitAddCircleCenteredLift (u : UnitAddCircle) :
    |unitAddCircleCenteredLift u| = ‖u‖ :=
  (Classical.choose_spec (exists_unitAddCircle_centeredLift u)).2

noncomputable def heathBrownCoefficientDisplacement
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (j : Fin (k - 1)) : ℝ :=
  unitAddCircleCenteredLift (α j - c j)

theorem coe_heathBrownCoefficientDisplacement
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (j : Fin (k - 1)) :
    ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle) =
      α j - c j :=
  coe_unitAddCircleCenteredLift _

theorem coe_center_add_heathBrownCoefficientDisplacement
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (j : Fin (k - 1)) :
    c j + ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle) =
      α j := by
  rw [coe_heathBrownCoefficientDisplacement]
  abel

theorem abs_heathBrownCoefficientDisplacement
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (j : Fin (k - 1)) :
    |heathBrownCoefficientDisplacement c α j| = dist (α j) (c j) := by
  unfold heathBrownCoefficientDisplacement
  rw [abs_unitAddCircleCenteredLift]
  rw [dist_eq_norm]

theorem abs_heathBrownCoefficientDisplacement_le_radius
    {k H : ℕ} {f : ℝ → ℝ} {n : ℝ}
    {α : HeathBrownCoefficientTorus k}
    (hα : α ∈ heathBrownCoefficientCell k H f n) (j : Fin (k - 1)) :
    |heathBrownCoefficientDisplacement
        (heathBrownCoefficientCenter k f n) α j| ≤
      heathBrownCellRadius H j := by
  rw [abs_heathBrownCoefficientDisplacement]
  have hj := hα j (Set.mem_univ j)
  simpa only [mem_closedBall, dist_comm] using hj

#print axioms exists_unitAddCircle_centeredLift
#print axioms coe_unitAddCircleCenteredLift
#print axioms abs_unitAddCircleCenteredLift
#print axioms coe_heathBrownCoefficientDisplacement
#print axioms abs_heathBrownCoefficientDisplacement_le_radius

end

end GafniTao
