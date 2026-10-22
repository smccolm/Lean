import Dubon2026.SourceOriginalClopenObstruction

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The actual original complex place manifold is connected. The original
place set is nonempty, and the proved compact maximum-modulus obstruction
rules out every proper nonempty clopen subset. No connectedness premise
or replacement curve is supplied.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set
variable (N : ℕ) [NeZero N]

theorem place_connectedSpace :
    @ConnectedSpace (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) := by
  letI := placeTopology N
  haveI : Nonempty (Place ℂ (modularFunctionFieldOver N ℂ)) :=
    ⟨originalAnalyticPlace N UpperHalfPlane.I⟩
  have hpre : PreconnectedSpace (Place ℂ (modularFunctionFieldOver N ℂ)) := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    by_contra h
    obtain ⟨he, hu⟩ := not_or.mp h
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr he
    exact original_false_of_proper_clopen N U hU v hv (Set.nonempty_compl.mpr hu)
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

end
end Dubon2026.SourceFunctionField.OriginalChart
