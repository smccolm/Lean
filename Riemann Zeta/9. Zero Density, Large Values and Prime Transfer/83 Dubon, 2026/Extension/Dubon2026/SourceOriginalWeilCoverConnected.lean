import Dubon2026.SourceOriginalWeilCoverClopenObstruction

/-! DUB-17/18 -> auxiliary Abel comparison -> connected actual cover.
The native finite coordinate proves nonemptiness. The proved compact
maximum-modulus obstruction rules out every proper nonempty clopen set.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Set
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem place_connectedSpace :
    @ConnectedSpace (Place ℂ EE) (placeTopology N n f D hf hfD) := by
  letI := placeTopology N n f D hf hfD
  letI := nonempty_cover_place N n f
  have hpre : PreconnectedSpace (Place ℂ EE) := by
    rw [preconnectedSpace_iff_clopen]
    intro U hU
    by_contra h
    obtain ⟨he, hu⟩ := not_or.mp h
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr he
    exact false_of_proper_clopen N n f D hf hfD U hU v hv (Set.nonempty_compl.mpr hu)
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
