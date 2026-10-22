import Dubon2026.SourceOriginalConstructedCellDissection
import Dubon2026.SourceOriginalNumericalGenus

/-! DUB-17/18 -> original Abel-Jacobi -> the curve Euler identity.
Reuse the already proved original canonical j-divisor degree and original
Riemann-Roch dimension comparison. They give the exact exceptional-fiber
cardinality identity needed by the cell count, without developing a second
general Riemann-Hurwitz framework.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_exceptional_fiber_card_euler :
    (SourceLevelProjective.dedekindPsi N : ℤ) -
      (originalPositiveFiber N (jOver N ℂ) 0).card -
      (originalPositiveFiber N (jOver N ℂ) 1728).card -
      (originalPositiveFiber N (jOver N ℂ)⁻¹ 0).card =
        2 * (Module.finrank ℂ (regularDifferentials ℂ F) : ℤ) - 2 := by
  have hc (g : F) (b : ℂ) : Nat.card {v : Place ℂ F // 0 < v.ord (g - algebraMap ℂ F b)} =
      (originalPositiveFiber N g b).card := by
    calc
      _ = Nat.card ↥(originalPositiveFiber N g b) := Nat.card_congr
        (Equiv.subtypeEquivRight fun v => (mem_originalPositiveFiber N g b v).symm)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hc0 := hc (jOver N ℂ) 0
  simp only [map_zero, sub_zero] at hc0
  have hc1 := hc (jOver N ℂ) 1728
  have hcp : (originalPositiveFiber N (jOver N ℂ)⁻¹ 0).card = SourceLevelProjective.cuspCount N := by
    apply card_original_j_poles_eq_cuspCount N ℂ
    intro v
    rw [mem_originalPositiveFiber, map_zero, sub_zero, v.ord_inv, neg_pos]
  have hd := original_jCanonical_degree_eq_fiber_cards N
  rw [hc0, hc1, ← hcp] at hd
  have hgen := original_canonical_degree_eq_zero_index N ℂ (D_jOver_ne_zero N ℂ)
  rw [← originalGenus_eq_zero_index, ← finrank_original_regularDifferentials_eq_genus] at hgen
  exact hd.symm.trans hgen

end
end Dubon2026.SourceFunctionField.CellGeometry
