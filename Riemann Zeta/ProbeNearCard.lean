import RiemannZeta.GuthMaynard.HughesYoungShiftRanges

open Complex Finset MeasureTheory Set
open scoped BigOperators Interval
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem probe_near_card
    {T P X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hY : 0 < Y) (hP : 0 ≤ P) :
    (hughesYoungNearShifts T P X Y a b M N).card ≤
      2 * ⌊P * Y / T⌋₊ + 1 := by
  let K : ℕ := ⌊P * Y / T⌋₊
  have hR : 0 ≤ P * Y / T := by positivity
  have hsub : hughesYoungNearShifts T P X Y a b M N ⊆
      Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro r hr
    have hrange := (mem_hughesYoungNearShifts_iff.mp hr).2.2.2.1
    have habs : |(r : ℝ)| ≤ P * Y / T := by
      have hdiv : 0 < Y := hY
      have hTnonneg : 0 ≤ T := hT.le
      have hYnonneg : 0 ≤ Y := hY.le
      calc
        |(r : ℝ)| = T * (|(r : ℝ)| / Y) * Y / T := by field_simp
        _ ≤ P * Y / T := by gcongr
    have hnat : r.natAbs ≤ K := by
      dsimp only [K]
      exact Nat.le_floor (by simpa using habs)
    simp only [Finset.mem_Icc]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * K + 1 := by
      rw [Int.card_Icc]
      have hform : (K : ℤ) + 1 - -(K : ℤ) = (K : ℤ) + 1 + (K : ℤ) := by ring
      rw [hform]
      have hnonneg : (0 : ℤ) ≤ (K : ℤ) + 1 + (K : ℤ) := by omega
      apply Int.ofNat_inj.mp
      rw [Int.toNat_of_nonneg hnonneg]
      norm_num
      ring
    _ = _ := rfl

end RiemannZeta.GuthMaynard
