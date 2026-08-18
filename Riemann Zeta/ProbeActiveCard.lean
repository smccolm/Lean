import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset MeasureTheory Set
open scoped BigOperators Interval
open Classical

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem probe_active_card (a b R K : ℕ) :
    (hughesYoungActiveDyadicBoxes a b R K).card ≤ (K + 2) ^ 2 := by
  unfold hughesYoungActiveDyadicBoxes
  apply (Finset.card_filter_le _ _).trans_eq
  simp [pow_two]

end RiemannZeta.GuthMaynard
