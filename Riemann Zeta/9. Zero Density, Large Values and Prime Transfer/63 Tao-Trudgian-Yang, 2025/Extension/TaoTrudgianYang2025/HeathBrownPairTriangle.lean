import TaoTrudgianYang2025.HeathBrownPairParameters
import TaoTrudgianYang2025.ExponentPair

/-! Triangle and slope of Heath--Brown's exact family, including the first order. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem heathBrownPair_slope {r : ℝ} (hr : 3 ≤ r) :
    1/2 ≤ heathBrownPairL r-heathBrownPairK r := by
  have h0 : 0 < r := by linarith
  have h1 : 0 < r-1 := by linarith
  have h2 : 0 < r+2 := by linarith
  have hx : 0 ≤ r-3 := by linarith
  have hid : heathBrownPairL r-heathBrownPairK r-1/2 =
      ((r-3)^4+12*(r-3)^3+45*(r-3)^2+62*(r-3)+20)/
        (2*r*(r-1)^2*(r+2)) := by
    unfold heathBrownPairL heathBrownPairK
    field_simp
    ring
  have hn : 0 ≤ heathBrownPairL r-heathBrownPairK r-1/2 := by
    rw [hid]
    positivity
  linarith

theorem heathBrownPair_sum_le {r : ℝ} (hr : 3 ≤ r) :
    heathBrownPairK r+heathBrownPairL r ≤ 1 := by
  have h0 : 0 < r := by linarith
  have h1 : 0 < r-1 := by linarith
  have h2 : 0 < r+2 := by linarith
  have h3 : 0 ≤ 3*r-1 := by linarith
  have h4 : 0 ≤ r-2 := by linarith
  have hid : 1-heathBrownPairK r-heathBrownPairL r =
      (3*r-1)*(r-2)/(r*(r-1)^2*(r+2)) := by
    unfold heathBrownPairL heathBrownPairK
    field_simp
    ring
  have hn : 0 ≤ 1-heathBrownPairK r-heathBrownPairL r := by
    rw [hid]
    positivity
  linarith

theorem heathBrownPair_inTriangle {r : ℝ} (hr : 3 ≤ r) :
    InExponentPairTriangle (heathBrownPairK r) (heathBrownPairL r) := by
  have hp := heathBrownPairK_pos hr
  have hs := heathBrownPair_slope hr
  have hsum := heathBrownPair_sum_le hr
  exact ⟨hp.le,by linarith,by linarith,by linarith,hsum⟩

end TaoTrudgianYang2025

