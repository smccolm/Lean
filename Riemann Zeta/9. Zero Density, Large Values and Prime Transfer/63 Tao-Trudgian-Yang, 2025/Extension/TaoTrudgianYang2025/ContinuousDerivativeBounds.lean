import GuthMaynard.SecondOrderMeanValue

/-! Continuous derivative bounds transferred to literal finite differences. -/

noncomputable section

open Set RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem derivative_increment_bounds
    (F F' : ℝ → ℝ) {a b μ Λ : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hlo : ∀ x ∈ Icc a b, μ ≤ F' x)
    (hhi : ∀ x ∈ Icc a b, F' x ≤ Λ) :
    μ*(b-a) ≤ F b-F a ∧ F b-F a ≤ Λ*(b-a) := by
  rcases hab.eq_or_lt with he | hlt
  · subst b
    simp
  · obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope F F' hlt
      (fun y hy => (hF y hy).continuousAt.continuousWithinAt)
      (fun y hy => hF y ⟨hy.1.le,hy.2.le⟩)
    have hpos : 0 < b-a := sub_pos.mpr hlt
    have hlow := hlo x ⟨hx.1.le,hx.2.le⟩
    have hupp := hhi x ⟨hx.1.le,hx.2.le⟩
    rw [he] at hlow hupp
    exact ⟨(le_div_iff₀ hpos).mp hlow,(div_le_iff₀ hpos).mp hupp⟩

theorem continuous_second_difference_bounds
    (F F' F'' : ℝ → ℝ) {a b μ Λ x : ℝ}
    (hx : a ≤ x) (hxb : x+2 ≤ b)
    (hF : ∀ y ∈ Icc a b, HasDerivAt F (F' y) y)
    (hF' : ∀ y ∈ Icc a b, HasDerivAt F' (F'' y) y)
    (hlo : ∀ y ∈ Icc a b, μ ≤ F'' y)
    (hhi : ∀ y ∈ Icc a b, F'' y ≤ Λ) :
    μ ≤ (F (x+2)-F (x+1))-(F (x+1)-F x) ∧
      (F (x+2)-F (x+1))-(F (x+1)-F x) ≤ Λ := by
  have hin (y : ℝ) (hy : y ∈ Icc x (x+2)) : y ∈ Icc a b :=
    ⟨hx.trans hy.1,hy.2.trans hxb⟩
  obtain ⟨y,hy,he⟩ := second_order_mean_value F F' F'' x
    (fun y hy => hF y (hin y hy))
    (fun y hy => hF' y (hin y hy))
  have hlow := hlo y (hin y ⟨hy.1.le,hy.2.le⟩)
  have hupp := hhi y (hin y ⟨hy.1.le,hy.2.le⟩)
  constructor <;> linarith

end TaoTrudgianYang2025
