import TaoTrudgianYang2025.AtkinsonGapArithmetic

/-!
# Actual source packets with fully numerical epsilon-weighted gap budgets

The literal coefficient energy is now replaced using its proved arithmetic
estimate. Constants precede the actual heights, widths and finite sets.
Source errors and their width restrictions are unchanged.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_atkinsonStationaryPacket_sq_le_arithmeticGap {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_atkinsonStationaryPacket_sq_le_physicalGap hδ
  obtain ⟨E,hE,B,_,henergy⟩ := exists_atkinsonPhysicalGapBudget_le_arithmetic hδ hη
  refine ⟨C*E,mul_pos hC hE,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have he := henergy H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  apply (hs.trans (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq
  ring

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap hδ hε
  obtain ⟨E,hE,B,_,henergy⟩ := exists_atkinsonPhysicalGapBudget_le_arithmetic hδ hη
  refine ⟨C,hC,D*E,mul_pos hD hE,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have he := henergy H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  apply (hs.trans (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq
  ring

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap_above_fourthRoot
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonArithmeticGapBudget η (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap_above_fourthRoot hδ hκ
  obtain ⟨E,hE,B,_,henergy⟩ := exists_atkinsonPhysicalGapBudget_le_arithmetic hδ hη
  refine ⟨C,hC,D*E,mul_pos hD hE,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have he := henergy H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  apply (hs.trans (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq
  ring

end TaoTrudgianYang2025
