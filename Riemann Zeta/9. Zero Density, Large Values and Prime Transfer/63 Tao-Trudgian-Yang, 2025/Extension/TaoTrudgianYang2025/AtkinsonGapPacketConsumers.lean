import TaoTrudgianYang2025.AtkinsonGapBudget

/-!
# Actual stationary and local-zeta packets with numerical gap bounds

These consumers compose the actual source, height-dependent Gram argument,
uniform truncated cancellation, and the derived physical cutoff geometry.
They assume no oscillatory-sum or zeta-entry theorem. The original
fourth-root-width restrictions on the local-mean error remain explicit.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_atkinsonStationaryPacket_sq_le_physicalGap {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_atkinsonStationaryPacket_sq_le_physicalGram hδ
  obtain ⟨B,_,hgap⟩ := exists_atkinsonPhysicalGramBudget_le_gapBudget hδ
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have hg := hgap H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hg (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram hδ hε
  obtain ⟨B,_,hgap⟩ := exists_atkinsonPhysicalGramBudget_le_gapBudget hδ
  refine ⟨C,hC,D,hD,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have hg := hgap H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hg (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGap_above_fourthRoot
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGapBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram_above_fourthRoot hδ hκ
  obtain ⟨B,_,hgap⟩ := exists_atkinsonPhysicalGramBudget_le_gapBudget hδ
  refine ⟨C,hC,D,hD,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := by linarith [hA.trans hHA]
  have hs := hsource H G W hHA hG hrange
  have hg := hgap H G W hHB (fun t ht =>
    ⟨(hrange t ht).1,(hrange t ht).2.1,(hrange t ht).2.2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hg (by positivity))

end TaoTrudgianYang2025
