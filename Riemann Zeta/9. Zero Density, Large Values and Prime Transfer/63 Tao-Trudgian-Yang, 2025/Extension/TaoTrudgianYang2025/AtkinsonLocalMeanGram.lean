import TaoTrudgianYang2025.AtkinsonPacketGram

/-!
# Physical local-mean excess packets consumed by the maximal Gram bound

The positive part subtracts the already proved stationary error from the
actual local zeta integral. No local-mean entry or Gram estimate is assumed.
The fourth-root-width restriction remains explicit in both consumers.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

def atkinsonLocalMeanExcess (G t error : ℝ) : ℝ :=
  max 0 ((∫ u in t-G..t+G, zetaMomentCriticalNorm u^2)-error)

theorem atkinsonLocalMeanExcess_nonneg (G t error : ℝ) :
    0 ≤ atkinsonLocalMeanExcess G t error := le_max_left _ _

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_gramBudget
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquareLocalMean_le_stationary hδ hε
  obtain ⟨D,hD,B,_,hpacket⟩ := exists_atkinsonStationaryPacket_sq_le_gramBudget hδ
  refine ⟨C,hC,(2*Real.exp 1)^2*D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hp := hpacket H G W hHB hG (fun t ht => by
    obtain ⟨hHt,hl,hu,_⟩ := hrange t ht
    exact ⟨hHt,hl,hu⟩)
  have hsum :
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε)))) ≤
        (2*Real.exp 1)*∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hHt,hl,hu,hq⟩ := hrange t ht
    have hs := hsource t G (hHA.trans hHt) hl hu hq
    have hre := mul_le_mul_of_nonneg_left
      (Complex.re_le_norm (atkinsonStationaryLeadingSum t G (Real.log t)))
      (by positivity : 0 ≤ 2*Real.exp 1)
    apply max_le (by positivity)
    dsimp only
    linarith
  calc
    _ ≤ ((2*Real.exp 1)*∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun t _ => atkinsonLocalMeanExcess_nonneg _ _ _)) hsum 2
    _ = (2*Real.exp 1)^2*(∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 :=
      mul_pow _ _ _
    _ ≤ (2*Real.exp 1)^2*(D*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by ring

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_gramBudget_above_fourthRoot
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquareLocalMean_le_stationary_above_fourthRoot hδ hκ
  obtain ⟨D,hD,B,_,hpacket⟩ := exists_atkinsonStationaryPacket_sq_le_gramBudget hδ
  refine ⟨C,hC,(2*Real.exp 1)^2*D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G W hH hG hrange
  have hHA : A ≤ H := (le_max_left _ _).trans hH
  have hHB : B ≤ H := (le_max_right _ _).trans hH
  have hp := hpacket H G W hHB hG (fun t ht => by
    obtain ⟨hHt,hl,hu,_⟩ := hrange t ht
    exact ⟨hHt,hl,hu⟩)
  have hsum :
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t)) ≤
        (2*Real.exp 1)*∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨hHt,hl,hu,hq⟩ := hrange t ht
    have hs := hsource t G (hHA.trans hHt) hl hu hq
    have hre := mul_le_mul_of_nonneg_left
      (Complex.re_le_norm (atkinsonStationaryLeadingSum t G (Real.log t)))
      (by positivity : 0 ≤ 2*Real.exp 1)
    apply max_le (by positivity)
    dsimp only
    linarith
  calc
    _ ≤ ((2*Real.exp 1)*∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun t _ => atkinsonLocalMeanExcess_nonneg _ _ _)) hsum 2
    _ = (2*Real.exp 1)^2*(∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 :=
      mul_pow _ _ _
    _ ≤ (2*Real.exp 1)^2*(D*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = _ := by ring

end TaoTrudgianYang2025
