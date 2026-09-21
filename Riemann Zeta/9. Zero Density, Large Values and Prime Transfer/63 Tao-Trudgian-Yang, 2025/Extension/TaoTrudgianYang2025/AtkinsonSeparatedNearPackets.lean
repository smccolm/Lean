import TaoTrudgianYang2025.AtkinsonNearGapBudget

/-!
# Actual source packets after summing the separated near heights

The source cutoffs, divisor energy, main sum, local integral and error
restrictions are unchanged. The same physical width G is the separation.
The remaining budget contains only explicit far-gap sums.
-/

noncomputable section

open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_atkinsonStationaryPacket_sq_le_separatedNear {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_atkinsonStationaryPacket_sq_le_arithmeticGap hδ hη
  refine ⟨C,hC,A,hA,?_⟩
  intro H G W hH hG hSep hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hs := hsource H G W hH hG hrange
  have hb := atkinsonArithmeticGapBudget_le_separated (η := η)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    hH0 hG hSep (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hb (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap hδ hε hη
  refine ⟨C,hC,D,hD,A,hA,?_⟩
  intro H G W hH hG hSep hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hs := hsource H G W hH hG hrange
  have hb := atkinsonArithmeticGapBudget_le_separated (η := η)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    hH0 hG hSep (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hb (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear_above_fourthRoot
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonSeparatedGapBudget η H G (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_arithmeticGap_above_fourthRoot hδ hκ hη
  refine ⟨C,hC,D,hD,A,hA,?_⟩
  intro H G W hH hG hSep hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hs := hsource H G W hH hG hrange
  have hb := atkinsonArithmeticGapBudget_le_separated (η := η)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    hH0 hG hSep (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  exact hs.trans (mul_le_mul_of_nonneg_left hb (by positivity))

end TaoTrudgianYang2025

