import TaoTrudgianYang2025.AtkinsonPairCutoff
import TaoTrudgianYang2025.AtkinsonPhysicalPackets

/-! Actual general-pair stationary and local-mean packets on physical scales. -/

noncomputable section
open RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem ExponentPair.atkinson_physical_gram_budget_all_lengths {k l δ ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ F : ℝ, 0 < F ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H →
        H^δ ≤ G → G ≤ Real.sqrt (2*H) → 0 < L →
        IsSeparated G W → (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
          F*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  obtain ⟨F,hF,A,hA,hbudget⟩ := hpair.atkinson_physical_gram_budget hδ hν
  refine ⟨F,hF,A,hA,?_⟩
  intro H G L W hH hwidth hupper hL hsep hrange hdiam
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hG : 0 < G := (Real.rpow_pos_of_pos hH0 δ).trans_le hwidth
  have hmin : 0 < min L H := lt_min hL hH0
  have hd : ∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ min L H := by
    intro t ht u hu
    apply le_min (hdiam t ht u hu)
    rw [abs_le]
    constructor <;> linarith [(hrange t ht).1,(hrange t ht).2,
      (hrange u hu).1,(hrange u hu).2]
  have hb := hbudget H G (min L H) W hH hwidth hupper hmin
    (min_le_right _ _) hsep hrange hd
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hmin.le (min_le_left _ _) hpair.inTriangle.1) (sq_nonneg _)

theorem ExponentPair.atkinson_stationary_pair_packet {k l δ ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < L →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
          D*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  obtain ⟨D,hD,A,hA,hsource⟩ :=
    exists_atkinsonStationaryPacket_sq_le_physicalGram hδ
  obtain ⟨F,hF,B,hB,hbudget⟩ := hpair.atkinson_physical_gram_budget_all_lengths hδ hν
  refine ⟨D*F,mul_pos hD hF,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G L W hH hG hL hsep hrange hdiam
  by_cases hW : W.Nonempty
  · have hAH : A ≤ H := (le_max_left _ _).trans hH
    have hBH : B ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ
      (by linarith [hA.trans hAH] : 1 ≤ H) hG hW
      hrange
    have hs := hsource H G W hAH hG hrange
    have hp := mul_le_mul_of_nonneg_left
      (hbudget H G L W hBH hw.1 hw.2 hL hsep
        (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hdiam) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

theorem ExponentPair.atkinson_localMean_pair_packet {k l δ ε ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < L →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
          D*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram hδ hε
  obtain ⟨F,hF,B,hB,hbudget⟩ := hpair.atkinson_physical_gram_budget_all_lengths hδ hν
  refine ⟨C,hC,D*F,mul_pos hD hF,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G L W hH hG hL hsep hrange hdiam
  by_cases hW : W.Nonempty
  · have hAH : A ≤ H := (le_max_left _ _).trans hH
    have hBH : B ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ
      (by linarith [hA.trans hAH] : 1 ≤ H) hG hW
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1,
        (hrange t ht).2.2.1,(hrange t ht).2.2.2.1⟩)
    have hs := hsource H G W hAH hG hrange
    have hp := mul_le_mul_of_nonneg_left
      (hbudget H G L W hBH hw.1 hw.2 hL hsep
        (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hdiam) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

theorem ExponentPair.atkinson_localMean_pair_packet_above_fourthRoot {k l δ κ ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H → 0 < G → 0 < L →
        IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
          D*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  obtain ⟨C,hC,D,hD,A,hA,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram_above_fourthRoot hδ hκ
  obtain ⟨F,hF,B,hB,hbudget⟩ := hpair.atkinson_physical_gram_budget_all_lengths hδ hν
  refine ⟨C,hC,D*F,mul_pos hD hF,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G L W hH hG hL hsep hrange hdiam
  by_cases hW : W.Nonempty
  · have hAH : A ≤ H := (le_max_left _ _).trans hH
    have hBH : B ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ
      (by linarith [hA.trans hAH] : 1 ≤ H) hG hW
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1,
        (hrange t ht).2.2.1,(hrange t ht).2.2.2.1⟩)
    have hs := hsource H G W hAH hG hrange
    have hp := mul_le_mul_of_nonneg_left
      (hbudget H G L W hBH hw.1 hw.2 hL hsep
        (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hdiam) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

end TaoTrudgianYang2025
