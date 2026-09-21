import TaoTrudgianYang2025.AtkinsonLocalMeanGram

/-!
# A common physical cutoff for maximal Gram packets

For heights in [H,2H], the maximum of the actual source cutoffs is
bounded by the same source cutoff at 2H. Only the nonnegative Gram
budget is enlarged; the stationary source is never extended.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem atkinsonSourceCutoff_log_mono_height {t u G : ℝ}
    (ht : 1 ≤ t) (htu : t ≤ u) (hG : 0 < G) :
    atkinsonSourceCutoff t G (Real.log t) ≤ atkinsonSourceCutoff u G (Real.log u) := by
  apply Nat.ceil_mono
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := ht0.trans_le htu
  have hlog : Real.log t ≤ Real.log u := Real.log_le_log ht0 htu
  have hratio := div_le_div_of_nonneg_right hlog hG.le
  have hs := pow_le_pow_left₀ (div_nonneg (Real.log_nonneg ht) hG.le) hratio 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left htu (by norm_num)) hs
    (sq_nonneg _) (by positivity)

theorem atkinsonPacketCutoff_le_height {H G : ℝ} {W : Finset ℝ}
    (hH : 1 ≤ H) (hG : 0 < G) (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) :
    atkinsonPacketCutoff G W ≤ atkinsonSourceCutoff (2*H) G (Real.log (2*H)) := by
  unfold atkinsonPacketCutoff
  apply Finset.sup_le
  intro t ht
  exact atkinsonSourceCutoff_log_mono_height (hH.trans (hrange t ht).1) (hrange t ht).2 hG

theorem atkinsonDyadicGramBudget_mono {N K : ℕ} (hNK : N ≤ K) (W : Finset ℝ) :
    atkinsonDyadicGramBudget N W ≤ atkinsonDyadicGramBudget K W := by
  have hlog := Nat.clog_mono_right 2 hNK
  unfold atkinsonDyadicGramBudget
  apply mul_le_mul (by exact_mod_cast hlog)
  · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hlog)
    intro j _ _
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
      atkinsonPrefixGramMax_nonneg _ _ t u))
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (atkinsonBlockCoefficientEnergy_nonneg _ _))
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
      atkinsonPrefixGramMax_nonneg _ _ t u))
  · exact Nat.cast_nonneg _

theorem exists_atkinsonStationaryPacket_sq_le_physicalGram {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,A,hA,hpacket⟩ := exists_atkinsonStationaryPacket_sq_le_gramBudget hδ
  refine ⟨C,hC,A,hA,?_⟩
  intro H G W hH hG hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hcut := atkinsonPacketCutoff_le_height (by linarith [hA.trans hH] : 1 ≤ H) hG
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  apply (hpacket H G W hH hG (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.2⟩)).trans
  exact mul_le_mul_of_nonneg_left (atkinsonDyadicGramBudget_mono hcut W) (by positivity)


theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hpacket⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_gramBudget hδ hε
  refine ⟨C,hC,D,hD,A,hA,?_⟩
  intro H G W hH hG hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hcut := atkinsonPacketCutoff_le_height (by linarith [hA.trans hH] : 1 ≤ H) hG
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  apply (hpacket H G W hH hG (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.2⟩)).trans
  exact mul_le_mul_of_nonneg_left (atkinsonDyadicGramBudget_mono hcut W) (by positivity)

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalGram_above_fourthRoot
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W := by
  obtain ⟨C,hC,D,hD,A,hA,hpacket⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_gramBudget_above_fourthRoot hδ hκ
  refine ⟨C,hC,D,hD,A,hA,?_⟩
  intro H G W hH hG hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hcut := atkinsonPacketCutoff_le_height (by linarith [hA.trans hH] : 1 ≤ H) hG
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
  apply (hpacket H G W hH hG (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.2⟩)).trans
  exact mul_le_mul_of_nonneg_left (atkinsonDyadicGramBudget_mono hcut W) (by positivity)

end TaoTrudgianYang2025
