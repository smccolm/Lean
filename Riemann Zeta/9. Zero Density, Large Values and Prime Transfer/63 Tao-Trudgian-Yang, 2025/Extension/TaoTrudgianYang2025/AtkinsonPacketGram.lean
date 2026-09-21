import TaoTrudgianYang2025.AtkinsonDyadicGramBudget

/-!
# Actual complete stationary packets consumed by the maximal Gram budget

The common integer cutoff is the maximum of the actual source cutoffs
of the packet. It is not a freely supplied analytic hypothesis.
All physical heights, widths, coefficients and prefix maxima are linked.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def atkinsonPacketCutoff (G : ℝ) (W : Finset ℝ) : ℕ :=
  W.sup (fun t => atkinsonSourceCutoff t G (Real.log t))

theorem atkinsonSourceCutoff_le_packet (G : ℝ) {W : Finset ℝ} {t : ℝ} (ht : t ∈ W) :
    atkinsonSourceCutoff t G (Real.log t) ≤ atkinsonPacketCutoff G W := by
  unfold atkinsonPacketCutoff
  exact Finset.le_sup (f := fun t : ℝ => atkinsonSourceCutoff t G (Real.log t)) ht

theorem exists_sum_norm_atkinsonStationary_le_undamped {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖) ≤
        C*G*H^(-(1/4:ℝ))*
          ∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t (atkinsonPacketCutoff G W) := by
  obtain ⟨C,hC,A,hA,hmain⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  refine ⟨C,hC,A,hA,?_⟩
  intro H G W hH hG hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨hHt,hlower,hupper⟩ := hrange t ht
  have ht0 : 0 < t := hH0.trans_le hHt
  have hp := Real.rpow_le_rpow_of_nonpos hH0 hHt (by norm_num : -(1/4:ℝ) ≤ 0)
  have hphase := (atkinsonFullDyadicPhaseBound_le_undamped ht0 G _).trans
    (atkinsonUndampedDyadicPhaseBound_mono t (atkinsonSourceCutoff_le_packet G ht))
  apply (hmain t G (hH.trans hHt) hlower hupper).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hphase
    (atkinsonFullDyadicPhaseBound_nonneg _ _ _) (by positivity)

theorem exists_atkinsonStationaryPacket_sq_le_gramBudget {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G →
      (∀ t ∈ W, H ≤ t ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W := by
  obtain ⟨C,hC,A,hA,hbound⟩ := exists_sum_norm_atkinsonStationary_le_undamped hδ
  refine ⟨C^2,by positivity,A,hA,?_⟩
  intro H G W hH hG hrange
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hsum := hbound H G W hH hG hrange
  have hgram := sum_atkinsonUndampedDyadicPhaseBound_sq_le_budget (atkinsonPacketCutoff G W) W
  have hp : (H^(-(1/4:ℝ)))^2 = H^(-(1/2:ℝ)) := by
    rw [sq,← Real.rpow_add hH0]
    congr 1
    norm_num
  calc
    _ ≤ (C*G*H^(-(1/4:ℝ))*
        ∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t (atkinsonPacketCutoff G W))^2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    _ = (C*G*H^(-(1/4:ℝ)))^2*
        (∑ t ∈ W, atkinsonUndampedDyadicPhaseBound t (atkinsonPacketCutoff G W))^2 := mul_pow _ _ _
    _ ≤ (C*G*H^(-(1/4:ℝ)))^2*atkinsonDyadicGramBudget (atkinsonPacketCutoff G W) W :=
      mul_le_mul_of_nonneg_left hgram (sq_nonneg _)
    _ = _ := by rw [mul_pow,mul_pow,hp]

end TaoTrudgianYang2025
