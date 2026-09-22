import TaoTrudgianYang2025.ExponentPairCorrelationSum
import TaoTrudgianYang2025.ExponentPairSourceWeyl

/-! The complete source Weyl estimate with the proved correlation sum. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem weyl_correlation_sum_majorant
    {X S V T N H L C B : ℝ}
    (hS : 0 ≤ S) (hV : 0 ≤ V) (hN : 0 < N) (hH : 0 < H)
    (hL : 0 ≤ L) (hLN : L ≤ 2*N) (hHN : H ≤ N)
    (hNT : N ≤ T) (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hweyl : H^2*X^2 ≤ (L+H)*(H*L+2*H*S))
    (hsum : S ≤ C*(H*V+(N^2/T)*B)) :
    X^2 ≤ 12*C*((N^2/H)*B+N*V) := by
  have hT : 0 < T := hN.trans_le hNT
  have hI : N^2/T ≤ N := (div_le_iff₀ hT).mpr (by nlinarith)
  have hsum' : S ≤ C*(H*V+N*B) := hsum.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hI (zero_le_one.trans hB))) (zero_le_one.trans hC))
  have hright : 0 ≤ H*L+2*H*S := by positivity
  have hraw : H^2*X^2 ≤ 3*N*(2*H*N+2*H*C*(H*V+N*B)) := by
    calc
      _ ≤ (L+H)*(H*L+2*H*S) := hweyl
      _ ≤ 3*N*(H*L+2*H*S) :=
        mul_le_mul_of_nonneg_right (by linarith) hright
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h₁ := mul_le_mul_of_nonneg_left hLN hH.le
        have h₂ := mul_le_mul_of_nonneg_left hsum' (show 0 ≤ 2*H by positivity)
        nlinarith
  have hCB : 1 ≤ C*B := by nlinarith
  have hnonneg := mul_nonneg (show 0 ≤ H*N^2 by positivity)
    (sub_nonneg.mpr hCB)
  have hpos := mul_nonneg (show 0 ≤ C*H^2*N by positivity) hV
  have heq : H^2*(12*C*((N^2/H)*B+N*V)) =
      12*C*(H*N^2*B+H^2*N*V) := by
    field_simp
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hH)).mp
  rw [heq]
  nlinarith

theorem source_exponentialSum_differencing_bound
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/2 ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N : ℝ) (a L H : ℕ),
          2 ≤ N → N ≤ T → 1 ≤ H → (H : ℝ) ≤ η₀*N →
          N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖exponentialSumAt F T N a (a+L)‖^2 ≤
            C*((N^2/(H : ℝ))*(1+Real.log N)+
              N*(T/N^2)^(k+ε)*N^(l+ε)*(H : ℝ)^(k+ε)) := by
  obtain ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,B,hB,hbound⟩ :=
    sum_sourceShiftCorrelation_le hkl hσ hε
  refine ⟨δ,hδ,P,hP,η₀,hη₀,hηhalf,12*B,by linarith,?_⟩
  intro F T N a L H hN hNT hH hHN ha hb hF
  have hNpos : 0 < N := by linarith
  have hT := hNpos.trans_le hNT
  have hHpos : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHN' : (H : ℝ) ≤ N := hHN.trans (by nlinarith)
  have hL : (L : ℝ)+1 ≤ 2*N := by
    push_cast at hb
    linarith
  have hlog : 1+Real.log H ≤ 1+Real.log N :=
    add_le_add le_rfl (Real.log_le_log hHpos hHN')
  have hbnd := hbound F T N a L H hT hN hHN ha hb hF
  have hsum : (∑ r ∈ Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) ≤
      B*((H : ℝ)*((T/N^2)^(k+ε)*N^(l+ε)*(H : ℝ)^(k+ε))+
        (N^2/T)*(1+Real.log N)) := by
    have hI : 0 ≤ N^2/T := by positivity
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hlog hI)
        ((T/N^2)^(k+ε)*N^(l+ε)*(H : ℝ)*(H : ℝ)^(k+ε))) (zero_le_one.trans hB)
    exact hbnd.trans (by nlinarith)
  have hw := source_exponentialSum_weyl F T N a L H
  simp only [Nat.cast_add,Nat.cast_one] at hw
  have hm := weyl_correlation_sum_majorant
    (show 0 ≤ ∑ r ∈ Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖ by positivity)
    (show 0 ≤ (T/N^2)^(k+ε)*N^(l+ε)*(H : ℝ)^(k+ε) by positivity)
    hNpos hHpos (show 0 ≤ (L : ℝ)+1 by positivity) hL hHN' hNT hB
    (show 1 ≤ 1+Real.log N by have := Real.log_nonneg (by linarith : 1 ≤ N); linarith)
    hw hsum
  convert hm using 1
  ring

end TaoTrudgianYang2025
