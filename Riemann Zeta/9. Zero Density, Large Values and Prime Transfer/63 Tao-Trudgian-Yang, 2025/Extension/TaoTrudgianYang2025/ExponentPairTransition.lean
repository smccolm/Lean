import TaoTrudgianYang2025.BetaModelSumBound
import TaoTrudgianYang2025.ExponentPair

/-! A uniform transition bound between the first-derivative and
large-parameter exponent-pair regimes. -/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sqrt_add_div_sqrt_le_transition {T N : ℝ}
    (hN : 0 < N) (hlo : N/4 ≤ T) (hhi : T ≤ N) :
    Real.sqrt T+N/Real.sqrt T ≤ 3*Real.sqrt N := by
  have hT : 0 < T := by linarith
  have ht := Real.sqrt_pos.mpr hT
  have hn := Real.sqrt_pos.mpr hN
  have ht2 := Real.sq_sqrt hT.le
  have hn2 := Real.sq_sqrt hN.le
  have hlow : Real.sqrt N ≤ 2*Real.sqrt T := by nlinarith
  have hu : Real.sqrt T ≤ Real.sqrt N := Real.sqrt_le_sqrt hhi
  have hd : N/Real.sqrt T ≤ 2*Real.sqrt N := by
    apply (div_le_iff₀ ht).mpr
    nlinarith
  linarith

theorem sqrt_le_exponentPair_transition {k l ε T N : ℝ}
    (hk : 0 ≤ k) (hl : 1/2 ≤ l) (hε : 0 ≤ ε)
    (hN : 1 ≤ N) (hlo : N/4 ≤ T) :
    Real.sqrt N ≤ (4 : ℝ)^(k+ε)*((T/N)^(k+ε)*N^(l+ε)) := by
  have hNpos := zero_lt_one.trans_le hN
  have hTpos : 0 < T := by linarith
  have hratio : 1 ≤ 4*(T/N) := by
    have hh := (le_div_iff₀ hNpos).mpr (show (1/4)*N ≤ T by linarith)
    linarith
  have hpow : 1 ≤ (4 : ℝ)^(k+ε)*(T/N)^(k+ε) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.one_le_rpow hratio (by linarith)
  have hNpow : Real.sqrt N ≤ N^(l+ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNpos.le (l+ε))
  nlinarith

theorem norm_exponentialSumAt_le_transition
    {k l σ δ ε T N : ℝ} {F : ℝ → ℝ} {a b : ℕ}
    (hk : 0 ≤ k) (hl : 1/2 ≤ l) (hε : 0 ≤ ε)
    (hσ : 0 < σ) (hN : 4 ≤ N)
    (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hlo : N/4 ≤ T) (hhi : T ≤ N) :
    ‖exponentialSumAt F T N a b‖ ≤
      (3*modelPhaseSumConstant σ*(4 : ℝ)^(k+ε))*
        ((T/N)^(k+ε)*N^(l+ε)) := by
  have hNpos : 0 < N := by linarith
  have hs := norm_exponentialSumAt_le_secondDerivative hσ (by linarith)
    (by linarith) hδ hF ha hb (by nlinarith)
  have hc := modelPhaseSumConstant_pos hσ
  calc
    _ ≤ modelPhaseSumConstant σ*(Real.sqrt T+N/Real.sqrt T) := hs
    _ ≤ modelPhaseSumConstant σ*(3*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (sqrt_add_div_sqrt_le_transition hNpos hlo hhi) hc.le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (sqrt_le_exponentPair_transition hk hl hε (by linarith) hlo)
        (show 0 ≤ 3*modelPhaseSumConstant σ by positivity)
      nlinarith

end TaoTrudgianYang2025
