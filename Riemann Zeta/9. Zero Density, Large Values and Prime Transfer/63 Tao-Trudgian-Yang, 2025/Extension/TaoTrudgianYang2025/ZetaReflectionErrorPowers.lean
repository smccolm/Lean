import TaoTrudgianYang2025.ZetaReflectionTimeBounds

/-! Explicit powers controlling all retained reflection remainders. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem reflection_epsilon_remainder_power {N T t b ε : ℝ}
    (hN : 0 < N) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hscale : T ≤ N^b) (hε : 0 ≤ ε) :
    (t/(2*Real.pi))^ε ≤ N^(b*ε) := by
  obtain ⟨_,hl,hpos⟩ := reflection_scaled_height_bounds hT ht
  calc
    _ ≤ T^ε := Real.rpow_le_rpow hpos.le hl hε
    _ ≤ (N^b)^ε := Real.rpow_le_rpow hT.le hscale hε
    _ = _ := (Real.rpow_mul hN.le b ε).symm

theorem reflection_tail_remainder_bounded {N T t b : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hscale : T ≤ N^b) (j : ℕ) (hj : b/2 ≤ (j : ℝ)+1) :
    Real.sqrt (t/(2*Real.pi))*
      (zetaReflectionTailConstant j/(4*Real.pi*N)^(j+1)) ≤ zetaReflectionTailConstant j := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hs : Real.sqrt (t/(2*Real.pi)) ≤ N^(j+1) := by
    calc
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (reflection_scaled_height_bounds hT ht).2.1
      _ ≤ N^(b/2) := reflection_sqrt_upper_power hNpos hscale
      _ ≤ N^((j : ℝ)+1) := Real.rpow_le_rpow_of_exponent_le hN hj
      _ = _ := by rw [show (j : ℝ)+1 = ((j+1 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  have hbase : N ≤ 4*Real.pi*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 4*Real.pi by nlinarith [Real.pi_gt_three]) hNpos.le
  have hpow := pow_le_pow_left₀ hNpos.le hbase (j+1)
  have hden : 0 < (4*Real.pi*N)^(j+1) := by positivity
  have hm := zetaReflectionTailConstant_nonneg j
  calc
    _ = (Real.sqrt (t/(2*Real.pi))*zetaReflectionTailConstant j)/(4*Real.pi*N)^(j+1) := by ring
    _ ≤ zetaReflectionTailConstant j := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_le_mul_of_nonneg_right (hs.trans hpow) hm]

theorem reflection_remainders_le_power {N T t a b ε α C : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (ht : t ∈ Icc T (2*T))
    (hlo : N^a ≤ T) (hhi : T ≤ N^b) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hα : 0 ≤ α) (hfirst : 1-a/2 ≤ α) (hsecond : b*ε ≤ α)
    (j : ℕ) (hj : b/2 ≤ (j : ℝ)+1) :
    Real.sqrt (t/(2*Real.pi))*
        (zetaReflectionTailConstant j/(4*Real.pi*N)^(j+1))+
      C*(N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) ≤
        (C*(Real.sqrt (2*Real.pi)+1)+zetaReflectionTailConstant j)*N^α := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hfirst' := (reflection_source_remainder_power hNpos hT ht hlo).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hfirst)
      (Real.sqrt_nonneg _))
  have hsecond' := (reflection_epsilon_remainder_power hNpos hT ht hhi hε).trans
    (Real.rpow_le_rpow_of_exponent_le hN hsecond)
  have htail := reflection_tail_remainder_bounded hN hT ht hhi j hj
  have hunit : 1 ≤ N^α := Real.one_le_rpow hN hα
  have htail' : zetaReflectionTailConstant j ≤ zetaReflectionTailConstant j*N^α := by
    nlinarith [zetaReflectionTailConstant_nonneg j]
  have hsource := mul_le_mul_of_nonneg_left (add_le_add hfirst' hsecond') hC
  nlinarith

end TaoTrudgianYang2025
