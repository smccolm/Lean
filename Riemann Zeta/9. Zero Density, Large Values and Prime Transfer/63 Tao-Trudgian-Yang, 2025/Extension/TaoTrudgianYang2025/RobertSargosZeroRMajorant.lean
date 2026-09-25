import TaoTrudgianYang2025.SignedSquareRootSums

/-! Exact signed-shift summation of the zero-r second-derivative majorant. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_robertSargos_zero_r_majorant
    (M H Q : ℕ) {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q,
      (H:ℝ)*(1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
        2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam)))) ≤
      2*(H:ℝ)*Q+24*C*M*H*Real.sqrt (4*(H:ℝ)*lam)*Q*Real.sqrt Q+
        96*H*Real.sqrt Q/Real.sqrt (2*(H:ℝ)*lam) := by
  have he (q : ℤ) :
      (H:ℝ)*(1+12*(C*M*Real.sqrt (4*(H:ℝ)*|(q:ℝ)| *lam)+
        2/Real.sqrt (2*(H:ℝ)*|(q:ℝ)| *lam))) =
      (H:ℝ)+(12*C*M*H*Real.sqrt (4*(H:ℝ)*lam))*Real.sqrt |(q:ℝ)|+
        (24*H/Real.sqrt (2*(H:ℝ)*lam))*(1/Real.sqrt |(q:ℝ)|) := by
    rw [show 4*(H:ℝ)*|(q:ℝ)| *lam = (4*(H:ℝ)*lam)*|(q:ℝ)| by ring,
      show 2*(H:ℝ)*|(q:ℝ)| *lam = (2*(H:ℝ)*lam)*|(q:ℝ)| by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 4*(H:ℝ)*lam),
      Real.sqrt_mul (by positivity : 0 ≤ 2*(H:ℝ)*lam)]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,← Finset.mul_sum]
  have hcN : (Finset.Ioo (-(Q:ℤ)) Q).card ≤ 2*Q := by
    rw [Int.card_Ioo]
    omega
  have hc := mul_le_mul_of_nonneg_right
    (show ((Finset.Ioo (-(Q:ℤ)) Q).card:ℝ) ≤ 2*Q by exact_mod_cast hcN)
    (Nat.cast_nonneg (α := ℝ) H)
  have hs := mul_le_mul_of_nonneg_left (sum_signed_sqrt_le Q)
    (show 0 ≤ 12*C*M*H*Real.sqrt (4*(H:ℝ)*lam) by positivity)
  have hi := mul_le_mul_of_nonneg_left (sum_signed_inverse_sqrt_le Q)
    (show 0 ≤ 24*H/Real.sqrt (2*(H:ℝ)*lam) by positivity)
  calc
    _ ≤ (2*(Q:ℝ))*H+
        (12*C*M*H*Real.sqrt (4*(H:ℝ)*lam))*(2*(Q:ℝ)*Real.sqrt Q)+
        (24*H/Real.sqrt (2*(H:ℝ)*lam))*(4*Real.sqrt Q) :=
      add_le_add (add_le_add hc hs) hi
    _ = _ := by ring

end TaoTrudgianYang2025
