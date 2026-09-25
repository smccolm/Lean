import TaoTrudgianYang2025.RobertSargosZeroQBlock
import TaoTrudgianYang2025.RobertSargosZeroRWeighted

/-! The actual triangularly weighted nonzero-r, zero-q column. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_weighted_column_bound
    (f : ℝ → ℝ) (M H R : ℕ) {C lam : ℝ}
    (hR : 0 < R) (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hRmax : (R:ℝ) ≤ lam^(-(1:ℝ)/13))
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
      (1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H 0 r).re) ≤
        2*(R:ℝ)*((H:ℝ)*(1+120*C*(1+2*Real.pi*C)*M*(2*(R:ℝ)*lam)^((1:ℝ)/12))+
          2*H*R) := by
  have hCp : 0 ≤ C := zero_le_one.trans hC
  let B := (H:ℝ)*(1+120*C*(1+2*Real.pi*C)*M*(2*(R:ℝ)*lam)^((1:ℝ)/12))+2*H*R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (r : ℤ) (hr : r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0) :
      (1-|(r:ℝ)|/R)*(robertSargosTrimmedCorrelation f M H 0 r).re ≤ B := by
    obtain ⟨hr0,hrmem⟩ := Finset.mem_erase.mp hr
    have hrabs := signed_shift_abs_le hrmem
    have hp := robertSargos_zero_q_trimmed_correlation_bound f M H r hr0 hC hlam hsmall
      hM hH (hrabs.trans hRmax) hf hlo hhi
    have hmu : 2*|(r:ℝ)| *lam ≤ 2*(R:ℝ)*lam := by
      nlinarith [mul_le_mul_of_nonneg_right hrabs hlam.le]
    have hrpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2*|(r:ℝ)| *lam)
      hmu (by norm_num : (0:ℝ) ≤ 1/12)
    have hmain := mul_le_mul_of_nonneg_left hrpow
      (show 0 ≤ 120*C*(1+2*Real.pi*C)*M by positivity)
    have hblock := mul_le_mul_of_nonneg_left (add_le_add_left hmain 1) (Nat.cast_nonneg H)
    have herr := mul_le_mul_of_nonneg_left hrabs (show 0 ≤ 2*(H:ℝ) by positivity)
    have hb : ‖robertSargosTrimmedCorrelation f M H 0 r‖ ≤ B := by
      dsimp [B]
      nlinarith [hblock,herr]
    have hw0 := signed_triangular_weight_nonneg hR hrmem
    have hw1 : 1-|(r:ℝ)|/R ≤ 1 := by
      have hn : 0 ≤ |(r:ℝ)|/R := by positivity
      linarith
    calc
      _ ≤ (1-|(r:ℝ)|/R)*‖robertSargosTrimmedCorrelation f M H 0 r‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hw0
      _ ≤ ‖robertSargosTrimmedCorrelation f M H 0 r‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
      _ ≤ B := hb
  have hcard : ((Finset.Ioo (-(R:ℤ)) R).erase 0).card ≤ 2*R := by
    have he := Finset.card_le_card (Finset.erase_subset 0 (Finset.Ioo (-(R:ℤ)) R))
    rw [Int.card_Ioo] at he
    omega
  calc
    _ ≤ ∑ _r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0, B := Finset.sum_le_sum hpoint
    _ ≤ 2*(R:ℝ)*B := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
    _ = _ := rfl

end TaoTrudgianYang2025
