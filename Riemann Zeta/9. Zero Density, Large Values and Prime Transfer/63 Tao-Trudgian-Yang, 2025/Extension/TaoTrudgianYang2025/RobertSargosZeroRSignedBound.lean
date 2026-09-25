import TaoTrudgianYang2025.RobertSargosZeroRPositiveBound

/-! Either nonzero sign of q, through the proved source conjugation identity. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_source_bound
    (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) {C lam : ℝ}
    (hC : 0 ≤ C) (hh : 0 < h) (hq : q ≠ 0) (hlam : 0 < lam)
    (hscale : 2*(h:ℝ)*|(q:ℝ)| *lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosZeroRSource f M h q‖ ≤
      1+12*(C*M*Real.sqrt (2*(h:ℝ)*|(q:ℝ)| *lam)+
        2/Real.sqrt (2*(h:ℝ)*|(q:ℝ)| *lam)) := by
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hqr : (q:ℝ) < 0 := by exact_mod_cast hneg
    have hs : 2*(h:ℝ)*((-q:ℤ):ℝ)*lam ≤ 1 := by
      simpa only [Int.cast_neg,abs_of_neg hqr] using hscale
    have hb := robertSargos_zero_r_source_positive_bound f M h (-q)
      hC hh (by omega) hlam hs hf hlo hhi
    rw [norm_robertSargos_zero_r_source_neg] at hb
    simpa only [Int.cast_neg,abs_of_neg hqr] using hb
  · have hqr : (0:ℝ) < q := by exact_mod_cast hpos
    have hs : 2*(h:ℝ)*(q:ℝ)*lam ≤ 1 := by
      simpa only [abs_of_pos hqr] using hscale
    simpa only [abs_of_pos hqr] using
      robertSargos_zero_r_source_positive_bound f M h q hC hh hpos hlam hs hf hlo hhi

end TaoTrudgianYang2025
