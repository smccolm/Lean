import TaoTrudgianYang2025.AtkinsonRootFourierSupport

/-!
# Uniform second-order Fourier decay of the actual root amplitude

Both global derivative bounds are constructed from the physical source.
The native Fourier integration-by-parts theorem is applied at order two.
-/

noncomputable section

open Complex Set
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem support_iteratedDeriv_atkinsonRootFourierAmplitude {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (α : ℝ) (j : ℕ) :
    Function.support (iteratedDeriv j (atkinsonRootFourierAmplitude T G L α)) ⊆
      Icc (1 / 4) 1 := by
  have hs : tsupport (iteratedDeriv j (atkinsonRootFourierAmplitude T G L α)) ⊆
      tsupport (atkinsonRootFourierAmplitude T G L α) := by
    induction j with
    | zero => simp
    | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
  exact (subset_tsupport _).trans (hs.trans
    (closure_minimal (support_atkinsonRootFourierAmplitude hT hG hL hwidth α) isClosed_Icc))

theorem exists_norm_fourier_atkinsonRootFourierAmplitude_le (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L ξ : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      (1 + |ξ|) ^ 2 * ‖𝓕 (atkinsonRootFourierAmplitude T G L α) ξ‖ ≤
        C * G * T ^ (-α) * T ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonRootFourierAmplitude α
  refine ⟨6 * C, by positivity, ?_⟩
  intro T G L ξ hT hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hf := hbound T G L hT hG hGT hL hwidth
  have hb0 : ∀ u, ‖iteratedDeriv 0 (atkinsonRootFourierAmplitude T G L α) u‖ ≤
      C * G * T ^ (-α) := by
    intro u
    simp only [iteratedDeriv_zero]
    by_cases hu : u ∈ Icc (1 / 4 : ℝ) 1
    · exact hf.norm_le u hu
    · have hz : atkinsonRootFourierAmplitude T G L α u = 0 := by
        by_contra hn
        exact hu (support_atkinsonRootFourierAmplitude hT0 hG hL0 hwidth α hn)
      rw [hz, norm_zero]
      positivity
  have hb2 : ∀ u, ‖iteratedDeriv 2 (atkinsonRootFourierAmplitude T G L α) u‖ ≤
      C * G * T ^ (-α) * T ^ 2 := by
    intro u
    by_cases hu : u ∈ Icc (1 / 4 : ℝ) 1
    · exact hf.second_le u hu
    · have hz : iteratedDeriv 2 (atkinsonRootFourierAmplitude T G L α) u = 0 := by
        by_contra hn
        exact hu (support_iteratedDeriv_atkinsonRootFourierAmplitude hT0 hG hL0 hwidth α 2 hn)
      rw [hz, norm_zero]
      positivity
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order 2
    (contDiff_atkinsonRootFourierAmplitude hT0 hG hL0 hwidth α)
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
    (support_atkinsonRootFourierAmplitude hT0 hG hL0 hwidth α)
    (by positivity) (by positivity) hb0 hb2 ξ
  apply h.trans
  have hm : C * G * T ^ (-α) ≤ C * G * T ^ (-α) * T ^ 2 :=
    le_mul_of_one_le_right (by positivity) (by nlinarith)
  nlinarith

end TaoTrudgianYang2025
