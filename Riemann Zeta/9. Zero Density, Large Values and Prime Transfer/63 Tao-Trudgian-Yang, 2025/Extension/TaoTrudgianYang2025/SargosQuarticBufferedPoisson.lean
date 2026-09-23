import TaoTrudgianYang2025.SargosQuarticPoisson
import TaoTrudgianYang2025.BetaBufferedBoundary

/-! Original quartic Poisson entry with a controlled, varying cutoff family.
The source loss is proved for the literal integer interval (N,2N]. -/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticBufferedCutoff (N : ℕ) (η : ℝ) : ℝ → ℝ :=
  modelPhaseBufferedCutoff (((N : ℝ)+1)/N) 2 η

theorem sargosQuarticBufferedCutoff_contDiff (N : ℕ) (η : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticBufferedCutoff N η) :=
  modelPhaseBufferedCutoff_contDiff _ _ _

theorem sargosQuarticBufferedCutoff_tsupport {N : ℕ} {η : ℝ}
    (hN : 1 ≤ N) (hη : 0 < η) :
    tsupport (sargosQuarticBufferedCutoff N η) ⊆ Ioo (1 : ℝ) 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply modelPhaseBufferedCutoff_tsupport_model hη _ le_rfl
  apply (one_le_div hNp).mpr
  linarith

theorem sargosQuartic_buffered_poisson {N : ℕ} {η : ℝ}
    (hN : 1 ≤ N) (hη : 0 < η) (α γ : ℝ) :
    Summable (fun m : ℤ => ‖sargosQuarticFourierMode (sargosQuarticBufferedCutoff N η) N α γ m‖) ∧
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        ∑' m : ℤ, sargosQuarticFourierMode (sargosQuarticBufferedCutoff N η) N α γ m‖ ≤
          4*N*η+2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hχ := sargosQuarticBufferedCutoff_contDiff N η
  have hs := sargosQuarticBufferedCutoff_tsupport hN hη
  refine ⟨summable_norm_sargosQuarticFourierMode hχ hs hNp α γ,?_⟩
  rw [← sargosQuartic_weighted_poisson hχ hs hNp α γ,sargosQuarticSum_eq_fourier_interval]
  let F : ℝ → ℝ := fun u => sargosQuarticPhase α γ ((N : ℝ)*u)
  have he (n : ℤ) : (1 : ℝ)*F ((n : ℝ)/N) = sargosQuarticPhase α γ n := by
    dsimp only [F,one_mul]
    rw [mul_div_cancel₀ _ hNp.ne',one_mul]
  have ha : (((N : ℤ)+1 : ℤ) : ℝ)/N = ((N : ℝ)+1)/N := by push_cast; rfl
  have hb : ((2*(N : ℤ) : ℤ) : ℝ)/N = 2 := by push_cast; field_simp
  have h := norm_modelPhase_source_sub_buffered_le hNp hη F 1 ((N : ℤ)+1) (2*N)
  rw [ha,hb] at h
  have hk (n : ℤ) : modelPhaseWeightedKernel (sargosQuarticBufferedCutoff N η) F 1 N n =
      sargosQuarticWeightedKernel (sargosQuarticBufferedCutoff N η) N α γ n := by
    unfold modelPhaseWeightedKernel sargosQuarticWeightedKernel
    rw [he]
  simp only [sargosQuarticBufferedCutoff] at hk ⊢
  simpa only [he,hk] using h

end TaoTrudgianYang2025
