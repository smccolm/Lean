import TaoTrudgianYang2025.SargosQuarticPrefix

/-! Every completed Fourier mode is the original source sum with unit-modulus coefficients. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticTwist {N : ℕ} [NeZero N] (z : ℤ → ℂ) (k : ZMod N) (n : ℤ) : ℂ :=
  z n*ZMod.stdAddChar (-(sargosSourceResidue N n*k))

theorem norm_sargosQuarticTwist {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (k : ZMod N) (n : ℤ) :
    ‖sargosQuarticTwist z k n‖ = ‖z n‖ := by
  rw [sargosQuarticTwist,norm_mul,sargos_stdAddChar_norm,mul_one]

theorem sargosQuarticTwist_norm_le_one {N : ℕ} [NeZero N] {z : ℤ → ℂ}
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1) (k : ZMod N) :
    ∀ n ∈ sargosSourceInterval N, ‖sargosQuarticTwist z k n‖ ≤ 1 := by
  intro n hn
  rw [norm_sargosQuarticTwist]
  exact hz n hn

theorem sargosQuarticSample_dft {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α γ : ℝ) (k : ZMod N) :
    ZMod.dft (sargosQuarticSample (N := N) z α γ) k =
      sargosQuarticSum N (sargosQuarticTwist z k) α γ := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    _ = ∑ j : ZMod N, sargosQuarticTwist z k (sargosSourceLift j)*
        fordAdditiveCharacter ((sargosSourceLift j : ℝ)^2*α+
          (sargosSourceLift j : ℝ)^4*γ) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold sargosQuarticTwist sargosQuarticSample
      rw [sargosSourceResidue_lift]
      ring
    _ = ∑ n ∈ sargosSourceInterval N, sargosQuarticTwist z k n*
        fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ) :=
      sargos_sum_sourceLift (N := N) (fun n => sargosQuarticTwist z k n*
        fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ))
    _ = _ := rfl

theorem sargosQuartic_fourier_majorant_eq {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosFourierFourthMajorant (sargosQuarticSample (N := N) z α γ) =
      (∑ k : ZMod N, sargosPrefixMajorant k)^3*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4) := by
  unfold sargosFourierFourthMajorant
  simp_rw [sargosQuarticSample_dft]

end TaoTrudgianYang2025
