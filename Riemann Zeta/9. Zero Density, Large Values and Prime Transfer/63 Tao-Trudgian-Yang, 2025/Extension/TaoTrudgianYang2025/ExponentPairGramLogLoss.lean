import TaoTrudgianYang2025.ExponentPairGramBound
import TaoTrudgianYang2025.ZetaSourceLogScales

/-! Uniform logarithmic control of the actual reciprocal-gap Gram loss. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem harmonic_ceil_le_log_of_power_window {N T d : ℝ}
    (hN : 2 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 ≤ d)
    (hT : 0 < T) (hupper : T ≤ N^d) :
    (harmonic (Nat.ceil T) : ℝ) ≤ (d+2)*Real.log N := by
  have hNp : 0 < N := by linarith
  have hp : 1 ≤ N^d := Real.one_le_rpow (by linarith) hd
  have hc : (Nat.ceil T : ℝ) ≤ 2*N^d := by
    have hh := Nat.ceil_lt_add_one hT.le
    linarith
  have hc0 : (0 : ℝ) < Nat.ceil T := hT.trans_le (Nat.le_ceil T)
  have hl := Real.log_le_log hc0 hc
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
    Real.log_rpow hNp] at hl
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hh := harmonic_le_one_add_log (Nat.ceil T)
  nlinarith

theorem eventually_exponentPair_gram_diagonal {C τ η : ℝ}
    (hC : 1 ≤ C) (hτ : 0 ≤ τ) (hη : 0 < η) :
    ∀ᶠ N : ℝ in atTop, ∀ T : ℝ, 0 < T → T ≤ N^(τ+1) →
      4*N*(2*N+4*Real.pi*C*N*(harmonic (Nat.ceil T) : ℝ)) ≤ N^(2+η) := by
  have hC0 : 0 ≤ C := by linarith
  filter_upwards [eventually_const_log_pow_le_rpow (8+16*Real.pi*C*(τ+3))
    (by positivity) 1 hη,eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hsmall hN hlog
  intro T hT hupper
  have hNp : 0 < N := by linarith
  have hh : (harmonic (Nat.ceil T) : ℝ) ≤ (τ+3)*Real.log N := by
    simpa only [show τ+1+2=τ+3 by ring] using
      harmonic_ceil_le_log_of_power_window hN hlog (by linarith : 0 ≤ τ+1) hT hupper
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 16*Real.pi*C*N^2)
  have hn := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8*N^2)
  have hdiag : 4*N*(2*N+4*Real.pi*C*N*(harmonic (Nat.ceil T) : ℝ)) ≤
      N^2*((8+16*Real.pi*C*(τ+3))*Real.log N) := by nlinarith
  norm_num only [pow_one] at hsmall
  calc
    _ ≤ N^2*((8+16*Real.pi*C*(τ+3))*Real.log N) := hdiag
    _ ≤ N^2*N^η := mul_le_mul_of_nonneg_left hsmall (sq_nonneg N)
    _ = _ := by rw [Real.rpow_add hNp,Real.rpow_two]

end TaoTrudgianYang2025
