import TaoTrudgianYang2025.BetaClosedDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Elementary logarithmic-phase coherence at the physical scale T=N.
The integer linear term is removed by cosine periodicity, not by changing
the model phase or its defining exponential sum. -/

noncomputable section

open Expdb
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem log_one_add_quadratic_remainder {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x-Real.log (1+x) ∧ x-Real.log (1+x) ≤ x^2 := by
  have hp : 0 < 1+x := by linarith
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  constructor
  · linarith
  · calc
      x-Real.log (1+x) ≤ x-(1-(1+x)⁻¹) := by linarith
      _ = x^2/(1+x) := by field_simp; ring
      _ ≤ x^2 := div_le_self (sq_nonneg x) (by linarith)

theorem logPhase_integer_remainder {N d : ℝ}
    (hN : 0 < N) (hd : 0 ≤ d) :
    |N*Real.log ((N+d)/N)-d| ≤ d^2/N := by
  have hx := log_one_add_quadratic_remainder (div_nonneg hd hN.le)
  have hratio : (N+d)/N = 1+d/N := by field_simp
  rw [hratio]
  have hlin : N*(d/N) = d := by field_simp
  have hnonpos : N*Real.log (1+d/N)-d ≤ 0 := by
    have h := mul_nonneg hN.le hx.1
    nlinarith
  rw [abs_of_nonpos hnonpos]
  calc
    -(N*Real.log (1+d/N)-d) = N*(d/N-Real.log (1+d/N)) := by
      nlinarith
    _ ≤ N*(d/N)^2 := mul_le_mul_of_nonneg_left hx.2 hN.le
    _ = d^2/N := by field_simp

theorem oscillatory_log_re_eq_cos_remainder (N : ℝ) (j : ℕ) :
    (oscillatory Real.log N N (N+j)).re =
      Real.cos (2*Real.pi*(N*Real.log ((N+j)/N)-j)) := by
  rw [show 2*Real.pi*(N*Real.log ((N+j)/N)-j) =
    2*Real.pi*(N*Real.log ((N+j)/N))-(j : ℝ)*(2*Real.pi) by ring,
    Real.cos_sub_nat_mul_two_pi]
  simp [oscillatory,Real.fourierChar_apply,Complex.exp_re]

theorem oscillatory_log_re_ge_half {N : ℝ} (hN : 0 < N) (j : ℕ)
    (hsmall : (j : ℝ)^2/N ≤ 1/16) :
    (1 : ℝ)/2 ≤ (oscillatory Real.log N N (N+j)).re := by
  let e := N*Real.log ((N+j)/N)-(j : ℝ)
  have he : |e| ≤ 1/16 :=
    (logPhase_integer_remainder hN (Nat.cast_nonneg j)).trans hsmall
  have hangle : |2*Real.pi*e| ≤ 1 := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hsq : (2*Real.pi*e)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 hangle
  rw [oscillatory_log_re_eq_cos_remainder]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*e)
  dsimp [e] at hc hsq
  linarith

end TaoTrudgianYang2025
