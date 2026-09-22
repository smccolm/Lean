import TaoTrudgianYang2025.BetaTwistedLogPhase

/-!
# Coherence of the original resonantly corrected logarithmic sum

Integer periodicity removes only the genuine linear term. The quadratic
remainder still has the actual physical factor T/N^2.
-/

noncomputable section

open Expdb
open scoped FourierTransform

namespace TaoTrudgianYang2025

theorem logPhase_physical_remainder {T N d : ℝ}
    (hT : 0 ≤ T) (hN : 0 < N) (hd : 0 ≤ d) :
    |T*Real.log ((N+d)/N)-T*d/N| ≤ T*d^2/N^2 := by
  calc
    |T*Real.log ((N+d)/N)-T*d/N| =
        |T/N| * |N*Real.log ((N+d)/N)-d| := by
      rw [← abs_mul]
      congr 1
      field_simp
    _ ≤ (T/N)*(d^2/N) := by
      rw [abs_of_nonneg (div_nonneg hT hN.le)]
      exact mul_le_mul_of_nonneg_left (logPhase_integer_remainder hN hd)
        (div_nonneg hT hN.le)
    _ = T*d^2/N^2 := by ring

theorem oscillatory_twistedLog_re_eq_cos_remainder
    {T N c : ℝ} (hN : N ≠ 0) (k j : ℕ)
    (hinteger : T*(1+c) = (k : ℝ)*N) :
    (oscillatory (twistedLogPhase c) T N (N+j)).re =
      Real.cos (2*Real.pi*(T*Real.log ((N+j)/N)-T*j/N)) := by
  have he : T*twistedLogPhase c ((N+j)/N)-((k*j : ℕ) : ℝ) =
      T*Real.log ((N+j)/N)-T*j/N := by
    simp only [twistedLogPhase,Nat.cast_mul]
    field_simp
    nlinarith [congrArg (fun z : ℝ => z*(j : ℝ)) hinteger]
  rw [← he,show 2*Real.pi*(T*twistedLogPhase c ((N+j)/N)-((k*j : ℕ) : ℝ)) =
    2*Real.pi*(T*twistedLogPhase c ((N+j)/N))-((k*j : ℕ) : ℝ)*(2*Real.pi) by ring,
    Real.cos_sub_nat_mul_two_pi]
  simp [oscillatory,Real.fourierChar_apply,Complex.exp_re]

theorem oscillatory_twistedLog_re_ge_half
    {T N c : ℝ} (hT : 0 ≤ T) (hN : 0 < N) (k j : ℕ)
    (hinteger : T*(1+c) = (k : ℝ)*N)
    (hsmall : T*(j : ℝ)^2/N^2 ≤ 1/16) :
    (1 : ℝ)/2 ≤ (oscillatory (twistedLogPhase c) T N (N+j)).re := by
  let e := T*Real.log ((N+j)/N)-T*j/N
  have he : |e| ≤ 1/16 :=
    (logPhase_physical_remainder hT hN (Nat.cast_nonneg j)).trans hsmall
  have hangle : |2*Real.pi*e| ≤ 1 := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hsq : (2*Real.pi*e)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 hangle
  rw [oscillatory_twistedLog_re_eq_cos_remainder hN.ne' k j hinteger]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*e)
  dsimp [e] at hc hsq
  linarith

end TaoTrudgianYang2025
