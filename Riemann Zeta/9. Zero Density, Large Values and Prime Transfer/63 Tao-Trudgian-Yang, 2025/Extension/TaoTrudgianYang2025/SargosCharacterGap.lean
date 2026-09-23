import TaoTrudgianYang2025.SargosFiniteFourier
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit unit-circle gaps for the finite Fourier prefix kernels. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargos_sin_pi_lower {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    2*min t (1-t) ≤ Real.sin (Real.pi*t) := by
  by_cases hh : t ≤ 1/2
  · rw [min_eq_left (by linarith)]
    have hs := Real.le_sin_mul (x := 2*t) (by linarith) (by linarith)
    convert hs using 1
    congr 1
    ring
  · rw [min_eq_right (by linarith)]
    have hs := Real.le_sin_mul (x := 2*(1-t)) (by linarith) (by linarith)
    have he : Real.pi/2*(2*(1-t)) = Real.pi-Real.pi*t := by ring
    rw [he,Real.sin_pi_sub] at hs
    exact hs

theorem sargos_stdAddChar_sub_one_norm {N : ℕ} [NeZero N] (k : ZMod N) :
    ‖ZMod.stdAddChar k-1‖ = 2*|Real.sin (Real.pi*(k.val : ℝ)/(N : ℝ))| := by
  have he : ZMod.stdAddChar k =
      Complex.exp (Complex.I*((2*Real.pi*(k.val : ℝ)/(N : ℝ) : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [he,Complex.norm_exp_I_mul_ofReal_sub_one]
  have he' : (2*Real.pi*(k.val : ℝ)/(N : ℝ))/2 =
      Real.pi*(k.val : ℝ)/(N : ℝ) := by ring
  rw [he',Real.norm_eq_abs,abs_mul]
  norm_num

end TaoTrudgianYang2025
