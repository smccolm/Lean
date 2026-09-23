import TaoTrudgianYang2025.LargeValuePattern
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Literal phase variation on a short positive integer block. -/

namespace TaoTrudgianYang2025

theorem dirichletPhase_eq_exp {n : ℕ} (hn : 0 < n) (t : ℝ) :
    dirichletPhase n t = Complex.exp (Complex.I*((-t*Real.log (n:ℝ):ℝ):ℂ)) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n:ℂ) = (Real.log (n:ℝ):ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg n : (0:ℝ) ≤ n)).symm
  change (n:ℂ)^(-(Complex.I*(t:ℂ))) = _
  rw [Complex.cpow_def_of_ne_zero hn0,hlog]
  congr 1
  push_cast
  ring

theorem norm_exp_I_sub_exp_I_le (x y : ℝ) :
    ‖Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ))‖ ≤ |x-y| := by
  have heq : Complex.exp (Complex.I*(x:ℂ))-Complex.exp (Complex.I*(y:ℂ)) =
      Complex.exp (Complex.I*(y:ℂ))*
        (Complex.exp (Complex.I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,← Complex.exp_add,mul_one]
    congr 1
    congr 1
    push_cast
    ring
  rw [heq,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x-y))

theorem dirichletPhase_block_variation {a n : ℕ} (ha : 0 < a) (han : a ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖dirichletPhase n t-dirichletPhase a t‖ ≤ t*((n:ℝ)-(a:ℝ))/(a:ℝ) := by
  have hap : (0:ℝ) < a := by exact_mod_cast ha
  have hnp : (0:ℝ) < n := by exact_mod_cast (ha.trans_le han)
  have hanr : (a:ℝ) ≤ n := by exact_mod_cast han
  have hlog : Real.log (a:ℝ) ≤ Real.log (n:ℝ) := Real.log_le_log hap hanr
  have hlogUpper : Real.log (n:ℝ)-Real.log (a:ℝ) ≤ ((n:ℝ)-(a:ℝ))/(a:ℝ) := by
    calc
      _ = Real.log ((n:ℝ)/(a:ℝ)) := (Real.log_div hnp.ne' hap.ne').symm
      _ ≤ (n:ℝ)/(a:ℝ)-1 := Real.log_le_sub_one_of_pos (div_pos hnp hap)
      _ = _ := by field_simp
  rw [dirichletPhase_eq_exp (ha.trans_le han),dirichletPhase_eq_exp ha]
  calc
    _ ≤ |(-t*Real.log (n:ℝ))-(-t*Real.log (a:ℝ))| := norm_exp_I_sub_exp_I_le _ _
    _ = t*(Real.log (n:ℝ)-Real.log (a:ℝ)) := by
      rw [abs_of_nonpos (by nlinarith)]
      ring
    _ ≤ t*(((n:ℝ)-(a:ℝ))/(a:ℝ)) := mul_le_mul_of_nonneg_left hlogUpper ht
    _ = _ := by ring

end TaoTrudgianYang2025
