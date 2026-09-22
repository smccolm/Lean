import TaoTrudgianYang2025.BetaQuadraticKernel

/-!
# Integration by parts for a quadratic Taylor remainder

A factor z squared removes the stationary singularity. The estimate uses
the actual smooth coefficient and its derivative, with no omitted endpoint.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem norm_integral_sq_mul_betaQuadraticKernel_le
    {V : ℝ → ℝ} {T H M L : ℝ}
    (hV : ContDiff ℝ ∞ V) (hT : 0 < T) (hH : 0 < H)
    (hb : ∀ z : ℝ, |V z| ≤ M) (hd : ∀ z : ℝ, |deriv V z| ≤ L) :
    ‖∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z‖ ≤
      (2*H*M+2*H*(M+H*L))/(2*Real.pi*T) := by
  let c : ℂ := ((-2*Real.pi*T : ℝ) : ℂ)*Complex.I
  let U : ℝ → ℂ := fun z => ((z*V z : ℝ) : ℂ)
  let U' : ℝ → ℂ := fun z => ((V z+z*deriv V z : ℝ) : ℂ)
  have hDV : Continuous (deriv V) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      hV.continuous_iteratedDeriv 1 (by simp)
  have hU : ∀ z : ℝ, HasDerivAt U (U' z) z := by
    intro z
    have h := ((hasDerivAt_id z).mul
      (hV.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0) z).hasDerivAt).ofReal_comp
    simpa only [id_eq,one_mul] using h
  have hK : ∀ z : ℝ, HasDerivAt (betaQuadraticKernel T)
      (c*(z : ℂ)*betaQuadraticKernel T z) z := by
    intro z
    convert betaQuadraticKernel_hasDerivAt T z using 1
    dsimp [c]
    push_cast
    ring
  have hUc : Continuous U' := Complex.continuous_ofReal.comp
    (hV.continuous.add (continuous_id.mul hDV))
  have hKc : Continuous (fun z : ℝ => c*(z : ℂ)*betaQuadraticKernel T z) :=
    (continuous_const.mul Complex.continuous_ofReal).mul (continuous_betaQuadraticKernel T)
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (u' := U') (v := betaQuadraticKernel T)
    (v' := fun z : ℝ => c*(z : ℂ)*betaQuadraticKernel T z)
    (fun z _ => hU z) (fun z _ => hK z)
    (hUc.intervalIntegrable (-H) H) (hKc.intervalIntegrable (-H) H)
  have he : c*(∫ z in (-H)..H, ((z^2*V z : ℝ) : ℂ)*betaQuadraticKernel T z) =
      U H*betaQuadraticKernel T H-U (-H)*betaQuadraticKernel T (-H)-
        ∫ z in (-H)..H, U' z*betaQuadraticKernel T z := by
    rw [← hp,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _
    dsimp [U]
    push_cast
    ring
  have hden : 0 < 2*Real.pi*T := mul_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have hc : ‖c‖ = 2*Real.pi*T := by
    dsimp only [c]
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_neg (by nlinarith : -2*Real.pi*T < 0)]
    ring
  have hUb : ∀ z : ℝ, |z| ≤ H → ‖U z*betaQuadraticKernel T z‖ ≤ H*M := by
    intro z hz
    rw [norm_mul,norm_betaQuadraticKernel,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hz (hb z) (abs_nonneg _) hH.le
  have hIb : ‖∫ z in (-H)..H, U' z*betaQuadraticKernel T z‖ ≤ 2*H*(M+H*L) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -H) (b := H) (f := fun z : ℝ => U' z*betaQuadraticKernel T z) (C := M+H*L) (fun z hz => by
        have hz' : |z| ≤ H := by
          rw [uIoc_of_le (by linarith : -H ≤ H)] at hz
          exact abs_le.mpr ⟨hz.1.le,hz.2⟩
        rw [norm_mul,norm_betaQuadraticKernel,mul_one,Complex.norm_real,Real.norm_eq_abs]
        exact (abs_add_le (V z) (z*deriv V z)).trans
          (add_le_add (hb z) (by
            rw [abs_mul]
            exact mul_le_mul hz' (hd z) (abs_nonneg _) hH.le)))
    apply hbound.trans_eq
    rw [abs_of_nonneg (by linarith : 0 ≤ H- -H)]
    ring
  apply (le_div_iff₀ hden).mpr
  rw [mul_comm,← hc,← norm_mul,he]
  have hnorm := (norm_sub_le
    (U H*betaQuadraticKernel T H-U (-H)*betaQuadraticKernel T (-H))
    (∫ z in (-H)..H, U' z*betaQuadraticKernel T z)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  have hright := hUb H (by rw [abs_of_pos hH])
  have hleft := hUb (-H) (by rw [abs_neg,abs_of_pos hH])
  linarith

end TaoTrudgianYang2025
