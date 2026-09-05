import GafniTao.Pintz2023MellinExp

/-!
# Pintz (2023), equation (3.5): the exact smoothing kernel

The difference `exp (-n/(2N)) - exp (-n/N)` is represented by two literal
inverse-Mellin integrals on `Re w = 2`.  No unspecified smoothing function is
introducedced.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

noncomputable def pintz2023MellinExpIntegrand (x t : ℝ) : ℂ :=
  (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)) *
    Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)

theorem integrable_pintz2023MellinExpIntegrand {x : ℝ} (hx : 0 < x) :
    Integrable (pintz2023MellinExpIntegrand x) := by
  have hMajorant : Integrable (fun t : ℝ =>
      x ^ (-(2 : ℝ)) *
        ‖Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
    integrable_pintz2023_Gamma_two_vertical.norm.const_mul _
  apply hMajorant.mono'
  · have hpow : Continuous (fun t : ℝ =>
        (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (t : ℂ) * I))) := by
      exact Continuous.cpow continuous_const (by fun_prop)
        (fun _ => Complex.ofReal_mem_slitPlane.mpr hx)
    exact (hpow.mul
      continuous_pintz2023_Gamma_two_vertical).aestronglyMeasurable
  · filter_upwards with t
    unfold pintz2023MellinExpIntegrand
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre :
        (-(((2 : ℝ) : ℂ) + (t : ℂ) * I)).re = -(2 : ℝ) := by simp
    rw [hre]

theorem pintz2023_inverseMellin_exp_neg_integrand {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, pintz2023MellinExpIntegrand x t) =
      Real.exp (-x) := by
  simpa [pintz2023MellinExpIntegrand] using
    pintz2023_inverseMellin_exp_neg hx

noncomputable def pintz2023MellinKernelIntegrand
    (N n : ℕ) (t : ℝ) : ℂ :=
  pintz2023MellinExpIntegrand ((n : ℝ) / (2 * N)) t -
    pintz2023MellinExpIntegrand ((n : ℝ) / N) t

/-- Exact inverse-Mellin formula for the kernel in Pintz (3.5). -/
theorem pintz2023HalaszKernel_eq_mellin
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    ((pintz2023HalaszKernel N n : ℝ) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t : ℝ, pintz2023MellinKernelIntegrand N n t) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hxTwo : 0 < (n : ℝ) / (2 * N) := by positivity
  have hxOne : 0 < (n : ℝ) / N := by positivity
  have hTwo := pintz2023_inverseMellin_exp_neg_integrand hxTwo
  have hOne := pintz2023_inverseMellin_exp_neg_integrand hxOne
  have hIntTwo := integrable_pintz2023MellinExpIntegrand hxTwo
  have hIntOne := integrable_pintz2023MellinExpIntegrand hxOne
  unfold pintz2023MellinKernelIntegrand
  rw [MeasureTheory.integral_sub hIntTwo hIntOne, mul_sub]
  rw [hTwo, hOne]
  unfold pintz2023HalaszKernel
  push_cast
  congr 1 <;> ring_nf

#print axioms integrable_pintz2023MellinExpIntegrand
#print axioms pintz2023HalaszKernel_eq_mellin

end

end GafniTao
