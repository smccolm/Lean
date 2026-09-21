import TaoTrudgianYang2025.FresnelGaussianComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Abel limit and quantitative Fresnel truncation

The zero-damping limit is taken on each finite interval. A damping-uniform
oscillatory tail identifies the limiting Gaussian value; no whole-line
Lebesgue integral at zero damping is asserted.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace TaoTrudgianYang2025

def fresnelGaussianValue (c : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (2 * Real.pi * c * I)) ^ (1 / 2 : ℂ)

theorem fresnelGaussianBase {c : ℝ} (hc : 0 < c) :
    (Real.pi : ℂ) / (2 * Real.pi * c * I) = -I / ((2 * c : ℝ) : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  simp [Complex.I_sq]

theorem continuousAt_fresnelGaussianValue_damping {c : ℝ} (hc : 0 < c) :
    ContinuousAt (fun ε : ℝ =>
      ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ)) 0 := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : ((0 : ℝ) : ℂ) + 2 * Real.pi * c * I ≠ 0 := by
    simpa only [Complex.ofReal_zero, zero_add] using
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hpiC) hcC) I_ne_zero
  have hbase : (Real.pi : ℂ) / (2 * Real.pi * c * I) ∈ slitPlane := by
    rw [fresnelGaussianBase hc]
    apply Or.inr
    rw [Complex.div_ofReal_im, Complex.neg_im, Complex.I_im]
    exact div_ne_zero (by norm_num) (by positivity)
  have hquot : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) /
      ((ε : ℂ) + 2 * Real.pi * c * I)) 0 :=
    continuousAt_const.div (Complex.continuous_ofReal.continuousAt.add continuousAt_const) hden
  have hbase' : (Real.pi : ℂ) / (((0 : ℝ) : ℂ) + 2 * Real.pi * c * I) ∈ slitPlane := by
    simpa only [Complex.ofReal_zero, zero_add] using hbase
  exact (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hbase').comp
    (f := fun ε : ℝ => (Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) hquot

theorem fresnelDampedKernel_zero (c x : ℝ) :
    fresnelDampedKernel 0 c x = Complex.exp (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * I) := by
  unfold fresnelDampedKernel
  congr 1
  push_cast
  ring

theorem continuous_fresnelDampedWindow (c H : ℝ) :
    Continuous (fun ε : ℝ => ∫ x in (-H)..H, fresnelDampedKernel ε c x) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry fresnelDampedKernel
  fun_prop

theorem norm_atkinsonQuadraticWindow_sub_gaussianValue_le {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    ‖atkinsonQuadraticWindow c H - fresnelGaussianValue c‖ ≤ 2 / (c * H * Real.pi) := by
  have hG : Tendsto (fun ε : ℝ =>
      ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (fresnelGaussianValue c)) := by
    simpa only [Complex.ofReal_zero, zero_add, fresnelGaussianValue] using
      (continuousAt_fresnelGaussianValue_damping hc).tendsto.mono_left nhdsWithin_le_nhds
  have hW : Tendsto (fun ε : ℝ => ∫ x in (-H)..H, fresnelDampedKernel ε c x)
      (𝓝[>] (0 : ℝ)) (𝓝 (atkinsonQuadraticWindow c H)) := by
    have h := (continuous_fresnelDampedWindow c H).continuousAt
      (x := (0 : ℝ)) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa only [fresnelDampedKernel_zero, atkinsonQuadraticWindow] using h
  rw [norm_sub_rev]
  apply le_of_tendsto (hG.sub hW).norm
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_gaussianValue_sub_fresnelDampedWindow_le hε hc hH

end TaoTrudgianYang2025
