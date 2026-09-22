import TaoTrudgianYang2025.BetaTaylorAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact integral remainder for the quadratic stationary deficit

A direct fundamental-theorem-of-calculus argument supplies the
weighted second-derivative average, including the zero-length segment.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem segmentTaylorAverage_zero_eq_intervalIntegral (f : ℝ → ℝ) (a x : ℝ) :
    segmentTaylorAverage f a 0 x =
      ∫ t in (0 : ℝ)..1, (1-t)*f (a+t*(x-a)) := by
  simp only [segmentTaylorAverage,pow_zero,mul_one,iteratedDeriv_zero,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

theorem segmentTaylorAverage_at_center (f : ℝ → ℝ) (a : ℝ) :
    segmentTaylorAverage f a 0 a = f a/2 := by
  rw [segmentTaylorAverage_zero_eq_intervalIntegral]
  simp only [sub_self,mul_zero,add_zero]
  have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub intervalIntegrable_const hid]
  norm_num [integral_id]
  ring

theorem segmentTaylorAverage_second
    {F : ℝ → ℝ} {l r a x : ℝ}
    (hF : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ F u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) :
    (x-a)^2*segmentTaylorAverage (deriv (deriv F)) a 0 x =
      F x-F a-(x-a)*deriv F a := by
  let p : ℝ → ℝ := fun t => F (a+t*(x-a))+(1-t)*(x-a)*deriv F (a+t*(x-a))
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt p ((x-a)^2*((1-t)*deriv (deriv F) (a+t*(x-a)))) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hc := hF _ (affineSegment_mem_Ioo ha hx ht')
    have h₁ := hc.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have h₂ := (hc.derivWithin (by simp)).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hg : HasDerivAt (fun t : ℝ => a+t*(x-a)) (x-a) t := by
      simpa only [one_mul] using ((hasDerivAt_id t).mul_const (x-a)).const_add a
    have hw := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (x-a)
    have h := (h₁.hasDerivAt.comp t hg).add (hw.mul (h₂.hasDerivAt.comp t hg))
    convert h using 1
    dsimp [p]
    ring
  have hjet : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ (deriv (deriv F)) u := by
    intro u hu
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (hF u hu) 2
  have hi := segmentTaylorAverage_integrable hjet ha hx 0
  simp only [pow_zero,mul_one,iteratedDeriv_zero] at hi
  have hint : IntervalIntegrable
      (fun t : ℝ => (x-a)^2*((1-t)*deriv (deriv F) (a+t*(x-a)))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hi.const_mul _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_const_mul,
    ← segmentTaylorAverage_zero_eq_intervalIntegral] at h
  simpa only [p,one_mul,zero_mul,sub_zero,sub_self,zero_add,add_zero,
    add_sub_cancel,sub_add_cancel,sub_add_eq_sub_sub] using h

end TaoTrudgianYang2025
