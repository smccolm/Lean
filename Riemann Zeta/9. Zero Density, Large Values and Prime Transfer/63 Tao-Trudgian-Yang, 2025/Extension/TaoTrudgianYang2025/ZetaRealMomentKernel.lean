import TaoTrudgianYang2025.ZetaMomentTransfer

/-!
# Weighted real-power moments for the separated zeta kernel

The exponent is any real p >= 1, including p=1. The proof integrates
Young's inequality at the actual weighted mean. It does not assume a
bound for zeta or for the cardinality of an ordinate set.
-/

noncomputable section
open Finset MeasureTheory Set
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem realMoment_tangent_bound {p a x : ℝ} (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    p * a ^ (p-1) * x ≤ x ^ p + (p-1) * a ^ p := by
  rcases eq_or_lt_of_le hp with he | hp'
  · subst p
    simp
  have hpq : p.HolderConjugate (p/(p-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp').mpr rfl
  have h := Real.young_inequality_of_nonneg hx (Real.rpow_nonneg ha (p-1)) hpq
  have hpow : (a ^ (p-1)) ^ (p/(p-1)) = a ^ p := by
    rw [← Real.rpow_mul ha, hpq.sub_one_mul_conj]
  rw [hpow] at h
  have hm := mul_le_mul_of_nonneg_left h hpq.pos.le
  have hright : p * (x ^ p / p + a ^ p / (p/(p-1))) =
      x ^ p + (p-1) * a ^ p := by
    field_simp [hpq.ne_zero, hpq.sub_one_ne_zero]
  rw [hright] at hm
  nlinarith

theorem integral_weighted_realMoment
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    {p : ℝ} (hp : 1 ≤ p)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hwInt : Integrable w μ) (hwfInt : Integrable (fun x => w x * f x) μ)
    (hwfPowInt : Integrable (fun x => w x * f x ^ p) μ)
    (hMass : 0 < ∫ x, w x ∂μ) :
    (∫ x, w x * f x ∂μ) ^ p ≤
      (∫ x, w x ∂μ) ^ (p-1) * ∫ x, w x * f x ^ p ∂μ := by
  let a : ℝ := (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ)
  have ha : 0 ≤ a := div_nonneg (integral_nonneg fun x => mul_nonneg (hw x) (hf x)) hMass.le
  have hmean : a * (∫ x, w x ∂μ) = ∫ x, w x * f x ∂μ := div_mul_cancel₀ _ hMass.ne'
  have hpow : a ^ (p-1) * a = a ^ p := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one' ha (show p-1+1 ≠ 0 by linarith)).symm
  have hpoint (x : α) :
      (p*a^(p-1))*(w x*f x) ≤ w x*f x^p + ((p-1)*a^p)*w x := by
    have hh := mul_le_mul_of_nonneg_left (realMoment_tangent_bound hp ha (hf x)) (hw x)
    nlinarith
  have hInt := integral_mono (hwfInt.const_mul (p*a^(p-1)))
    (hwfPowInt.add (hwInt.const_mul ((p-1)*a^p))) hpoint
  dsimp only [Pi.add_apply] at hInt
  rw [integral_add hwfPowInt (hwInt.const_mul _), integral_const_mul, integral_const_mul] at hInt
  have hsmall : a^p * (∫ x, w x ∂μ) ≤ ∫ x, w x*f x^p ∂μ := by
    rw [← hmean] at hInt
    have heq : p*a^(p-1)*(a*(∫ x, w x ∂μ)) = p*a^p*(∫ x, w x ∂μ) := by
      calc
        _ = p*(a^(p-1)*a)*(∫ x, w x ∂μ) := by ring
        _ = _ := by rw [hpow]
    rw [heq] at hInt
    nlinarith
  calc
    _ = (∫ x, w x ∂μ)^(p-1) * (a^p*(∫ x, w x ∂μ)) := by
      rw [← hmean, Real.mul_rpow ha hMass.le]
      have hh : (∫ x, w x ∂μ)^p =
          (∫ x, w x ∂μ)^(p-1)*(∫ x, w x ∂μ) := by
        simpa only [sub_add_cancel] using Real.rpow_add_one hMass.ne' (p-1)
      rw [hh]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hMass.le _)

theorem sum_convolution_realMoment_le_moment
    {T p : ℝ} (W : Finset ℝ) (hT : 0 < T) (hp : 1 ≤ p)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hW : ∀ t ∈ W, t ∈ Set.Icc T (2*T))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∑ t ∈ W, (∫ u in T/2..3*T, zetaMomentKernel t u*f u)^p) ≤
      zetaMomentLogLoss T^p * ∫ u in T/2..3*T, f u^p := by
  have hab : T/2 ≤ 3*T := by linarith
  have hfp : Continuous (fun u => f u^p) :=
    hf.rpow_const (fun _ => Or.inr (by linarith))
  have hweighted (t : ℝ) : Continuous (fun u => zetaMomentKernel t u*f u^p) :=
    (continuous_zetaMomentKernel t).mul hfp
  have hJensen (t : ℝ) (ht : t ∈ W) :
      (∫ u in T/2..3*T, zetaMomentKernel t u*f u)^p ≤
        zetaMomentLogLoss T^(p-1) * ∫ u in T/2..3*T, zetaMomentKernel t u*f u^p := by
    obtain ⟨hmass, hmassBound⟩ := integral_zetaMomentKernel_source_mass hT (hW t ht)
    have hraw := integral_weighted_realMoment
      (μ := volume.restrict (Set.Ioc (T/2) (3*T))) hp
      (fun u => (zetaMomentKernel_pos t u).le) hf0
      ((continuous_zetaMomentKernel t).intervalIntegrable (T/2) (3*T)).1
      (((continuous_zetaMomentKernel t).mul hf).intervalIntegrable (T/2) (3*T)).1
      ((hweighted t).intervalIntegrable (T/2) (3*T)).1
      (by simpa only [intervalIntegral.integral_of_le hab] using hmass)
    have hraw' :
        (∫ u in T/2..3*T, zetaMomentKernel t u*f u)^p ≤
          (∫ u in T/2..3*T, zetaMomentKernel t u)^(p-1) *
            ∫ u in T/2..3*T, zetaMomentKernel t u*f u^p := by
      simpa only [intervalIntegral.integral_of_le hab] using hraw
    apply hraw'.trans
    apply mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hmass.le hmassBound (by linarith))
    exact intervalIntegral.integral_nonneg hab fun u _ =>
      mul_nonneg (zetaMomentKernel_pos t u).le (Real.rpow_nonneg (hf0 u) p)
  have hsum : (∑ t ∈ W, ∫ u in T/2..3*T, zetaMomentKernel t u*f u^p) ≤
      zetaMomentLogLoss T * ∫ u in T/2..3*T, f u^p := by
    rw [← intervalIntegral.integral_finsetSum (fun t ht =>
      (hweighted t).intervalIntegrable (T/2) (3*T)),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_finsetSum W fun t ht => hweighted t).intervalIntegrable (T/2) (3*T))
      ((hfp.const_mul _).intervalIntegrable (T/2) (3*T))
    intro u hu
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_zetaMomentKernel_on_source_window W hT hSep hW hu)
      (Real.rpow_nonneg (hf0 u) p)
  calc
    _ ≤ ∑ t ∈ W, zetaMomentLogLoss T^(p-1) *
        ∫ u in T/2..3*T, zetaMomentKernel t u*f u^p :=
      Finset.sum_le_sum hJensen
    _ = zetaMomentLogLoss T^(p-1) *
        ∑ t ∈ W, ∫ u in T/2..3*T, zetaMomentKernel t u*f u^p :=
      (Finset.mul_sum ..).symm
    _ ≤ zetaMomentLogLoss T^(p-1) *
        (zetaMomentLogLoss T * ∫ u in T/2..3*T, f u^p) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (zetaMomentLogLoss_pos T).le _)
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add_one (zetaMomentLogLoss_pos T).ne', sub_add_cancel]

end TaoTrudgianYang2025

