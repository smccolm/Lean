import TaoTrudgianYang2025.ZetaRealMomentEndpoint
import TaoTrudgianYang2025.ZetaGrowthExponent

/-!
# Actual real zeta moments supplied by a pointwise growth bound

This module integrates the actual zeta norm on positive-height intervals.
The real growth exponent may have either sign; no lower-bound hypothesis
on that exponent is inserted.
-/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem continuousOn_zeta_fixedLine_positive (c : ℝ) :
    ContinuousOn (fun t : ℝ => riemannZeta ((c : ℂ)+(t : ℂ)*I)) (Ioi 0) := by
  intro t ht
  have hne : (c : ℂ)+(t : ℂ)*I ≠ 1 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,
      mul_zero,add_zero,zero_add,one_im] at hi
    exact (ne_of_gt ht) hi
  exact ((differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun u : ℝ => (c : ℂ)+(u : ℂ)*I) (by fun_prop)).continuousWithinAt

theorem intervalIntegrable_zetaLineMoment_positive (c : ℝ) {p H : ℝ}
    (hp : 0 ≤ p) (hH : 0 < H) :
    IntervalIntegrable (fun t => zetaMomentLineNorm c t^p) volume H (2*H) := by
  have hc : ContinuousOn (zetaMomentLineNorm c) (Ioi 0) :=
    (continuousOn_zeta_fixedLine_positive c).norm
  apply ContinuousOn.intervalIntegrable
  apply (hc.rpow_const (fun _ _ => Or.inr hp)).mono
  intro t ht
  rw [Set.uIcc_of_le (by linarith : H ≤ 2*H)] at ht
  exact hH.trans_le ht.1

theorem rpow_le_dyadic_height_envelope {H t q : ℝ}
    (hH : 0 < H) (ht : t ∈ Icc H (2*H)) :
    t^q ≤ (2 : ℝ)^|q| * H^q := by
  by_cases hq : 0 ≤ q
  · calc
      _ ≤ (2*H)^q := Real.rpow_le_rpow (hH.le.trans ht.1) ht.2 hq
      _ = _ := by rw [Real.mul_rpow (by norm_num) hH.le,abs_of_nonneg hq]
  · have hq0 : q ≤ 0 := le_of_not_ge hq
    calc
      _ ≤ H^q := Real.rpow_le_rpow_of_nonpos hH ht.1 hq0
      _ ≤ (2 : ℝ)^|q| * H^q := by
        have hh := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (abs_nonneg q)
        nlinarith [Real.rpow_nonneg hH.le q]

theorem IsZetaGrowthBound.dyadic_realMoment {c m p : ℝ}
    (hGrowth : IsZetaGrowthBound c m) (hp : 1 ≤ p) :
    ∀ ε : ℝ, 0 < ε → ∃ D H₀ : ℝ, 0 ≤ D ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentLineNorm c t^p) ≤ D*H^(1+p*m+ε) := by
  intro ε hε
  have hpp : 0 < p := by linarith
  let η : ℝ := ε/(2*p)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C,hC,hbound⟩ := hGrowth η hη
  let q : ℝ := p*(m+η)
  let D : ℝ := C^p*(2 : ℝ)^|q|
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hq : q = p*m+ε/2 := by
    dsimp [q,η]
    field_simp
  refine ⟨D,C,hD,?_⟩
  intro H hHC hH
  have hHone : 1 ≤ H := hC.trans hHC
  have hpoint (t : ℝ) (ht : t ∈ Icc H (2*H)) :
      zetaMomentLineNorm c t^p ≤ D*H^q := by
    have htp : 0 < t := hH.trans_le ht.1
    have hg := hbound t (by rw [abs_of_pos htp]; exact hHC.trans ht.1)
    rw [abs_of_pos htp] at hg
    have hgPow := Real.rpow_le_rpow (norm_nonneg _) hg hpp.le
    rw [Real.mul_rpow hCp.le (Real.rpow_nonneg htp.le _),
      ← Real.rpow_mul htp.le] at hgPow
    change zetaMomentLineNorm c t^p ≤ C^p*t^((m+η)*p) at hgPow
    have heq : (m+η)*p = q := by dsimp [q]; ring
    rw [heq] at hgPow
    apply hgPow.trans
    have hh := mul_le_mul_of_nonneg_left
      (rpow_le_dyadic_height_envelope hH ht (q := q)) (Real.rpow_nonneg hCp.le p)
    simpa only [D,mul_assoc] using hh
  calc
    _ ≤ ∫ _t in H..2*H, D*H^q :=
      intervalIntegral.integral_mono_on (by linarith)
        (intervalIntegrable_zetaLineMoment_positive c hpp.le hH)
        (continuous_const.intervalIntegrable _ _) hpoint
    _ = D*H^(q+1) := by
      rw [intervalIntegral.integral_const,smul_eq_mul,Real.rpow_add_one hH.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hHone (by rw [hq]; linarith)) hD

end TaoTrudgianYang2025
