import TaoTrudgianYang2025.SargosDiagonalMoment
import TaoTrudgianYang2025.SargosCentralSixthMoment

/-! The actual base sixth moment has nonzero lower bound and the genuine trivial initial exponent. -/

noncomputable section

open MeasureTheory Set Filter

namespace TaoTrudgianYang2025

def sargosSixthBaseMoment (N : ℕ) : ℝ :=
  ∫ α in Icc (0 : ℝ) 1, ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
    ‖sargosQuarticSum N (fun _ => 1) α γ‖^6

theorem sargosSixthBaseMoment_nonneg (N : ℕ) : 0 ≤ sargosSixthBaseMoment N :=
  integral_nonneg (fun _α => integral_nonneg (fun _γ => pow_nonneg (norm_nonneg _) 6))

theorem sargosQuartic_central_sixth_le_base (N : ℕ) {A : ℝ} (hA : 0 ≤ A) (hA1 : A ≤ 1) :
    (∫ α in Icc (-A) A, ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
      ‖sargosQuarticSum N (fun _ => 1) α γ‖^6) ≤ 2*sargosSixthBaseMoment N := by
  apply (sargosQuartic_central_power_le_positive N 6 hA (by positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact setIntegral_mono_set
    (integrable_sargosQuarticNormPower_outer N 6 (fun _ => 1) 0 1 _ _)
    (Eventually.of_forall (fun α => integral_nonneg (fun γ => pow_nonneg (norm_nonneg _) 6)))
    (Icc_subset_Icc le_rfl hA1).eventuallyLE

theorem sargosSixthBaseMoment_lower {N : ℕ} (hN : 1 ≤ N) :
    (1/64 : ℝ) ≤ sargosSixthBaseMoment N := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h := sargosQuartic_central_even_moment_lower hN 3
    (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < 2/(N : ℝ)^3)
  have hwidth : (2/(N : ℝ)^3)/2 = 1/(N : ℝ)^3 := by ring
  have hscale : ((1 : ℝ)*(2/(N : ℝ)^3)/64)*(N : ℝ)^3 = 1/32 := by field_simp; norm_num
  rw [hwidth,hscale] at h
  have hu := sargosQuartic_central_sixth_le_base N
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  norm_num only [Nat.reduceMul] at h
  linarith

theorem sargosSixthBaseMoment_trivial {N : ℕ} (hN : 1 ≤ N) :
    sargosSixthBaseMoment N ≤ 2*(N : ℝ)^3 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB : 0 ≤ 1/(N : ℝ)^3 := by positivity
  have hn (α γ : ℝ) : ‖sargosQuarticSum N (fun _ => 1) α γ‖ ≤ (N : ℝ) := by
    rw [← sargosQuarticPrefix_full]
    exact (norm_sargosQuarticPrefix_le_maximum (fun _ => 1) α γ le_rfl).trans
      (sargosQuarticPrefixMaximum_unweighted_le N α γ)
  have hi : IntegrableOn (fun _α : ℝ =>
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3), (N : ℝ)^6) (Icc (0 : ℝ) 1) :=
    integrable_const _
  calc
    _ ≤ ∫ α in Icc (0 : ℝ) 1,
        ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3), (N : ℝ)^6 := by
      apply integral_mono (integrable_sargosQuarticNormPower_outer N 6 (fun _ => 1) 0 1 _ _) hi
      intro α
      apply integral_mono (integrable_sargosQuarticNormPower_inner N 6 (fun _ => 1) α _ _)
        (integrable_const _)
      intro γ
      exact pow_le_pow_left₀ (norm_nonneg _) (hn α γ) 6
    _ = _ := by
      simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,Real.volume_Icc,
        MeasureTheory.measureReal_def,sub_neg_eq_add,ENNReal.toReal_ofReal (by positivity : 0 ≤
          1/(N : ℝ)^3+1/(N : ℝ)^3)]
      norm_num
      field_simp
      ring

end TaoTrudgianYang2025
