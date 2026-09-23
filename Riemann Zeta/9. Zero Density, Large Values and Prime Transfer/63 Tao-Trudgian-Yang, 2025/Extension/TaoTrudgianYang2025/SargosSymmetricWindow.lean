import TaoTrudgianYang2025.SargosPowerRegularity
import TaoTrudgianYang2025.SargosQuarticMaximalMoment

/-! Exact sign symmetry of the literal quartic sum and central-to-positive windows. -/

noncomputable section

open MeasureTheory Set Filter GafniTao
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosQuarticSum_unweighted_neg (N : ℕ) (α γ : ℝ) :
    sargosQuarticSum N (fun _ => 1) (-α) (-γ) =
      conj (sargosQuarticSum N (fun _ => 1) α γ) := by
  unfold sargosQuarticSum sargosPlanarSum
  rw [map_sum]
  simp only [one_mul,conj_fordAdditiveCharacter]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  ring

theorem sargosQuarticSum_unweighted_norm_neg (N : ℕ) (α γ : ℝ) :
    ‖sargosQuarticSum N (fun _ => 1) (-α) (-γ)‖ =
      ‖sargosQuarticSum N (fun _ => 1) α γ‖ := by
  rw [sargosQuarticSum_unweighted_neg,Complex.norm_conj]

theorem sargos_setIntegral_Icc_comp_neg (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b, f (-x)) = ∫ x in Icc (-b) (-a), f x := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_neg,intervalIntegral.integral_of_le (neg_le_neg hab),
    ← integral_Icc_eq_integral_Ioc]

theorem sargosQuartic_inner_power_neg (N p : ℕ) (α : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    (∫ γ in Icc (-B) B, ‖sargosQuarticSum N (fun _ => 1) (-α) γ‖^p) =
      ∫ γ in Icc (-B) B, ‖sargosQuarticSum N (fun _ => 1) α γ‖^p := by
  have h := sargos_setIntegral_Icc_comp_neg
    (fun γ => ‖sargosQuarticSum N (fun _ => 1) (-α) γ‖^p) (-B) B (by linarith)
  simp_rw [sargosQuarticSum_unweighted_norm_neg] at h
  simpa only [neg_neg] using h.symm

theorem sargosQuartic_central_power_le_positive (N p : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ α in Icc (-A) A, ∫ γ in Icc (-B) B,
      ‖sargosQuarticSum N (fun _ => 1) α γ‖^p) ≤
      2*(∫ α in Icc (0 : ℝ) A, ∫ γ in Icc (-B) B,
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^p) := by
  let F : ℝ → ℝ := fun α => ∫ γ in Icc (-B) B, ‖sargosQuarticSum N (fun _ => 1) α γ‖^p
  have hn (α : ℝ) : 0 ≤ F α := integral_nonneg (fun γ => pow_nonneg (norm_nonneg _) p)
  have hs : IntegrableOn F (Icc (-A) 0) :=
    integrable_sargosQuarticNormPower_outer N p (fun _ => 1) (-A) 0 (-B) B
  have ht : IntegrableOn F (Icc 0 A) :=
    integrable_sargosQuarticNormPower_outer N p (fun _ => 1) 0 A (-B) B
  have hcover : Icc (-A) A ⊆ Icc (-A) 0 ∪ Icc 0 A := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · exact Or.inl ⟨hx.1,hx0⟩
    · exact Or.inr ⟨(lt_of_not_ge hx0).le,hx.2⟩
  have hμ : volume.restrict (Icc (-A) A) ≤
      volume.restrict (Icc (-A) 0)+volume.restrict (Icc 0 A) :=
    (Measure.restrict_mono hcover le_rfl).trans (Measure.restrict_union_le _ _)
  have h := integral_mono_measure hμ (Eventually.of_forall hn)
    (integrable_add_measure.mpr ⟨hs,ht⟩)
  rw [integral_add_measure hs ht] at h
  have hr := sargos_setIntegral_Icc_comp_neg F 0 A hA
  have he (x : ℝ) : F (-x) = F x := sargosQuartic_inner_power_neg N p x hB
  simp_rw [he,neg_zero] at hr
  change (∫ α in Icc (-A) A, F α) ≤ 2*(∫ α in Icc (0 : ℝ) A, F α)
  rw [← hr] at h
  linarith

theorem sargosQuartic_fixed_power_le_maximal (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    (∫ α in Icc a b, ∫ γ in Icc c d, ‖sargosQuarticSum N z α γ‖^p) ≤
      ∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^p := by
  apply integral_mono (integrable_sargosQuarticNormPower_outer N p z a b c d)
    (integrable_sargosQuarticMaximumPower_outer N p z a b c d)
  intro α
  apply integral_mono (integrable_sargosQuarticNormPower_inner N p z α c d)
    (integrable_sargosQuarticMaximumPower_inner N p z α c d)
  intro γ
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [← sargosQuarticPrefix_full]
  exact norm_sargosQuarticPrefix_le_maximum z α γ le_rfl

end TaoTrudgianYang2025

