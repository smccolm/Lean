import TaoTrudgianYang2025.SargosUnweightedPowers

/-! Exact rectangle comparison and a two-window split for the sixth moment. -/

noncomputable section

open MeasureTheory Set Filter

namespace TaoTrudgianYang2025

theorem sargos_integral_Icc_split_le (f : ℝ → ℝ) (A B : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hs : IntegrableOn f (Icc 0 B))
    (ht : IntegrableOn f (Icc B A)) :
    (∫ x in Icc 0 A, f x) ≤ (∫ x in Icc 0 B, f x)+(∫ x in Icc B A, f x) := by
  have hcover : Icc (0 : ℝ) A ⊆ Icc 0 B ∪ Icc B A := by
    intro x hx
    by_cases hb : x ≤ B
    · exact Or.inl ⟨hx.1,hb⟩
    · exact Or.inr ⟨(lt_of_not_ge hb).le,hx.2⟩
  have hμ : volume.restrict (Icc (0 : ℝ) A) ≤
      volume.restrict (Icc 0 B)+volume.restrict (Icc B A) :=
    (Measure.restrict_mono hcover le_rfl).trans (Measure.restrict_union_le _ _)
  have h := integral_mono_measure hμ (Eventually.of_forall hf)
    (integrable_add_measure.mpr ⟨hs,ht⟩)
  rwa [integral_add_measure hs ht] at h

theorem sargosQuartic_sixth_rectangle_le_of_sq_bound (N : ℕ)
    (a b c d B : ℝ)
    (hB : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d,
      (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^2 ≤ B) :
    (∫ α in Icc a b, ∫ γ in Icc c d,
      (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
    B*(∫ α in Icc a b, ∫ γ in Icc c d,
      (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^4) := by
  have h6 := integrable_sargosQuarticUnweightedPower_rectangle N 6 a b c d
  have h4 := integrable_sargosQuarticUnweightedPower_rectangle N 4 a b c d
  calc
    _ = ∫ p : ℝ × ℝ, (sargosQuarticPrefixMaximum N (fun _ => 1) p.1 p.2)^6
        ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) :=
      (integral_prod _ h6).symm
    _ ≤ ∫ p : ℝ × ℝ, B*(sargosQuarticPrefixMaximum N (fun _ => 1) p.1 p.2)^4
        ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
      apply integral_mono_ae h6 (h4.const_mul B)
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      calc
        _ = (sargosQuarticPrefixMaximum N (fun _ => 1) p.1 p.2)^2*
            (sargosQuarticPrefixMaximum N (fun _ => 1) p.1 p.2)^4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hB p.1 hp.1 p.2 hp.2) (by positivity)
    _ = _ := by rw [integral_const_mul,integral_prod _ h4]

theorem sargosQuartic_sixth_rectangle_le_trivial (N : ℕ) (a b c d : ℝ) :
    (∫ α in Icc a b, ∫ γ in Icc c d,
      (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
    (N : ℝ)^2*(∫ α in Icc a b, ∫ γ in Icc c d,
      (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^4) := by
  apply sargosQuartic_sixth_rectangle_le_of_sq_bound
  intro α hα γ hγ
  exact pow_le_pow_left₀ (sargosQuarticPrefixMaximum_nonneg N (fun _ => 1) α γ)
    (sargosQuarticPrefixMaximum_unweighted_le N α γ) 2

theorem sargosQuartic_sixth_rectangle_le_curvature {N : ℕ} (hN : 1 ≤ N)
    {A : ℝ} (hA : A ≤ 1) :
    (∫ α in Icc (128/(N : ℝ)) A,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) ≤
    (4096*(N : ℝ)^2*A)*(∫ α in Icc (128/(N : ℝ)) A,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^4) := by
  apply sargosQuartic_sixth_rectangle_le_of_sq_bound
  intro α hα γ hγ
  exact (sargosQuarticPrefixMaximum_sq_le_curvature hN (abs_le.mpr hγ) hα.1
    (hα.2.trans hA)).trans (mul_le_mul_of_nonneg_left hα.2 (by positivity))

end TaoTrudgianYang2025
