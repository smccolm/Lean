import TaoTrudgianYang2025.SargosDyadicIntegral

/-! Source-linked integration of the dyadic moment estimates. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosSixthInitialMoment_mono (N : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    sargosSixthInitialMoment N A ≤ sargosSixthInitialMoment N B :=
  sargosQuartic_power_rectangle_mono N 6 (fun _ => 1) le_rfl hAB le_rfl le_rfl

theorem sargosSixthInitialMoment_le_dyadic_budget {N : ℕ} (hN : 1 ≤ N)
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hdyadic : ∀ δ : ℝ, 1/Real.sqrt N ≤ δ → δ ≤ A →
      sargosQuarticDyadicSixthMoment N δ ≤ B*δ) :
    sargosSixthInitialMoment N A ≤ 44845498368*(1+Real.log N)^5+2*A*B := by
  let a : ℝ := 1/Real.sqrt N
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmall := sargosSixthInitialMoment_small hN
  by_cases hAa : A ≤ a
  · have hh := (sargosSixthInitialMoment_mono N hAa).trans hsmall
    have hp : 0 ≤ 2*A*B := by positivity
    linarith only [hh,hp]
  · obtain ⟨K,hend,hscales,hsum⟩ := sargos_dyadic_scale_budget ha (le_of_not_ge hAa)
    let f : ℝ → ℝ := fun α => ∫ γ in Icc (-(1/(N:ℝ)^3)) (1/(N:ℝ)^3),
      ‖sargosQuarticSum N (fun _ => 1) α γ‖^6
    have hi (c d : ℝ) : IntegrableOn f (Icc c d) :=
      integrable_sargosQuarticNormPower_outer N 6 (fun _ => 1) c d _ _
    have hf (x : ℝ) : 0 ≤ f x := integral_nonneg (fun _γ => pow_nonneg (norm_nonneg _) 6)
    have hsplit := sargos_integral_dyadic_split f a K hf hi
    change sargosSixthInitialMoment N (a*2^K) ≤ sargosSixthInitialMoment N a+
      ∑ i ∈ Finset.range K, sargosQuarticDyadicSixthMoment N (a*2^i) at hsplit
    have hbudget : (∑ i ∈ Finset.range K,
        sargosQuarticDyadicSixthMoment N (a*2^i)) ≤ 2*A*B := by
      calc
        _ ≤ ∑ i ∈ Finset.range K, B*(a*2^i) := by
          apply Finset.sum_le_sum
          intro i hiK
          exact hdyadic _ (hscales i hiK).1 (hscales i hiK).2
        _ = B*(∑ i ∈ Finset.range K, a*2^i) := (Finset.mul_sum _ _ _).symm
        _ ≤ B*(2*A) := mul_le_mul_of_nonneg_left hsum hB
        _ = _ := by ring
    have hh := (sargosSixthInitialMoment_mono N hend).trans hsplit
    linarith only [hh,hsmall,hbudget]

theorem sargosSixthBaseMoment_le_dyadic_budget {N : ℕ} (hN : 1 ≤ N)
    {A B : ℝ} (hA : 0 < A) (hA₁ : A ≤ 1/2) (hB : 0 ≤ B)
    (hdyadic : ∀ δ : ℝ, 1/Real.sqrt N ≤ δ → δ ≤ A →
      sargosQuarticDyadicSixthMoment N δ ≤ B*δ) :
    sargosSixthBaseMoment N ≤
      (1024/A)*(44845498368*(1+Real.log N)^5)+2048*B := by
  calc
    _ ≤ (1024/A)*sargosSixthInitialMoment N A :=
      sargosSixthBaseMoment_localize hN hA hA₁
    _ ≤ (1024/A)*(44845498368*(1+Real.log N)^5+2*A*B) :=
      mul_le_mul_of_nonneg_left
        (sargosSixthInitialMoment_le_dyadic_budget hN hA hB hdyadic) (by positivity)
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
