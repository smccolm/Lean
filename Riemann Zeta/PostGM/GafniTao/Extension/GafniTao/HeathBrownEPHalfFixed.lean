import GafniTao.HeathBrownEPHalfLow

/-!
# Fixed derivative orders for the middle logarithmic ranges

The fourth- and fifth-derivative estimates cover the compact transition
between the A/B-process range and the variable-order argument.  The epsilon
budget is split explicitly in half.
-/

namespace GafniTao

noncomputable section

def heathBrownHalfTarget (epsilon tau : ℝ) : ℝ :=
  1 - 1 / (2 * tau ^ 2) + epsilon

/-- Fourth derivative: `5/2 ≤ tau ≤ 7/2`. -/
theorem norm_pintz2023ExponentialBlock_le_half_kfour
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      5 / 2 ≤ tau → tau ≤ 7 / 2 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      4 (epsilon / 2) (by norm_num) hepsilonHalf
      (fun tau : ℝ => 5 / 2 ≤ tau ∧ tau ≤ 7 / 2)
      (heathBrownHalfTarget epsilon)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfour_first htau.1 htau.2
        unfold heathBrownLogFirstExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfour_second htau.1
        unfold heathBrownLogSecondExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfour_third htau.1
        unfold heathBrownLogThirdExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  exact hbound N R tau hN hNR hR ⟨htauLow, htauHigh⟩

/-- Fifth derivative: `7/2 ≤ tau ≤ 4`. -/
theorem norm_pintz2023ExponentialBlock_le_half_kfive
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      7 / 2 ≤ tau → tau ≤ 4 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      5 (epsilon / 2) (by norm_num) hepsilonHalf
      (fun tau : ℝ => 7 / 2 ≤ tau ∧ tau ≤ 4)
      (heathBrownHalfTarget epsilon)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfive_first htau.1 htau.2
        unfold heathBrownLogFirstExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfive_second htau.1
        unfold heathBrownLogSecondExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
      (by
        intro tau htau
        have hsave := heathBrown_half_kfive_third htau.1
        unfold heathBrownLogThirdExponent heathBrownHalfTarget
        simp only [div_eq_mul_inv, mul_inv] at hsave ⊢
        norm_num at hsave ⊢
        linarith)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  exact hbound N R tau hN hNR hR ⟨htauLow, htauHigh⟩

#print axioms norm_pintz2023ExponentialBlock_le_half_kfour
#print axioms norm_pintz2023ExponentialBlock_le_half_kfive

end

end GafniTao
