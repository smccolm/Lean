import GafniTao.HeathBrownEP1Algebra
import GafniTao.HeathBrownEP1Statement
import GafniTao.HeathBrownEPHalfBlock

/-!
# Heath--Brown EP1: the fixed fifth-derivative ranges

This file proves the two ranges of Heath--Brown (2017), Theorem 4, equation
(1.9), that use the fifth-derivative estimate.  The three terms in the native
derivative theorem are compared separately with the published
`49 / (80 * tau^2)` saving.
-/

namespace GafniTao

noncomputable section

/-- The constant-saving fifth-derivative range `7/2 ≤ tau ≤ 4`. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_kfive_constant
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      7 / 2 ≤ tau → tau ≤ 4 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      5 (epsilon / 2) (by norm_num) hepsilonHalf
      (fun tau : ℝ => 7 / 2 ≤ tau ∧ tau ≤ 4)
      (heathBrownEP1Target epsilon)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_constant_range hlow hhigh
        unfold heathBrownLogFirstExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 + (tau - 5) / 20 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 + (tau - 5) / 20 ≤
              1 + epsilon / 2 + (-1 / 20) := by linarith
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_constant_range hlow hhigh
        unfold heathBrownLogSecondExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 - 1 / 20 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 - 1 / 20 ≤
              1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_constant_range hlow hhigh
        unfold heathBrownLogThirdExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 - 2 * tau / 100 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 - 2 * tau / 100 ≤
              1 + epsilon / 2 - 1 / 20 := by linarith
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  exact hbound N R tau hN hNR hR ⟨htauLow, htauHigh⟩

/-- The sloping-saving fifth-derivative range `4 ≤ tau ≤ 13/3`. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_kfive_sloping
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      4 ≤ tau → tau ≤ 13 / 3 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      5 (epsilon / 2) (by norm_num) hepsilonHalf
      (fun tau : ℝ => 4 ≤ tau ∧ tau ≤ 13 / 3)
      (heathBrownEP1Target epsilon)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_sloping_range hlow hhigh
        unfold heathBrownLogFirstExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 + (tau - 5) / 20 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 + (tau - 5) / 20 ≤
              1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_sloping_range hlow hhigh
        unfold heathBrownLogSecondExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 - 1 / 20 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 - 1 / 20 ≤
              1 + epsilon / 2 + (tau - 5) / 20 := by linarith
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
      (by
        intro tau htau
        rcases htau with ⟨hlow, hhigh⟩
        have hsave := heathBrown_EP1_kfive_sloping_range hlow hhigh
        unfold heathBrownLogThirdExponent heathBrownEP1Target
        have hcomparison :
            1 + epsilon / 2 - 2 * tau / 100 ≤
              1 - 49 / (80 * tau ^ 2) + epsilon := by
          calc
          1 + epsilon / 2 - 2 * tau / 100 ≤
              1 + epsilon / 2 + (tau - 5) / 20 := by linarith
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by linarith
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
        convert hcomparison using 1
        all_goals norm_num)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  exact hbound N R tau hN hNR hR ⟨htauLow, htauHigh⟩

#print axioms norm_pintz2023ExponentialBlock_le_EP1_kfive_constant
#print axioms norm_pintz2023ExponentialBlock_le_EP1_kfive_sloping

end

end GafniTao
