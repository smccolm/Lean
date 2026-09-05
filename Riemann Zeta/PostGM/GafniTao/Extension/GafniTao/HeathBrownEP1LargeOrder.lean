import GafniTao.HeathBrownEP1LargeAlgebra
import GafniTao.HeathBrownEPHalfBlock
import GafniTao.HeathBrownEP1Statement

/-!
# Heath--Brown EP1 on one large source strip

This is the analytic consumer of the exact strip arithmetic.  For one fixed
derivative order it applies the native Heath--Brown derivative theorem and
checks all three terms against equation (1.9).
-/

namespace GafniTao

noncomputable section

theorem norm_pintz2023ExponentialBlock_le_EP1_large_order
    (k : ℕ) (epsilon : ℝ) (hk : 6 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      heathBrownEP1StripLower k ≤ tau →
      tau ≤ heathBrownEP1StripUpper k →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      k (epsilon / 2) (show 3 ≤ k by omega) hepsilonHalf
      (fun tau : ℝ =>
        heathBrownEP1StripLower k ≤ tau ∧
          tau ≤ heathBrownEP1StripUpper k)
      (heathBrownEP1Target epsilon)
      (by
        intro tau htau
        have hsave := (heathBrown_EP1_large_three_savings
          hk htau.1 htau.2).1
        unfold heathBrownLogFirstExponent heathBrownEP1Target
        calc
          1 + epsilon / 2 +
                (tau - (k : ℝ)) / ((k : ℝ) * ((k : ℝ) - 1)) ≤
              1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by
                gcongr
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring)
      (by
        intro tau htau
        have hsave := (heathBrown_EP1_large_three_savings
          hk htau.1 htau.2).2.1
        unfold heathBrownLogSecondExponent heathBrownEP1Target
        calc
          1 + epsilon / 2 -
                1 / ((k : ℝ) * ((k : ℝ) - 1)) =
              1 + epsilon / 2 +
                (-1 / ((k : ℝ) * ((k : ℝ) - 1))) := by ring
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by
            gcongr
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring)
      (by
        intro tau htau
        have hsave := (heathBrown_EP1_large_three_savings
          hk htau.1 htau.2).2.2
        unfold heathBrownLogThirdExponent heathBrownEP1Target
        calc
          1 + epsilon / 2 -
                2 * tau / ((k : ℝ) ^ 2 * ((k : ℝ) - 1)) =
              1 + epsilon / 2 +
                (-2 * tau / ((k : ℝ) ^ 2 * ((k : ℝ) - 1))) := by ring
          _ ≤ 1 + epsilon / 2 + (-49 / (80 * tau ^ 2)) := by
            gcongr
          _ ≤ 1 + epsilon + (-49 / (80 * tau ^ 2)) := by linarith
          _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR hlower hupper
  exact hbound N R tau hN hNR hR ⟨hlower, hupper⟩

#print axioms norm_pintz2023ExponentialBlock_le_EP1_large_order

end

end GafniTao
