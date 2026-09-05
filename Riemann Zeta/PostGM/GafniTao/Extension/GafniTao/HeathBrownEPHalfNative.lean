import GafniTao.HeathBrownEPHalfLarge

/-!
# Uniform coefficient-one-half exponential-sum estimate

This is the complete replacement for the one exponential-sum input used in
Pintz's zeta estimate.  It combines the exact A/B-process range, fixed fourth
and fifth derivatives, and the uniform variable-order argument.
-/

namespace GafniTao

noncomputable section

/-- The coefficient-one-half logarithmic saving, stated with all uniform
quantifiers needed by the later dyadic zeta consumer. -/
def HeathBrownHalfExponentialSumBound : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N → 2 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau

/-- Native proof of the uniform coefficient-one-half logarithmic saving. -/
theorem heathBrownHalfExponentialSumBound_native :
    HeathBrownHalfExponentialSumBound := by
  intro epsilon hepsilon
  obtain ⟨C₄, hC₄, hfour⟩ :=
    norm_pintz2023ExponentialBlock_le_half_kfour epsilon hepsilon
  obtain ⟨C₅, hC₅, hfive⟩ :=
    norm_pintz2023ExponentialBlock_le_half_kfive epsilon hepsilon
  obtain ⟨CLarge, hCLarge, hinfty⟩ :=
    norm_pintz2023ExponentialBlock_le_half_large epsilon hepsilon
  let C : ℝ := max 90 (max C₄ (max C₅ CLarge))
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 90)
    (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau
  have hNPos : 0 < N := by omega
  have hpowNonneg :
      0 ≤ (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by positivity
  by_cases hlow : tau ≤ 5 / 2
  · have hraw := norm_pintz2023ExponentialBlock_le_half_low
      hN hNR hR htau hlow hepsilon
    exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowNonneg)
  · have htauFourLow : 5 / 2 ≤ tau := le_of_not_ge hlow
    by_cases hfourHigh : tau ≤ 7 / 2
    · have hraw := hfour N R tau hNPos hNR hR htauFourLow hfourHigh
      have hcoeff : C₄ ≤ C := by
        dsimp only [C]
        exact le_max_of_le_right (le_max_left _ _)
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hpowNonneg)
    · have htauFiveLow : 7 / 2 ≤ tau := le_of_not_ge hfourHigh
      by_cases hfiveHigh : tau ≤ 4
      · have hraw := hfive N R tau hNPos hNR hR htauFiveLow hfiveHigh
        have hcoeff : C₅ ≤ C := by
          dsimp only [C]
          exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
        exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hpowNonneg)
      · have htauLarge : 4 ≤ tau := le_of_not_ge hfiveHigh
        have hraw := hinfty N R tau hNPos hNR hR htauLarge
        have hcoeff : CLarge ≤ C := by
          dsimp only [C]
          exact le_max_of_le_right
            (le_max_of_le_right (le_max_right _ _))
        exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hpowNonneg)

#print axioms heathBrownHalfExponentialSumBound_native

end

end GafniTao
