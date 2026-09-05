import GafniTao.PintzNearOneZetaExponent
import GafniTao.HeathBrownEPHalfLow
import GafniTao.HeathBrownEP1Fixed
import GafniTao.HeathBrownEP1Large

/-!
# Pintz's near-one exponential-sum input

This file assembles only the range needed when Pintz applies (2.19):
`11/12 <= sigma <= 1`.  The five logarithmic-scale pieces use, respectively,
the native `AB` estimate, the native order-four derivative estimate, the two
order-five pieces in Heath--Brown's proof, and the native large-order piece.
-/

namespace GafniTao

noncomputable section

/-- Native unweighted prefix bound with Pintz's coefficient `1/2`, uniform in
the real part and in every terminal point of the dyadic block. -/
theorem norm_pintz2023ExponentialBlock_le_nearOne_target
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma : ℝ) (N R : ℕ) (tau : ℝ),
      sigma ≤ 1 → 11 / 12 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N → 2 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ pintzNearOneUnweightedTarget sigma epsilon tau := by
  obtain ⟨C₄, hC₄, hkfour⟩ :=
    norm_pintz2023ExponentialBlock_le_target_of_exponents
      4 epsilon (by norm_num) hepsilon
      (fun tau : ℝ => 5 / 2 ≤ tau ∧ tau ≤ 7 / 2)
      (fun tau : ℝ => pintzNearOneUnweightedTarget (11 / 12) epsilon tau)
      (by
        intro tau htau
        exact pintz_nearOne_kfour_first_exponent_le
          (by norm_num) (by norm_num) hepsilon.le htau.1 htau.2)
      (by
        intro tau htau
        exact pintz_nearOne_kfour_second_exponent_le
          (by norm_num) (by norm_num) hepsilon.le htau.1)
      (by
        intro tau htau
        exact pintz_nearOne_kfour_third_exponent_le
          (by norm_num) (by norm_num) hepsilon.le htau.1)
  obtain ⟨C₅ₐ, hC₅ₐ, hkfiveA⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_constant epsilon hepsilon
  obtain ⟨C₅ₑ, hC₅ₑ, hkfiveB⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_sloping epsilon hepsilon
  obtain ⟨Cₗ, hCₗ, hlarge⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_large epsilon hepsilon
  let C : ℝ := 90 + C₄ + C₅ₐ + C₅ₑ + Cₗ
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro sigma N R tau hsigmaUpper hsigmaLower hN hNR hR htau
  have hNPos : 0 < N := by omega
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have htargetNonneg :
      0 ≤ (N : ℝ) ^ pintzNearOneUnweightedTarget sigma epsilon tau :=
    Real.rpow_nonneg (by positivity) _
  by_cases hab : tau ≤ 5 / 2
  · have hraw := norm_pintz2023ExponentialBlock_le_AB_log_power
      hN hNR hR htau hab
    have hexp := pintz_nearOne_AB_exponent_le
      hsigmaUpper hsigmaLower hepsilon.le htau hab
    have hpow := Real.rpow_le_rpow_of_exponent_le hNOne hexp
    calc
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
          90 * (N : ℝ) ^ ((tau + 3) / 6) := hraw
      _ ≤ 90 * (N : ℝ) ^
          pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
      _ ≤ C * (N : ℝ) ^
          pintzNearOneUnweightedTarget sigma epsilon tau := by
        apply mul_le_mul_of_nonneg_right _ htargetNonneg
        dsimp only [C]
        nlinarith
  · have htauFive : 5 / 2 ≤ tau := le_of_not_ge hab
    by_cases hk4 : tau ≤ 7 / 2
    · have hraw := hkfour N R tau hNPos hNR hR ⟨htauFive, hk4⟩
      have htargetMono :
          pintzNearOneUnweightedTarget (11 / 12) epsilon tau ≤
            pintzNearOneUnweightedTarget sigma epsilon tau :=
        pintzNearOneUnweightedTarget_lower_endpoint_le
          hsigmaUpper hsigmaLower (by linarith) hk4
      have hpow := Real.rpow_le_rpow_of_exponent_le hNOne htargetMono
      calc
        ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
            C₄ * (N : ℝ) ^
              pintzNearOneUnweightedTarget (11 / 12) epsilon tau := hraw
        _ ≤ C₄ * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
        _ ≤ C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau := by
          apply mul_le_mul_of_nonneg_right _ htargetNonneg
          dsimp only [C]
          nlinarith
    · have htauSeven : 7 / 2 ≤ tau := le_of_not_ge hk4
      have hep := pintz_nearOne_EP1_exponent_le
        hsigmaUpper hepsilon.le htauSeven
      have hpow := Real.rpow_le_rpow_of_exponent_le hNOne hep
      by_cases hfour : tau ≤ 4
      · have hraw := hkfiveA N R tau hNPos hNR hR htauSeven hfour
        calc
          ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
              C₅ₐ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
          _ ≤ C₅ₐ * (N : ℝ) ^
              pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
          _ ≤ C * (N : ℝ) ^
              pintzNearOneUnweightedTarget sigma epsilon tau := by
            apply mul_le_mul_of_nonneg_right _ htargetNonneg
            dsimp only [C]
            nlinarith
      · have hfourLower : 4 ≤ tau := le_of_not_ge hfour
        by_cases hthirteen : tau ≤ 13 / 3
        · have hraw := hkfiveB N R tau hNPos hNR hR hfourLower hthirteen
          calc
            ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
                C₅ₑ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
            _ ≤ C₅ₑ * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
            _ ≤ C * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by
              apply mul_le_mul_of_nonneg_right _ htargetNonneg
              dsimp only [C]
              nlinarith
        · have hthirteenLower : 13 / 3 ≤ tau := le_of_not_ge hthirteen
          have hraw := hlarge N R tau hNPos hNR hR hthirteenLower
          calc
            ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
                Cₗ * (N : ℝ) ^ heathBrownEP1Target epsilon tau := hraw
            _ ≤ Cₗ * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by gcongr
            _ ≤ C * (N : ℝ) ^
                pintzNearOneUnweightedTarget sigma epsilon tau := by
              apply mul_le_mul_of_nonneg_right _ htargetNonneg
              dsimp only [C]
              nlinarith

#print axioms norm_pintz2023ExponentialBlock_le_nearOne_target

end

end GafniTao
