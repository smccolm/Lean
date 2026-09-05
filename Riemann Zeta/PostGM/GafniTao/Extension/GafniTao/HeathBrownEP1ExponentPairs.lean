import GafniTao.HeathBrownEP1Fixed
import GafniTao.HeathBrownEP1Large

/-!
# The two exact classical exponent-pair inputs in Heath--Brown EP1

These propositions expose, rather than hide, the only two remaining inputs to
Heath--Brown (2017), Theorem 4 for the logarithmic phase.  They are strictly
narrower than EP1 and record the source exponents and ranges literally.  The
theorems below prove the complete epsilon and range transfer from those inputs
to equation (1.9).  Separate modules must prove both propositions natively.
-/

namespace GafniTao

noncomputable section

def HeathBrownOneNinthExponentPairBound : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N →
      2 ≤ tau → tau ≤ 59 / 22 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ (1 + (2 * tau - 7) / 18 + epsilon)

def HeathBrownOneTwentiethExponentPairBound : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N →
      59 / 22 ≤ tau → tau ≤ 7 / 2 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ (1 + (2 * tau - 9) / 40 + epsilon)

theorem norm_pintz2023ExponentialBlock_le_EP1_low
    (hpair : HeathBrownOneNinthExponentPairBound)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N →
      2 ≤ tau → tau ≤ 59 / 22 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  obtain ⟨C, hC, hbound⟩ := hpair (epsilon / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  have hraw := hbound N R tau hN hNR hR htauLow htauHigh
  have hsave := heathBrown_EP1_low_range htauLow htauHigh
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hexponent :
      1 + (2 * tau - 7) / 18 + epsilon / 2 ≤
        heathBrownEP1Target epsilon tau := by
    unfold heathBrownEP1Target
    calc
      1 + (2 * tau - 7) / 18 + epsilon / 2 ≤
          1 + (-49 / (80 * tau ^ 2)) + epsilon / 2 := by linarith
      _ ≤ 1 + (-49 / (80 * tau ^ 2)) + epsilon := by linarith
      _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hNOne hexponent) hC.le)

theorem norm_pintz2023ExponentialBlock_le_EP1_middle
    (hpair : HeathBrownOneTwentiethExponentPairBound)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N →
      59 / 22 ≤ tau → tau ≤ 7 / 2 →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
  obtain ⟨C, hC, hbound⟩ := hpair (epsilon / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htauLow htauHigh
  have hraw := hbound N R tau hN hNR hR htauLow htauHigh
  have hsave := heathBrown_EP1_middle_exponent_pair_range htauLow htauHigh
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hexponent :
      1 + (2 * tau - 9) / 40 + epsilon / 2 ≤
        heathBrownEP1Target epsilon tau := by
    unfold heathBrownEP1Target
    calc
      1 + (2 * tau - 9) / 40 + epsilon / 2 ≤
          1 + (-49 / (80 * tau ^ 2)) + epsilon / 2 := by linarith
      _ ≤ 1 + (-49 / (80 * tau ^ 2)) + epsilon := by linarith
      _ = 1 - 49 / (80 * tau ^ 2) + epsilon := by ring
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hNOne hexponent) hC.le)

/-- Complete source-range assembly.  The only assumptions are the two
classical exponent-pair specializations displayed above. -/
theorem heathBrownEP1ExponentialSumBound_of_exponentPairs
    (honeNinth : HeathBrownOneNinthExponentPairBound)
    (honeTwentieth : HeathBrownOneTwentiethExponentPairBound) :
    HeathBrownEP1ExponentialSumBound := by
  intro epsilon hepsilon
  obtain ⟨C₁, hC₁, hlow⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_low honeNinth epsilon hepsilon
  obtain ⟨C₂, hC₂, hmiddle⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_middle
      honeTwentieth epsilon hepsilon
  obtain ⟨C₃, hC₃, hkfiveConstant⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_constant epsilon hepsilon
  obtain ⟨C₄, hC₄, hkfiveSloping⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_kfive_sloping epsilon hepsilon
  obtain ⟨C₅, hC₅, hlarge⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_large epsilon hepsilon
  let C : ℝ := max C₁ (max C₂ (max C₃ (max C₄ C₅)))
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau
  have hNPos : 0 < N := by omega
  have hpowNonneg : 0 ≤ (N : ℝ) ^ heathBrownEP1Target epsilon tau := by
    positivity
  by_cases h₁ : tau ≤ 59 / 22
  · exact (hlow N R tau hN hNR hR htau h₁).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowNonneg)
  by_cases h₂ : tau ≤ 7 / 2
  · have hraw := hmiddle N R tau hN hNR hR (le_of_not_ge h₁) h₂
    exact hraw.trans (mul_le_mul_of_nonneg_right
      ((le_max_left C₂ (max C₃ (max C₄ C₅))).trans (le_max_right C₁ _))
      hpowNonneg)
  by_cases h₃ : tau ≤ 4
  · have hraw := hkfiveConstant N R tau hNPos hNR hR
      (le_of_not_ge h₂) h₃
    have hC₃le : C₃ ≤ C :=
      (le_max_left C₃ (max C₄ C₅)).trans
        ((le_max_right C₂ _).trans (le_max_right C₁ _))
    exact hraw.trans (mul_le_mul_of_nonneg_right hC₃le hpowNonneg)
  by_cases h₄ : tau ≤ 13 / 3
  · have hraw := hkfiveSloping N R tau hNPos hNR hR
      (le_of_not_ge h₃) h₄
    have hC₄le : C₄ ≤ C :=
      (le_max_left C₄ C₅).trans
        ((le_max_right C₃ _).trans
          ((le_max_right C₂ _).trans (le_max_right C₁ _)))
    exact hraw.trans (mul_le_mul_of_nonneg_right hC₄le hpowNonneg)
  · have hraw := hlarge N R tau hNPos hNR hR (le_of_not_ge h₄)
    have hC₅le : C₅ ≤ C :=
      (le_max_right C₄ C₅).trans
        ((le_max_right C₃ _).trans
          ((le_max_right C₂ _).trans (le_max_right C₁ _)))
    exact hraw.trans (mul_le_mul_of_nonneg_right hC₅le hpowNonneg)

#print axioms norm_pintz2023ExponentialBlock_le_EP1_low
#print axioms norm_pintz2023ExponentialBlock_le_EP1_middle
#print axioms heathBrownEP1ExponentialSumBound_of_exponentPairs

end

end GafniTao
