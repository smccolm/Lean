import TaoTrudgianYang2025.RobertSargosSmallToleranceCount
import TaoTrudgianYang2025.RobertSargosLargeToleranceCount

/-! Full uniform primitive six-variable count from Robert--Sargos (2002),
for the actual source system and every nonnegative tolerance. Closed boxes
overcount the paper's half-open supports. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_primitive_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  obtain ⟨Cs,hCs,hs⟩ := exists_robertSargos_primitive_count_small_tolerance ε hε
  obtain ⟨Cl,hCl,hl⟩ := exists_robertSargos_primitive_count_large_tolerance ε hε
  refine ⟨Cs+Cl,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hRH hmem
  have hnonneg : 0 ≤ (R*H*Q)^(1+ε)*(1+δ*Q) := by positivity
  by_cases hsmall : δ ≤ 1
  · calc
      _ ≤ Cs*(R*H*Q)^(1+ε)*(1+δ*Q) :=
        hs S R H Q δ hR hH hQ ⟨hδ,hsmall⟩ hRH hmem
      _ ≤ (Cs+Cl)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hCl]) hnonneg
      _ = _ := by ring
  · calc
      _ ≤ Cl*(R*H*Q)^(1+ε)*(1+δ*Q) :=
        hl S R H Q δ hR hH hQ (le_of_not_ge hsmall) hmem
      _ ≤ (Cs+Cl)*((R*H*Q)^(1+ε)*(1+δ*Q)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hCs]) hnonneg
      _ = _ := by ring

end TaoTrudgianYang2025

