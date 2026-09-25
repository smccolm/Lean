import TaoTrudgianYang2025.RobertSargosSevenMultiplicity
import TaoTrudgianYang2025.RobertSargosReducedCount

/-! The full seven-variable target count away from zero displacement. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_seven_nonzero_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) →
      (∀ p ∈ S, p.n₁ ≠ p.n₂) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_reduced_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N δ hR hH hQ hN hδ hRH hmem hne
  have hN0 : 0 ≤ N := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hB : 0 ≤ R*H*Q := by positivity
  have ht : ∀ p ∈ S.image robertSargosDisplacementPoint,
      RobertSargosReducedSystem R H Q δ p := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hmem p hp).to_reduced (hne p hp)
  have hb := hcount _ R H Q δ hR hH hQ hδ hRH ht
  calc
    _ ≤ N*((S.image robertSargosDisplacementPoint).card:ℝ) :=
      robertSargos_seven_card_le_displacement_image S hN hmem
    _ ≤ N*(C*(R*H*Q)^(1+ε)*(1+δ*Q)) := mul_le_mul_of_nonneg_left hb hN0
    _ = C*(N*(R*H*Q)^(1+ε))*(1+δ*Q) := by ring
    _ ≤ C*(N*(R*H*Q))^(1+ε)*(1+δ*Q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (robertSargos_count_multiplicity_algebra hN hB hε.le) hC.le) (by positivity)
    _ = _ := by rw [show N*(R*H*Q) = R*N*H*Q from by ring]

end TaoTrudgianYang2025

