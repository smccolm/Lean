import TaoTrudgianYang2025.RobertSargosSevenNonzeroCount
import TaoTrudgianYang2025.RobertSargosSevenZeroCount

/-! Complete actual seven-variable count, including zero displacement and both gcds. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_seven_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  obtain ⟨Cz,hCz,hzero⟩ := exists_robertSargos_seven_zero_count ε hε
  obtain ⟨Cn,hCn,hnonzero⟩ := exists_robertSargos_seven_nonzero_count ε hε
  refine ⟨Cz+Cn,by positivity,?_⟩
  intro S R H Q N δ hR hH hQ hN hδ hRH hmem
  let Z := S.filter (fun p => p.n₁ = p.n₂)
  let U := S.filter (fun p => p.n₁ ≠ p.n₂)
  have hcard : (S.card:ℝ) = (Z.card:ℝ)+(U.card:ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := S) (fun p => p.n₁ = p.n₂)).symm
  have hz := hzero Z R H Q N δ hR hH hQ hN
    (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hu := hnonzero U R H Q N δ hR hH hQ hN hδ hRH
    (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
  have hQ0 : 0 ≤ Q := by linarith
  have hone : 1 ≤ 1+δ*Q := by nlinarith only [mul_nonneg hδ hQ0]
  have hz' : (Z.card:ℝ) ≤ Cz*(R*N*H*Q)^(1+ε)*(1+δ*Q) :=
    hz.trans (le_mul_of_one_le_right (by positivity) hone)
  calc
    _ = (Z.card:ℝ)+(U.card:ℝ) := hcard
    _ ≤ Cz*(R*N*H*Q)^(1+ε)*(1+δ*Q)+Cn*(R*N*H*Q)^(1+ε)*(1+δ*Q) :=
      add_le_add hz' hu
    _ = _ := by ring

end TaoTrudgianYang2025

