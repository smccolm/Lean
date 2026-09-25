import TaoTrudgianYang2025.RobertSargosProductFibers

/-! The primitive source count for tolerance at least one, via the exact product equation. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_primitive_count_large_tolerance (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ δ →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  obtain ⟨C,hC,hfiber⟩ := exists_robertSargos_product_fiber_bound ε hε
  refine ⟨570*C*(4:ℝ)^ε,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hmem
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hB : 0 < R*H*Q := by positivity
  let U := S.image robertSargosProductKey
  have hU : (U.card:ℝ) ≤ 570*δ*R*H*Q^2 :=
    robertSargos_product_image_card_le S hR hH hQ hδ hmem
  have hmaps : Set.MapsTo robertSargosProductKey S U := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ U, ((S.filter (fun p => robertSargosProductKey p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hf : ∀ z : (ℤ × ℤ × ℤ) × ℤ,
      ((S.filter (fun p => robertSargosProductKey p = z)).card:ℝ) ≤ C*(4*H*Q)^ε := by
    intro z
    exact hfiber _ R H Q δ z hHp hQp
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hHQ : H*Q ≤ R*H*Q := by
    have hm := mul_le_mul_of_nonneg_right hR (mul_nonneg hHp.le hQp.le)
    nlinarith only [hm]
  have hpow : (4*H*Q)^ε ≤ (4:ℝ)^ε*(R*H*Q)^ε := by
    calc
      _ = (4:ℝ)^ε*(H*Q)^ε := by
        rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hHQ hε.le) (by positivity)
  have hmass : δ*R*H*Q^2 ≤ (R*H*Q)*(1+δ*Q) := by
    nlinarith only [hB]
  have hmass570 : 570*δ*R*H*Q^2 ≤ 570*((R*H*Q)*(1+δ*Q)) := by
    nlinarith only [hmass]
  have hb : (570*δ*R*H*Q^2)*(C*(4*H*Q)^ε) ≤
      (570*((R*H*Q)*(1+δ*Q)))*(C*((4:ℝ)^ε*(R*H*Q)^ε)) :=
    mul_le_mul hmass570
      (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity) (by positivity)
  calc
    _ = _ := hcardR
    _ ≤ ∑ _z ∈ U, C*(4*H*Q)^ε := Finset.sum_le_sum (fun z _ => hf z)
    _ = (U.card:ℝ)*(C*(4*H*Q)^ε) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (570*δ*R*H*Q^2)*(C*(4*H*Q)^ε) :=
      mul_le_mul_of_nonneg_right hU (by positivity)
    _ ≤ (570*((R*H*Q)*(1+δ*Q)))*(C*((4:ℝ)^ε*(R*H*Q)^ε)) := hb
    _ = _ := by rw [Real.rpow_add hB,Real.rpow_one]; ring

end TaoTrudgianYang2025
