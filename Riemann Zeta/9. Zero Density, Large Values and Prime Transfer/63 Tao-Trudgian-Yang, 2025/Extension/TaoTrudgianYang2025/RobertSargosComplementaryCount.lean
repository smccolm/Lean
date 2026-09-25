import TaoTrudgianYang2025.RobertSargosWeightedScale

/-! Unconditional weighted source counts, assembled from the actual conic and linear
frequency fibers. All constants depend only on epsilon. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_primitive_count_conic_weight (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      0 ≤ R → 0 < H → 1 ≤ Q → δ ∈ Set.Icc 0 1 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*Q^ε*Q*(1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ) := by
  classical
  obtain ⟨C,hC,hfiber⟩ := exists_robertSargos_frequency_fiber_conic_bound
    (ε/2) (by linarith)
  refine ⟨C*(180*(1+2/ε)*(9:ℝ)^ε),by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hmem
  have hδ0 : 0 ≤ δ := hδ.1
  have hQp : 0 < Q := by linarith
  have hf : ∀ z : ℤ × ℤ × ℤ,
      ((S.filter (fun p => robertSargosFrequencyKey p = z)).card:ℝ) ≤
        C*(z.1.natAbs:ℝ)^(ε/2)*(1+(8*H^2*δ)/z.1.natAbs) := by
    intro z
    exact hfiber _ R H Q δ z hH hQp hδ0
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  calc
    _ ≤ C*(2*(1+2/ε)*(4*Q+1)*(2*(δ*Q+99*R*Q/H)+1)*
        (⌊9*Q⌋₊:ℝ)^ε*((⌊9*Q⌋₊:ℝ)+8*H^2*δ)) :=
      robertSargos_card_le_weighted_frequency_sum S hH hQ hδ hR hε
        (by positivity) hC.le hmem hf
    _ ≤ C*((180*(1+2/ε)*(9:ℝ)^ε)*Q^ε*Q*
        (1+(δ*Q+99*R*Q/H))*(Q+8*H^2*δ)) :=
      mul_le_mul_of_nonneg_left
        (robertSargos_weighted_sum_scale hQ (by positivity) hε (by positivity)) hC.le
    _ = _ := by ring

theorem exists_robertSargos_primitive_count_linear_weight (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      0 ≤ R → 0 < H → 1 ≤ Q → δ ∈ Set.Icc 0 1 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*Q^ε*Q*(1+(δ*Q+99*R*Q/H))*(Q+72*H*R) := by
  classical
  obtain ⟨C,hC,hfiber⟩ := exists_robertSargos_frequency_fiber_linear_bound
    (ε/2) (by linarith)
  refine ⟨C*(180*(1+2/ε)*(9:ℝ)^ε),by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hmem
  have hδ0 : 0 ≤ δ := hδ.1
  have hQp : 0 < Q := by linarith
  have hf : ∀ z : ℤ × ℤ × ℤ,
      ((S.filter (fun p => robertSargosFrequencyKey p = z)).card:ℝ) ≤
        C*(z.1.natAbs:ℝ)^(ε/2)*(1+(72*H*R)/z.1.natAbs) := by
    intro z
    exact hfiber _ R H Q δ z hR hH hQp hδ.2
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  calc
    _ ≤ C*(2*(1+2/ε)*(4*Q+1)*(2*(δ*Q+99*R*Q/H)+1)*
        (⌊9*Q⌋₊:ℝ)^ε*((⌊9*Q⌋₊:ℝ)+72*H*R)) :=
      robertSargos_card_le_weighted_frequency_sum S hH hQ hδ hR hε
        (by positivity) hC.le hmem hf
    _ ≤ C*((180*(1+2/ε)*(9:ℝ)^ε)*Q^ε*Q*
        (1+(δ*Q+99*R*Q/H))*(Q+72*H*R)) :=
      mul_le_mul_of_nonneg_left
        (robertSargos_weighted_sum_scale hQ (by positivity) hε (by positivity)) hC.le
    _ = _ := by ring

end TaoTrudgianYang2025

