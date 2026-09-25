import TaoTrudgianYang2025.RobertSargosFrequencyCoordinates
import TaoTrudgianYang2025.RobertSargosFixedDisplacementLoss

/-! Uniform bounds on the actual source frequency fibers. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_frequency_fiber_conic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (z : ℤ × ℤ × ℤ),
      0 < H → 0 < Q → 0 ≤ δ →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, robertSargosFrequencyKey p = z) →
      (S.card:ℝ) ≤ C*(z.1.natAbs:ℝ)^ε*(1+8*H^2*δ/z.1.natAbs) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_robertSargos_fixed_displacement_conic_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q δ z hH hQ hδ hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    let T := S.image robertSargosCoefficientTriple
    have hT := robertSargos_frequency_fiber_image_valid S hmem hfix
    have h₀ := hT _ (Finset.mem_image.mpr ⟨p₀,hp₀,rfl⟩)
    have hb := hbound T z.1 z.2.1 z.2.2 H Q δ
      h₀.coordinate_primitive h₀.d_ne_zero hH hQ hδ
      h₀.q₁_support.1 h₀.q₂_support.1 h₀.same_sign
      (fun t ht => (hT t ht).h₁_support)
      (fun t ht => (hT t ht).h₂_support)
      (fun t ht => (hT t ht).coefficient_primitive)
      (fun t ht => by
        have hl := (hT t ht).linear
        dsimp [robertSargosFromFrequencyKey] at hl
        nlinarith only [hl])
      (fun t ht => (hT t ht).near)
    have hcard : T.card = S.card := robertSargos_frequency_fiber_image_card S hfix
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

theorem exists_robertSargos_frequency_fiber_linear_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (z : ℤ × ℤ × ℤ),
      0 ≤ R → 0 < H → 0 < Q → δ ≤ 1 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, robertSargosFrequencyKey p = z) →
      (S.card:ℝ) ≤ C*(z.1.natAbs:ℝ)^ε*(1+72*H*R/z.1.natAbs) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_robertSargos_fixed_displacement_linear_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q δ z hR hH hQ hδ hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    let T := S.image robertSargosCoefficientTriple
    have hT := robertSargos_frequency_fiber_image_valid S hmem hfix
    have h₀ := hT _ (Finset.mem_image.mpr ⟨p₀,hp₀,rfl⟩)
    have hb := hbound T z.1 z.2.1 z.2.2 R H Q δ
      h₀.coordinate_primitive h₀.d_ne_zero hR hH hQ hδ
      h₀.q₁_support h₀.q₂_support h₀.same_sign
      (fun t ht => (hT t ht).h₁_support)
      (fun t ht => (hT t ht).h₂_support)
      (fun t ht => (hT t ht).r_bound)
      (fun t ht => (hT t ht).coefficient_primitive)
      (fun t ht => by
        have hl := (hT t ht).linear
        dsimp [robertSargosFromFrequencyKey] at hl
        nlinarith only [hl])
      (fun t ht => (hT t ht).near)
    have hcard : T.card = S.card := robertSargos_frequency_fiber_image_card S hfix
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025

