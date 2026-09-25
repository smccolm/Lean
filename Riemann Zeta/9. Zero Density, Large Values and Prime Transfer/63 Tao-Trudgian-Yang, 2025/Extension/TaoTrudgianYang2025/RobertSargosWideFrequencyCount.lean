import TaoTrudgianYang2025.RobertSargosCoefficientProjection
import TaoTrudgianYang2025.RobertSargosCoefficientFibers

/-! Actual source-fiber summation in the wide-frequency regime. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_primitive_count_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 0 < Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*H^ε*(R*H^2+δ*R*H*Q^2) := by
  classical
  obtain ⟨C,hC,hfiber⟩ := exists_robertSargos_coefficient_fiber_bound ε hε
  refine ⟨12*C,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hRH hmem
  have hHp : 0 < H := by linarith
  let U := S.image robertSargosCoefficientKey
  have hU : (U.card:ℝ) ≤ 12*R*H^2 :=
    robertSargos_coefficient_image_card_le S hR hH hmem
  have hf : ∀ z : ℤ × ℤ × ℤ,
      ((S.filter (fun p => robertSargosCoefficientKey p = z)).card:ℝ) ≤
        C*H^ε*(1+δ*Q^2/H) := by
    intro z
    apply hfiber (S.filter (fun p => robertSargosCoefficientKey p = z))
      R H Q δ z.1 z.2.1 z.2.2 hHp hQ hδ hRH
    · intro p hp
      exact hmem p (Finset.mem_filter.mp hp).1
    · intro p hp
      have he := (Finset.mem_filter.mp hp).2
      exact ⟨congrArg (fun z : ℤ × ℤ × ℤ => z.1) he,
        congrArg (fun z : ℤ × ℤ × ℤ => z.2.1) he,
        congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) he⟩
  have hmaps : Set.MapsTo robertSargosCoefficientKey S U := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ U, ((S.filter (fun p => robertSargosCoefficientKey p = z)).card:ℝ) := by
    exact_mod_cast hcard
  calc
    _ = _ := hcardR
    _ ≤ ∑ _z ∈ U, (C*H^ε*(1+δ*Q^2/H)) :=
      Finset.sum_le_sum (fun z _ => hf z)
    _ = (U.card:ℝ)*(C*H^ε*(1+δ*Q^2/H)) := by simp
    _ ≤ (12*R*H^2)*(C*H^ε*(1+δ*Q^2/H)) :=
      mul_le_mul_of_nonneg_right hU (by positivity)
    _ = _ := by field_simp

end TaoTrudgianYang2025
