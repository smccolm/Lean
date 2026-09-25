import TaoTrudgianYang2025.RobertSargosPrimitiveProjection
import TaoTrudgianYang2025.RobertSargosFixedCoefficientLoss

/-! Actual source fibers with a fixed coefficient key; every source condition
is extracted from the six-coordinate primitive system. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_coefficient_fiber_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ) (r h₁ h₂ : ℤ),
      0 < H → 0 < Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosPrimitiveSystem R H Q δ p) →
      (∀ p ∈ S, p.r = r ∧ p.h₁ = h₁ ∧ p.h₂ = h₂) →
      (S.card:ℝ) ≤ C*H^ε*(1+δ*Q^2/H) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_robertSargos_fixed_coeff_bound ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q δ r h₁ h₂ hH hQ hδ hRH hmem hfix
  by_cases hs : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hs
    have h₀ := hmem p₀ hp₀
    rcases hfix p₀ hp₀ with ⟨hr₀,hh₁₀,hh₂₀⟩
    have hc : Int.gcd (Int.gcd r h₁ : ℤ) h₂ = 1 := by
      simpa only [hr₀,hh₁₀,hh₂₀] using h₀.coefficient_primitive
    have hr : r ≠ 0 := by simpa only [hr₀] using h₀.r_ne_zero
    have hrH : |(r:ℝ)| ≤ H/2 :=
      (show |(r:ℝ)| ≤ R by simpa only [hr₀] using h₀.r_bound).trans hRH
    have hh₁ : H ≤ (h₁:ℝ) := by simpa only [hh₁₀] using h₀.h₁_support.1
    have hh₂ : H ≤ (h₂:ℝ) := by simpa only [hh₂₀] using h₀.h₂_support.1
    let f : RobertSargosPoint → ℤ × ℤ × ℤ := fun p => (p.q₂,p.q₁,p.d)
    let T := S.image f
    have hinj : Set.InjOn f S := by
      intro p hp q hq he
      apply robertSargos_keys_injective
      · simp only [robertSargosCoefficientKey,(hfix p hp).1,(hfix q hq).1,
          (hfix p hp).2.1,(hfix q hq).2.1,(hfix p hp).2.2,(hfix q hq).2.2]
      · have he₁ := congrArg (fun z : ℤ × ℤ × ℤ => z.1) he
        have he₂ := congrArg (fun z : ℤ × ℤ × ℤ => z.2.1) he
        have he₃ := congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) he
        exact Prod.ext he₃ (Prod.ext he₂ he₁)
    have hTq₁ : ∀ t ∈ T, |(t.2.1:ℝ)| ∈ Set.Icc Q (2*Q) := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      exact (hmem p hp).q₁_support
    have hTq₂ : ∀ t ∈ T, Q ≤ |(t.1:ℝ)| := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      exact (hmem p hp).q₂_support.1
    have hTs : ∀ t ∈ T, 0 < t.2.1*t.1 := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      exact (hmem p hp).same_sign
    have hTp : ∀ t ∈ T, Int.gcd (Int.gcd t.2.2 t.2.1 : ℤ) t.1 = 1 := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      exact (hmem p hp).coordinate_primitive
    have hTl : ∀ t ∈ T, r*t.2.2+h₁*t.2.1-h₂*t.1 = 0 := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      simpa only [f,(hfix p hp).1,(hfix p hp).2.1,(hfix p hp).2.2] using
        (hmem p hp).linear
    have hTn : ∀ t ∈ T, |robertSargosReduced r t.2.1 t.1 h₁ h₂ t.2.2| ≤ δ*H*Q^2 := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      simpa only [f,(hfix p hp).1,(hfix p hp).2.1,(hfix p hp).2.2] using
        (hmem p hp).near
    have hb := hbound T r h₁ h₂ H Q δ hc hr hH hQ hδ hrH hh₁ hh₂
      hTq₁ hTq₂ hTs hTp hTl hTn
    have hcard : T.card = S.card := Finset.card_image_of_injOn hinj
    rwa [hcard] at hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end TaoTrudgianYang2025

