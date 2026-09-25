import TaoTrudgianYang2025.RobertSargosSevenSystem

/-! Actual near-coincidences of the two Taylor coordinates in
Robert--Sargos (2002), (4.15) and (4.25). The sign reversal and
the two lower-degree terms are transported to the counting system. -/

noncomputable section
namespace TaoTrudgianYang2025

structure RobertSargosTaylorSystem (R H Q N E : ℝ) (p : RobertSargosSevenPoint) : Prop where
  r_ne_zero : p.r ≠ 0
  r_bound : |(p.r:ℝ)| ≤ R
  q₁_support : |(p.q₁:ℝ)| ∈ Set.Icc Q (2*Q)
  q₂_support : |(p.q₂:ℝ)| ∈ Set.Icc Q (2*Q)
  h₁_support : (p.h₁:ℝ) ∈ Set.Icc H (2*H)
  h₂_support : (p.h₂:ℝ) ∈ Set.Icc H (2*H)
  n₁_support : (p.n₁:ℝ) ∈ Set.Icc 1 N
  n₂_support : (p.n₂:ℝ) ∈ Set.Icc 1 N
  same_sign : 0 < p.q₁*p.q₂
  linear : p.h₁*p.q₁-p.r*p.n₁ = p.h₂*p.q₂-p.r*p.n₂
  near : |robertSargosTaylorQuadratic p.r p.q₁ p.h₁ p.n₁-
    robertSargosTaylorQuadratic p.r p.q₂ p.h₂ p.n₂| ≤ E

def robertSargosReverseR (p : RobertSargosSevenPoint) : RobertSargosSevenPoint :=
  ⟨-p.r,p.q₁,p.q₂,p.h₁,p.h₂,p.n₁,p.n₂⟩

theorem robertSargos_reverseR_involution (p : RobertSargosSevenPoint) :
    robertSargosReverseR (robertSargosReverseR p) = p := by
  cases p
  simp [robertSargosReverseR]

theorem robertSargos_reverseR_injective : Function.Injective robertSargosReverseR :=
  Function.LeftInverse.injective robertSargos_reverseR_involution

theorem RobertSargosTaylorSystem.counting_near {R H Q N E : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosTaylorSystem R H Q N E p)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H) :
    |robertSargosQuadratic (-p.r) p.q₁ p.h₁ p.n₁-
      robertSargosQuadratic (-p.r) p.q₂ p.h₂ p.n₂| ≤ E+12*R*H^2 := by
  have hline : robertSargosLinear (-(p.r:ℝ)) p.q₁ p.h₁ p.n₁ =
      robertSargosLinear (-(p.r:ℝ)) p.q₂ p.h₂ p.n₂ := by
    unfold robertSargosLinear
    have ht : (p.h₁:ℝ)*p.q₁-p.r*p.n₁ = p.h₂*p.q₂-p.r*p.n₂ := by
      exact_mod_cast h.linear
    linarith
  have hh₁ : |(p.h₁:ℝ)| ≤ 2*H := by
    rw [abs_of_nonneg (hH.trans h.h₁_support.1)]
    exact h.h₁_support.2
  have hh₂ : |(p.h₂:ℝ)| ≤ 2*H := by
    rw [abs_of_nonneg (hH.trans h.h₂_support.1)]
    exact h.h₂_support.2
  rw [robertSargos_quadratic_difference hline]
  exact robertSargos_actual_to_counting_tolerance hR hH hRH h.r_bound hh₁ hh₂
    hline h.near

theorem RobertSargosTaylorSystem.to_counting {R H Q N E δ : ℝ}
    {p : RobertSargosSevenPoint} (h : RobertSargosTaylorSystem R H Q N E p)
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hδ : E+12*R*H^2 ≤ δ*H*Q^2) :
    RobertSargosSevenSystem R H Q N δ (robertSargosReverseR p) := by
  refine ⟨neg_ne_zero.mpr h.r_ne_zero,?_,h.q₁_support,h.q₂_support,
    h.h₁_support,h.h₂_support,h.n₁_support,h.n₂_support,h.same_sign,?_,?_⟩
  · simpa only [robertSargosReverseR,Int.cast_neg,abs_neg] using h.r_bound
  · change (-p.r)*p.n₁+p.h₁*p.q₁ = (-p.r)*p.n₂+p.h₂*p.q₂
    linarith only [h.linear]
  · simpa only [robertSargosReverseR,Int.cast_neg] using
      (h.counting_near hR hH hRH).trans hδ

end TaoTrudgianYang2025
