import Dubon2026.SourceCyclotomicConjugateCancellation

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> elliptic divisibility under cyclotomic conjugation. Holomorphic
division of original cyclotomic Fricke fractions stays in that original
fraction algebra. Analytic conjugation then transports the actual quotient
identity; the quotient is not merely in a complex linear span. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem holomorphicCyclotomicFrickeFractions_of_holomorphic_quotient
    {N : ℕ} [NeZero N] {F H W : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hH : H ∈ holomorphicCyclotomicFrickeFractions N) (hH0 : H ≠ 0)
    (hW : MDiff W) (hWH : W * H = F) : W ∈ holomorphicCyclotomicFrickeFractions N := by
  obtain ⟨_, a, ha, b, hb, hb0, hFb⟩ := hF
  obtain ⟨hHhol, c, hc, d, hd, hd0, hHd⟩ := hH
  have hc0 : c ≠ 0 := by
    intro hz
    have hprod : H * d = 0 := hHd.trans hz
    exact hH0 (((UpperHalfPlane.mul_eq_zero_iff hHhol
      (cyclotomicLevelRing_holomorphic hd)).mp hprod).resolve_right hd0)
  refine ⟨hW, a * d, Subalgebra.mul_mem _ ha hd,
    b * c, Subalgebra.mul_mem _ hb hc, ?_, ?_⟩
  · intro hz
    exact ((UpperHalfPlane.mul_eq_zero_iff (cyclotomicLevelRing_holomorphic hb)
      (cyclotomicLevelRing_holomorphic hc)).mp hz).elim hb0 hc0
  · calc W * (b * c) = ((W * H) * b) * d := by rw [← hHd]; ring
         _ = a * d := by rw [hWH, hFb]

theorem CyclotomicConjugates.holomorphic_division {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {F G J W : ℍ → ℂ}
    (hFG : CyclotomicConjugates σ F G) (hJJ : CyclotomicConjugates σ J J)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N)
    (hJ : J ∈ holomorphicCyclotomicFrickeFractions N) (hJ0 : J ≠ 0)
    (hW : MDiff W) (hWJ : W * J = F) :
    ∃ W' : ℍ → ℂ, MDiff W' ∧ W' * J = G := by
  have hWmem := holomorphicCyclotomicFrickeFractions_of_holomorphic_quotient hF hJ hJ0 hW hWJ
  obtain ⟨W', hW', hWW'⟩ := exists_cyclotomicConjugates σ hWmem
  have hprod : CyclotomicConjugates σ F (W' * J) := by
    simpa only [hWJ] using hWW'.mul hJJ
  exact ⟨W', hW'.1, hprod.unique hFG (holomorphicCyclotomicFrickeFractions_mul hW' hJ) hG⟩

end
end Dubon2026.SourceFricke
