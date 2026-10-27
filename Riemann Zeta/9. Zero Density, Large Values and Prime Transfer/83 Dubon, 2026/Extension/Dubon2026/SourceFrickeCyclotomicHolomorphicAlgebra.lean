import Dubon2026.SourceFrickeLaurentIndependence

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient twists of the actual Fricke span. The actual holomorphic
cyclotomic fractions form an algebra over the original field. This supplies
the original scalar module whose basis will be extended using the proved
Laurent independence theorem; no twist-stability premise is introduced. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem holomorphicCyclotomicFrickeFractions_add {N : ℕ} [NeZero N] {F G : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) :
    F + G ∈ holomorphicCyclotomicFrickeFractions N := by
  obtain ⟨hFh, a, ha, b, hb, hb0, hFb⟩ := hF
  obtain ⟨hGh, c, hc, d, hd, hd0, hGd⟩ := hG
  refine ⟨hFh.add hGh, a * d + c * b,
    Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha hd) (Subalgebra.mul_mem _ hc hb),
    b * d, Subalgebra.mul_mem _ hb hd, ?_, ?_⟩
  · intro hbd
    exact ((UpperHalfPlane.mul_eq_zero_iff (cyclotomicLevelRing_holomorphic hb)
      (cyclotomicLevelRing_holomorphic hd)).mp hbd).elim hb0 hd0
  · calc (F + G) * (b * d) = (F * b) * d + (G * d) * b := by ring
         _ = a * d + c * b := by rw [hFb, hGd]

theorem holomorphicCyclotomicFrickeFractions_mul {N : ℕ} [NeZero N] {F G : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) :
    F * G ∈ holomorphicCyclotomicFrickeFractions N := by
  obtain ⟨hFh, a, ha, b, hb, hb0, hFb⟩ := hF
  obtain ⟨hGh, c, hc, d, hd, hd0, hGd⟩ := hG
  refine ⟨hFh.mul hGh, a * c, Subalgebra.mul_mem _ ha hc,
    b * d, Subalgebra.mul_mem _ hb hd, ?_, ?_⟩
  · intro hbd
    exact ((UpperHalfPlane.mul_eq_zero_iff (cyclotomicLevelRing_holomorphic hb)
      (cyclotomicLevelRing_holomorphic hd)).mp hbd).elim hb0 hd0
  · calc (F * G) * (b * d) = (F * b) * (G * d) := by ring
         _ = a * c := by rw [hFb, hGd]

/-- The algebra of actual holomorphic fractions over the original cyclotomic Fricke ring. -/
def cyclotomicHolomorphicFrickeAlgebra (N : ℕ) [NeZero N] : Subalgebra (kN N) (ℍ → ℂ) where
  carrier := holomorphicCyclotomicFrickeFractions N
  zero_mem' := ⟨mdifferentiable_const, 0, zero_mem _, 1, one_mem _, one_ne_zero, zero_mul _⟩
  one_mem' := ⟨mdifferentiable_const, 1, one_mem _, 1, one_mem _, one_ne_zero, one_mul _⟩
  add_mem' := holomorphicCyclotomicFrickeFractions_add
  mul_mem' := holomorphicCyclotomicFrickeFractions_mul
  algebraMap_mem' c := ⟨mdifferentiable_const, algebraMap (kN N) (ℍ → ℂ) c,
    Subalgebra.algebraMap_mem _ c, 1, one_mem _, one_ne_zero, mul_one _⟩

end
end Dubon2026.SourceFricke