import Dubon2026.SourceCyclotomicEllipticDivisibility
import Dubon2026.SourceFrickeEllipticCoordinateTwist

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> the two elliptic divisibility conditions. The actual j and
j-1728 coordinates are fixed by cyclotomic conjugation. Consume the original
E4-cube and E6-square identities, retaining the original holomorphic quotients. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField ModularForm
open scoped Manifold ModularForm

theorem CyclotomicConjugates.jShift {N : ℕ} [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N)
    (c : ℚ) : CyclotomicConjugates σ
      (cyclotomicFrickeJShift N c : ℍ → ℂ) (cyclotomicFrickeJShift N c : ℍ → ℂ) := by
  have h := (CyclotomicConjugates.j σ).add (CyclotomicConjugates.const σ (-(c : kN N)))
  simpa only [cyclotomicFrickeJShift, map_neg, map_ratCast, sub_eq_add_neg,
    IntermediateField.coe_neg, Pi.add_apply] using h

theorem CyclotomicConjugates.E4_divisibility {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) (m a : ℕ)
    (hdiv : ∃ W : ℍ → ℂ, MDiff W ∧ ∀ τ : ℍ,
      (F τ * CuspForm.discriminant τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * W τ) :
    ∃ W : ℍ → ℂ, MDiff W ∧ ∀ τ : ℍ,
      (G τ * CuspForm.discriminant τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * W τ := by
  apply hFG.elliptic_divisibility hF hG (cyclotomicFrickeJShift N 0)
    (cyclotomicFrickeJShift_ne_zero N 0) (by simpa using CyclotomicConjugates.jShift σ 0)
    E₄ m 3 a _ hdiv
  intro τ
  change E₄ τ ^ 3 = (JMultiplicity.jf τ - (0 : ℂ)) * CuspForm.discriminant τ
  simp only [sub_zero, JMultiplicity.jf, CuspForm.coe_discriminant,
    div_mul_cancel₀ _ (discriminant_ne_zero τ)]

theorem CyclotomicConjugates.E6_divisibility {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) (m b : ℕ)
    (hdiv : ∃ W : ℍ → ℂ, MDiff W ∧ ∀ τ : ℍ,
      (F τ * CuspForm.discriminant τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * W τ) :
    ∃ W : ℍ → ℂ, MDiff W ∧ ∀ τ : ℍ,
      (G τ * CuspForm.discriminant τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * W τ := by
  apply hFG.elliptic_divisibility hF hG (cyclotomicFrickeJShift N 1728)
    (cyclotomicFrickeJShift_ne_zero N 1728) (by simpa using CyclotomicConjugates.jShift σ 1728)
    E₆ m 2 b _ hdiv
  intro τ
  change E₆ τ ^ 2 = (JMultiplicity.jf τ - (1728 : ℂ)) * CuspForm.discriminant τ
  rw [jf_sub_1728]
  exact (div_mul_cancel₀ _ (discriminant_ne_zero τ)).symm

end
end Dubon2026.SourceFricke
