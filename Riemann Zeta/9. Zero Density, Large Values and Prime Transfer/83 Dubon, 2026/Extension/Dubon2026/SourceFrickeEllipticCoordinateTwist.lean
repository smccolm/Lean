import Dubon2026.SourceFrickeEllipticDivisibilityTwist
import Dubon2026.SourceAnalyticJSurjectivity
import Dubon2026.SourceInverseJDerivativePower

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> the two original elliptic-point divisibility conditions. Instantiate the
proved transport with the actual j and j-1728 functions and the existing
E4-cube/discriminant and E6-square/discriminant identities. Nonzero
coordinates follow from proved surjectivity of the original analytic j. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField ModularForm
open scoped Manifold ModularForm

/-- The actual analytic j-coordinate shifted by an original cyclotomic constant. -/
def cyclotomicFrickeJShift (N : ℕ) [NeZero N] (c : kN N) :
    (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule :=
  ⟨JMultiplicity.jf - fun _ : ℍ => (c : ℂ),
    JMultiplicity.mdifferentiable_jf.sub mdifferentiable_const,
    JMultiplicity.jf - fun _ : ℍ => (c : ℂ),
    Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _))
      (Subalgebra.algebraMap_mem _ c), 1, one_mem _, one_ne_zero, mul_one _⟩

theorem cyclotomicFrickeJShift_ne_zero (N : ℕ) [NeZero N] (c : kN N) :
    (cyclotomicFrickeJShift N c : ℍ → ℂ) ≠ 0 := by
  intro hz
  obtain ⟨τ, hτ⟩ := JMultiplicity.jf_surjective ((c : ℂ) + 1)
  have he := congrFun hz τ
  change JMultiplicity.jf τ - (c : ℂ) = 0 at he
  rw [hτ] at he
  have : (1 : ℂ) = 0 := by linear_combination he
  exact one_ne_zero this

theorem frickeCoefficientTwist_E4_divisibility (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m a : ℕ) (hdiv : ∃ G : ℍ → ℂ, MDiff G ∧ ∀ τ : ℍ,
      ((F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) :
    ∃ G' : ℍ → ℂ, MDiff G' ∧ ∀ τ : ℍ,
      ((frickeCoefficientTwist N σ F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ 3 =
        E₄ τ ^ (3 * a) * G' τ := by
  apply frickeCoefficientTwist_transport_elliptic_divisibility N σ F
    (cyclotomicFrickeJShift N 0) (cyclotomicFrickeJShift_ne_zero N 0) E₄ m 3 a _ hdiv
  intro τ
  change E₄ τ ^ 3 = (JMultiplicity.jf τ - (0 : ℂ)) * CuspForm.discriminant τ
  simp only [sub_zero, JMultiplicity.jf, CuspForm.coe_discriminant,
    div_mul_cancel₀ _ (discriminant_ne_zero τ)]

theorem frickeCoefficientTwist_E6_divisibility (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m b : ℕ) (hdiv : ∃ G : ℍ → ℂ, MDiff G ∧ ∀ τ : ℍ,
      ((F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) :
    ∃ G' : ℍ → ℂ, MDiff G' ∧ ∀ τ : ℍ,
      ((frickeCoefficientTwist N σ F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ 2 =
        E₆ τ ^ (2 * b) * G' τ := by
  apply frickeCoefficientTwist_transport_elliptic_divisibility N σ F
    (cyclotomicFrickeJShift N 1728) (cyclotomicFrickeJShift_ne_zero N 1728) E₆ m 2 b _ hdiv
  intro τ
  change E₆ τ ^ 2 = (JMultiplicity.jf τ - (1728 : ℂ)) * CuspForm.discriminant τ
  rw [jf_sub_1728]
  exact (div_mul_cancel₀ _ (discriminant_ne_zero τ)).symm

end
end Dubon2026.SourceFricke