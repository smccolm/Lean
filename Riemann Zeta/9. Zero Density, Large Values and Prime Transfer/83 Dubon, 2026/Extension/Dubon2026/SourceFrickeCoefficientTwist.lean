import Dubon2026.SourceFrickeScalarExtensionBasis
import Dubon2026.SourceComplexBasisCoefficientTwist

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient descent. The proved scalar-extension basis constructs the
actual coefficient twist on the original holomorphic Fricke function span.
It fixes every original cyclotomic fraction and applies the automorphism to
the complex scalars in every finite representation. Cusp-subspace stability
is a subsequent obligation, not an input to this construction. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Module UpperHalfPlane SourceFunctionField

/-- Include the original cyclotomic Fricke algebra in its complex function span. -/
def cyclotomicFrickeSpanInclusion (N : ℕ) [NeZero N] :
    (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule →ₗ[kN N]
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) where
  toFun F := ⟨F, Submodule.subset_span F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient twist of the actual complex span of holomorphic cyclotomic Fricke fractions. -/
def frickeCoefficientTwist (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ) :
    (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) ≃ₗ[kN N]
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) :=
  basisCoefficientTwist (cyclotomicFrickeComplexBasis N) σ

theorem frickeCoefficientTwist_fixes_original (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) :
    frickeCoefficientTwist N σ (cyclotomicFrickeSpanInclusion N F) =
      cyclotomicFrickeSpanInclusion N F := by
  let b := Module.Free.chooseBasis (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule
  have he : (frickeCoefficientTwist N σ).toLinearMap.comp (cyclotomicFrickeSpanInclusion N) =
      cyclotomicFrickeSpanInclusion N := by
    apply b.ext
    intro i
    change frickeCoefficientTwist N σ (cyclotomicFrickeSpanInclusion N (b i)) =
      cyclotomicFrickeSpanInclusion N (b i)
    have hi : cyclotomicFrickeSpanInclusion N (b i) = cyclotomicFrickeComplexBasis N i := by
      apply Subtype.ext
      exact (cyclotomicFrickeComplexBasis_apply N i).symm
    rw [hi]
    exact basisCoefficientTwist_basis (cyclotomicFrickeComplexBasis N) σ i
  exact LinearMap.congr_fun he F

theorem frickeCoefficientTwist_smul (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (c : ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    frickeCoefficientTwist N σ (c • F) = σ c • frickeCoefficientTwist N σ F :=
  basisCoefficientTwist_smul (cyclotomicFrickeComplexBasis N) σ c F

theorem frickeCoefficientTwist_sum_original (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) :
    (frickeCoefficientTwist N σ (∑ i ∈ s, c i • cyclotomicFrickeSpanInclusion N (F i)) : ℍ → ℂ) =
      ∑ i ∈ s, σ (c i) • (F i : ℍ → ℂ) := by
  rw [map_sum]
  simp_rw [frickeCoefficientTwist_smul, frickeCoefficientTwist_fixes_original]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rfl

end
end Dubon2026.SourceFricke