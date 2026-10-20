import Dubon2026.FiniteBaseCMCharacterComparison
import Dubon2026.PolarizationCongruenceInvolution

/-! The CM kernel and the actual real-place involution generate the
original arithmetic group. Their aligned matrix and polarization data
therefore prove whole polarized conjugacy on the DUB-17 descent route. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the full polarized comparison. -/
local instance finiteBaseCMPolarizedAlignmentUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A single basis change aligning the original CM matrices and actual
real-place form conjugates the entire polarized arithmetic representation. -/
theorem finiteBaseCM_polarized_conjugate_of_alignment
    (σ₀ σ₁ : finiteBaseArithmeticGaloisGroup a F →* PolarizedGaloisGroup ι R)
    (r s : FiniteBaseCMKernel a F K →* GeneralLinearGroup ι R)
    (μ : FiniteBaseCMKernel a F K →* Rˣ) (B₀ B₁ W : GeneralLinearGroup ι R)
    (h₀ : ∀ g : FiniteBaseCMKernel a F K, σ₀ g.val = polarizedIdentityComponent (r g, μ g))
    (h₁ : ∀ g : FiniteBaseCMKernel a F K, σ₁ g.val = polarizedIdentityComponent (s g, μ g))
    (hc₀ : σ₀ (finiteBaseRealConjugation a F) = polarizedInvolution B₀)
    (hc₁ : σ₁ (finiteBaseRealConjugation a F) = polarizedInvolution B₁)
    (hW : ∀ g, r g = W * s g * W⁻¹) (hB : polarizationCongruence B₁ W = B₀) :
    ∀ g, σ₀ g = polarizedLinearInclusion W * σ₁ g * (polarizedLinearInclusion W)⁻¹ := by
  have he : (MulAut.conj (polarizedLinearInclusion W)).toMonoidHom.comp σ₁ = σ₀ := by
    apply finiteBaseCMCharacter_ext a F K
    · intro g
      change polarizedLinearInclusion W * σ₁ g.val * (polarizedLinearInclusion W)⁻¹ = σ₀ g.val
      rw [h₁, h₀, polarizedLinear_conjugate_identity, ← hW]
    · change polarizedLinearInclusion W * σ₁ (finiteBaseRealConjugation a F) *
          (polarizedLinearInclusion W)⁻¹ = σ₀ (finiteBaseRealConjugation a F)
      rw [hc₁, hc₀, polarizedLinear_conjugate_involution, hB]
  exact fun g => (DFunLike.congr_fun he g).symm

end
end Dubon2026
