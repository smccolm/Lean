import Dubon2026.SourceModularCoefficientSimplePresentation
import Dubon2026.SourceRationalShiftPowerSpan

/-! The transcendental j-coordinate can be specialized to any actual
transcendental element. Native rational-function equivalences and adjoin
extensionality replace the reference polynomial-localization construction.
This is the entry map for the finite exceptional-fiber orbit argument. -/
namespace Dubon2026.SourceFunctionField.CoefficientPresentation
noncomputable section
open IntermediateField SourceCurve
open scoped IntermediateField
variable (N : ℕ) (K : Type*) [Field K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] {j₀ : Ω}

/-- The actual map of j-coordinate fields sending the original j to j₀. -/
def coordinateSpecialization (hj₀ : Transcendental K j₀) : K⟮jCoeff N K⟯ →ₐ[K] Ω :=
  (rationalCoordinateEmbedding K j₀ hj₀).comp
    (RatFunc.algEquivOfTranscendental (jCoeff N K) (transcendental_jCoeff N K)).symm.toAlgHom

theorem coordinateSpecialization_gen (hj₀ : Transcendental K j₀) :
    coordinateSpecialization N K hj₀ (AdjoinSimple.gen K (jCoeff N K)) = j₀ := by
  change rationalCoordinateEmbedding K j₀ hj₀
    ((RatFunc.algEquivOfTranscendental (jCoeff N K) (transcendental_jCoeff N K)).symm
      (AdjoinSimple.gen K (jCoeff N K))) = j₀
  rw [RatFunc.algEquivOfTranscendental_symm_gen, rationalCoordinateEmbedding_X]

theorem coordinate_algHom_ext {f g : K⟮jCoeff N K⟯ →ₐ[K] Ω}
    (h : f (AdjoinSimple.gen K (jCoeff N K)) = g (AdjoinSimple.gen K (jCoeff N K))) :
    f = g := by
  apply adjoin_algHom_ext K
  intro x hx
  obtain rfl : x = jCoeff N K := Set.mem_singleton_iff.mp hx
  exact h

end
end Dubon2026.SourceFunctionField.CoefficientPresentation
