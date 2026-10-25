import Dubon2026.SourceFiniteCoordinateHom
import Dubon2026.SourceOriginalUniformizerFinite
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! DUB-17/18 -> original Weil reciprocity -> finite norm transfer of
coordinate reciprocity. The actual original field is finite over the image
of every rational-coordinate embedding, by the existing transcendental
coordinate theorem. No degree or finiteness input remains at this interface. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Embed the rational field using an actual transcendental function. -/
def rationalCoordinate (t : F) (ht : Transcendental K t) : RatFunc K →ₐ[K] F :=
  (K⟮t⟯.val).comp (RatFunc.algEquivOfTranscendental t ht).toAlgHom

theorem rationalCoordinate_X (t : F) (ht : Transcendental K t) :
    rationalCoordinate t ht RatFunc.X = t := RatFunc.algEquivOfTranscendental_X t ht

end
end Dubon2026.SourceCurve
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

theorem original_ratfunc_hom_finite (φ : RatFunc L →ₐ[L] modularFunctionFieldOver N L) :
    φ.toRingHom.Finite := by
  have ht : Transcendental L (φ RatFunc.X) := by
    intro h
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  haveI := finiteDimensional_original_over_transcendental N L ht
  exact SourceCurve.finite_hom_of_finite_image_coordinate φ RatFunc.X

end
end Dubon2026.SourceFunctionField
