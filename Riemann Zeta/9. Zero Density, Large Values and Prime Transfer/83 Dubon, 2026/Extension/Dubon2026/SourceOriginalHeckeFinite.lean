import Dubon2026.SourceOriginalHeckeDegeneracy
import Dubon2026.SourceFiniteCoordinateHom
import Dubon2026.SourceOriginalUniformizerFinite

/-! DUB-17/18 -> original Picard Hecke correspondence -> finite degeneracy
maps. The already proved finiteness over every transcendental coordinate
applies to the image of the actual j coordinate. Native finite-composition
and field-range equivalence then prove both degeneracy maps finite, without
repeating the prime modular-polynomial argument or assuming its symmetry.
The divisor norm and degree identities remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem original_field_hom_finite (L : Type*) [Field L] [Algebra ℚ L]
    (M N : ℕ) [NeZero N]
    (φ : modularFunctionFieldOver M L →ₐ[L] modularFunctionFieldOver N L) :
    φ.toRingHom.Finite := by
  have ht : Transcendental L (φ (jOver M L)) := by
    intro h
    exact transcendental_jOver M L ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  haveI := finiteDimensional_original_over_transcendental N L ht
  exact SourceCurve.finite_hom_of_finite_image_coordinate φ (jOver M L)

theorem originalHeckeAlpha_finite (L : Type*) [Field L] [Algebra ℚ L]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    (originalHeckeAlpha L N ℓ).toRingHom.Finite :=
  original_field_hom_finite L N (N * ℓ) (originalHeckeAlpha L N ℓ)

theorem originalHeckeBeta_finite (L : Type*) [Field L] [Algebra ℚ L]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    (originalHeckeBeta L N ℓ).toRingHom.Finite :=
  original_field_hom_finite L N (N * ℓ) (originalHeckeBeta L N ℓ)

end
end Dubon2026.SourceFunctionField
