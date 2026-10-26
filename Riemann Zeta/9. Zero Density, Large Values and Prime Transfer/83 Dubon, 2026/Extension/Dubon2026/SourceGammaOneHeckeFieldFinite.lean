import Dubon2026.SourceGammaOneHeckeDegeneracy
import Dubon2026.SourceFiniteCoordinateHom
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> actual finite Hecke correspondences. Existing finite-coordinate
exchange and finite ring-homomorphism transport prove finiteness of both
literal maps; no modular-polynomial symmetry or finite-map premise is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField

theorem gamma1_hecke_hom_finite (L : Type*) [Field L] [Algebra ℚ L]
    (M d : ℕ) [NeZero M] [NeZero d]
    (φ : laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (d * M))) :
    φ.toRingHom.Finite := by
  obtain ⟨x, hx, _⟩ := gamma1_finite_coordinate M L
  obtain ⟨t, _, ht⟩ := gamma1_hecke_finite_coordinate M (d * M) L
  letI := ht
  have hφx : Transcendental L (φ x) := by
    intro h
    exact hx ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  haveI := SourceCurve.finite_over_transcendental_of_finite_coordinate t hφx
  exact SourceCurve.finite_hom_of_finite_image_coordinate φ x

theorem heckeAlpha_finite (L : Type*) [Field L] [Algebra ℚ L]
    (M d : ℕ) [NeZero M] [NeZero d] :
    (heckeAlpha L M d).toRingHom.Finite :=
  gamma1_hecke_hom_finite L M d (heckeAlpha L M d)

theorem heckeBeta_finite (L : Type*) [Field L] [Algebra ℚ L]
    (M d : ℕ) [NeZero M] [NeZero d] :
    (heckeBeta L M d).toRingHom.Finite :=
  gamma1_hecke_hom_finite L M d (heckeBeta L M d)

end
end Dubon2026.SourceFunctionField.GammaOne
