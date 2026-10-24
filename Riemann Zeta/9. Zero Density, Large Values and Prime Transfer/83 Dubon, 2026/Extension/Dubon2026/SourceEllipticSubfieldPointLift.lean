import Dubon2026.SourceEllipticFiniteCoefficientField

/-! Lift actual points whose coordinates lie in the coefficient field.
The native nonsingularity reflection and injective point map preserve the
actual points, their orders and their cyclic subgroups in the product descent. -/

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- Actual affine coordinates in the image of a field embedding lift to an actual point. -/
theorem exists_pointMapHom_of_coordinates (f : K →+* F) (V : WeierstrassCurve K)
    (P : (V.map f).toAffine.Point)
    (hx : (coordsOrZero P).1 ∈ Set.range f) (hy : (coordsOrZero P).2 ∈ Set.range f) :
    ∃ R, pointMapHom f V R = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, map_zero _⟩
  · obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨Point.some a b ((V.toAffine.map_nonsingular f.injective a b).mp h), rfl⟩

/-- Equality transport of curves preserves the literal point coordinates. -/
theorem coordsOrZero_cast {W V : WeierstrassCurve F} (h : W = V)
    (P : W.toAffine.Point) :
    coordsOrZero (AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) h P) =
      coordsOrZero P := by
  subst V
  rfl

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
