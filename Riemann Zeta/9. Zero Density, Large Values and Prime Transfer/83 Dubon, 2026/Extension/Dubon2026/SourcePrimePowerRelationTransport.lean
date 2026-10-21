import Dubon2026.SourcePrimePowerAdjacentEmbedding

/-! DUB-17/18 -> numerical modular genus -> exact prime-power degree
-> nonmembership contradiction. Transport the actual integral relation
through a subfield embedding. This is used for both adjacent j roots,
without a new symmetry premise or an abstract polynomial-data package.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open Polynomial

theorem relationAtSeed_eval_subfield_map {K : Type*} [Field K]
    (P : Polynomial (Polynomial ℤ))
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (x y : F) (h : (relationAtSeed P (x : LaurentSeries ℚ)).eval (y : LaurentSeries ℚ) = 0) :
    (relationAtSeed P (σ x)).eval (σ y) = 0 := by
  have hF : (relationAtSeed P x).eval y = 0 := by
    apply (algebraMap F (LaurentSeries ℚ)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map]
    exact h
  have h' := congrArg σ hF
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map] at h'
  exact h'

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
