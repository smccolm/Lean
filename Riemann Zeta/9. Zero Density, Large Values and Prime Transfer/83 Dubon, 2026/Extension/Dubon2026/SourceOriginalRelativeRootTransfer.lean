import Dubon2026.SourcePrimeConjugateReducedStep

/-! DUB-17/18 -> numerical modular genus -> composite degree -> indexed
roots of the original minimal polynomial. A root of the relative minimal
polynomial over an actual original subfield is also a root of the base
minimal polynomial after the literal expansion embedding. Native tower
divisibility supplies the transfer; the base action is explicit.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem expanded_minpoly_root_of_relative_root
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F)
    (σ : F →+* LaurentSeries K) (A N : ℕ) [NeZero A] [NeZero N]
    (hbase : ∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ F),
      σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ A (z : LaurentSeries ℚ)))
    (y : LaurentSeries K)
    (hy : ((minpoly F (qExpand ℚ N jq)).map σ).eval y = 0) :
    (expandedJMinpoly K A N).eval y = 0 := by
  have hBF : ℚ⟮jq⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hj)
  letI : Algebra ℚ⟮jq⟯ F := (Subfield.inclusion
    (show (ℚ⟮jq⟯).toSubfield ≤ F.toSubfield from hBF)).toAlgebra
  letI : IsScalarTower ℚ⟮jq⟯ F (LaurentSeries ℚ) := IsScalarTower.of_algebraMap_eq' rfl
  have hdvd := minpoly.dvd_map_of_isScalarTower ℚ⟮jq⟯ F (qExpand ℚ N jq)
  have h := Polynomial.map_dvd σ hdvd
  rw [Polynomial.map_map] at h
  have he : σ.comp (algebraMap ℚ⟮jq⟯ F) =
      ((coeffEmb K).comp (qExpand ℚ A)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    refine RingHom.ext fun z => ?_
    exact hbase z (hBF z.2)
  rw [he] at h
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h hy

end
end Dubon2026.SourceFunctionField
