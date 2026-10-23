import Dubon2026.SourceResiduePrimeReducedStep

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalRelativeRootTransfer to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_expanded_minpoly_root_of_relative_root
    (F : IntermediateField K (LaurentSeries K)) (hj : (jqModC K) ∈ F)
    (σ : F →+* LaurentSeries K) (A N : ℕ) [NeZero A] [NeZero N]
    (hbase : ∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ F),
      σ ⟨z, hz⟩ = (qExpand K A (z : LaurentSeries K)))
    (y : LaurentSeries K)
    (hy : ((minpoly F (qExpand K N (jqModC K))).map σ).eval y = 0) :
    (residueExpandedJMinpoly K A N).eval y = 0 := by
  have hBF : K⟮(jqModC K)⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hj)
  letI : Algebra K⟮(jqModC K)⟯ F := (Subfield.inclusion
    (show (K⟮(jqModC K)⟯).toSubfield ≤ F.toSubfield from hBF)).toAlgebra
  letI : IsScalarTower K⟮(jqModC K)⟯ F (LaurentSeries K) := IsScalarTower.of_algebraMap_eq' rfl
  have hdvd := minpoly.dvd_map_of_isScalarTower K⟮(jqModC K)⟯ F (qExpand K N (jqModC K))
  have h := Polynomial.map_dvd σ hdvd
  rw [Polynomial.map_map] at h
  have he : σ.comp (algebraMap K⟮(jqModC K)⟯ F) =
      ((qExpand K A)).comp (algebraMap K⟮(jqModC K)⟯ (LaurentSeries K)) := by
    refine RingHom.ext fun z => ?_
    exact hbase z (hBF z.2)
  rw [he] at h
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h hy

end
end Dubon2026.SourceFunctionField
