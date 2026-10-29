import Dubon2026.SourceResidueAllLevelDegree
import Dubon2026.SourceLaurentCoefficientReindex
import Dubon2026.SourceLaurentIntegralDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! DUB-17/18 -> original all-weight association -> Gamma1 degree/genus
preservation -> signed-index lower bound -> full modular base degree.
Only the needed direction of degree comparison is proved: mapping an actual
monic equation to the algebraic closure cannot increase its minimum degree.
This reuses the original Laurent coefficient map, rational-function coordinate
description and proved algebraically closed j-substitution degree. A general
linear-disjointness or arbitrary function-field base-change theorem is not needed.
-/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

theorem coeffMap_aeval_coordinate {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (j : LaurentSeries K) (p : K[X]) :
    coeffMap σ (aeval j p) = aeval (coeffMap σ j) (p.map σ) := by
  apply Polynomial.map_aeval_eq_aeval_map
  apply RingHom.ext
  intro a
  change algebraMap L (LaurentSeries L) (σ a) =
    coeffMap σ (algebraMap K (LaurentSeries K) a)
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]

theorem coeffMap_mem_coordinate {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (j x : LaurentSeries K) (hx : x ∈ K⟮j⟯) :
    coeffMap σ x ∈ L⟮coeffMap σ j⟯ := by
  rw [mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p.map σ, q.map σ, by
    rw [map_div₀, coeffMap_aeval_coordinate, coeffMap_aeval_coordinate]⟩

theorem minpoly_coordinate_coeffMap_degree_le {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (j x : LaurentSeries K) (hx : IsIntegral K⟮j⟯ x) :
    (minpoly L⟮coeffMap σ j⟯ (coeffMap σ x)).natDegree ≤
      (minpoly K⟮j⟯ x).natDegree := by
  let φ : K⟮j⟯ →+* L⟮coeffMap σ j⟯ :=
    (coeffMap σ).restrict _ _ fun y hy => coeffMap_mem_coordinate σ j y hy
  have hc : (algebraMap L⟮coeffMap σ j⟯ (LaurentSeries L)).comp φ =
      (coeffMap σ).comp (algebraMap K⟮j⟯ (LaurentSeries K)) := by
    ext a
    rfl
  have hz : aeval (coeffMap σ x) ((minpoly K⟮j⟯ x).map φ) = 0 := by
    rw [← Polynomial.map_aeval_eq_aeval_map hc, minpoly.aeval, map_zero]
  have hm := (minpoly.monic hx).map φ
  have hd := Polynomial.natDegree_le_natDegree
    (minpoly.degree_le_of_ne_zero L⟮coeffMap σ j⟯ (coeffMap σ x) hm.ne_zero hz)
  rwa [(minpoly.monic hx).natDegree_map φ] at hd

end
end Dubon2026.SourceFunctionField.IntegralDiamond
