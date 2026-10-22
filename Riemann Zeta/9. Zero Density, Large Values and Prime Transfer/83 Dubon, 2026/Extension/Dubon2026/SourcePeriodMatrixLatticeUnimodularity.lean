import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> raw period reciprocity.
The exact strict cyclic-word matrix must be skew-symmetric and unimodular.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Only the required cyclic interval and lattice arguments are retained;
the existing actual dissection, loop generation and full real span supply
their inputs in the original-curve consumer.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open Module

theorem isUnit_det_of_lattice {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (z J : ι → V) (P : Matrix ι ι ℤ)
    (hJ : ∀ j, J j = -∑ l, P j l • z l)
    (hz : ∀ l, z l ∈ AddSubgroup.closure (Set.range J))
    (hspan : ⊤ ≤ Submodule.span ℝ (Set.range z))
    (hcard : Fintype.card ι = finrank ℝ V) : IsUnit P.det := by
  classical

  have hM : ∀ l, ∃ m : ι → ℤ, z l = ∑ j, m j • J j := by
    intro l
    have h := hz l
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
      Submodule.mem_span_range_iff_exists_fun] at h
    obtain ⟨m, hm⟩ := h
    exact ⟨m, hm.symm⟩
  choose M hM using hM

  have hind : LinearIndependent ℝ z := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard

  have hrow : ∀ l, ∑ k, (((1 : Matrix ι ι ℤ) + (Matrix.of M) * P) l k : ℝ) • z k = 0 := by
    intro l
    have h1 : z l = -∑ k, ((Matrix.of M * P) l k) • z k := by
      calc z l = ∑ j, M l j • J j := hM l
        _ = ∑ j, M l j • (-∑ k, P j k • z k) := by simp_rw [← hJ]
        _ = -∑ k, (∑ j, M l j * P j k) • z k := by
          simp only [smul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul, neg_inj]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
        _ = -∑ k, ((Matrix.of M * P) l k) • z k := by
          simp only [Matrix.mul_apply, Matrix.of_apply]
    have h2 : ∑ k, (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k) • z k = 0 := by
      simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [h1]; abel
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]

  have hMP : (1 : Matrix ι ι ℤ) + Matrix.of M * P = 0 := by
    ext l k
    have := (linearIndependent_iff'.1 hind) Finset.univ
      (fun k => (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k : ℝ)) (hrow l) k (Finset.mem_univ k)
    have h' : (((1 : Matrix ι ι ℤ) + Matrix.of M * P) l k : ℝ) = 0 := this
    rw [Matrix.zero_apply]
    exact_mod_cast h'
  have hprod : Matrix.of M * P = -1 := eq_neg_of_add_eq_zero_right hMP
  have hdet : (Matrix.of M).det * P.det = (-1 : Matrix ι ι ℤ).det := by
    rw [← Matrix.det_mul, hprod]
  rw [Matrix.det_neg, Matrix.det_one, mul_one] at hdet

  have hu : IsUnit ((Matrix.of M).det * P.det) := by
    rw [hdet]; exact (isUnit_neg_one.pow _)
  exact isUnit_of_mul_isUnit_right hu

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
