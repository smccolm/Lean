import Dubon2026.SourceResidueFieldTowerDegree
import Dubon2026.SourceConjugateRemovedRootDistinction

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalEmbeddedConjugate to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_expanded_minpoly_root_of_member
    (F : IntermediateField K (LaurentSeries K)) (hj : (jqModC K) ∈ F)
    (σ : F →+* LaurentSeries K) (A N : ℕ) [NeZero A] [NeZero N]
    (hbase : ∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ F),
      σ ⟨z, hz⟩ = (qExpand K A (z : LaurentSeries K)))
    (hN : qExpand K N (jqModC K) ∈ F) :
    (residueExpandedJMinpoly K A N).IsRoot (σ ⟨qExpand K N (jqModC K), hN⟩) := by
  apply residue_expanded_minpoly_root_of_relative_root F hj σ A N hbase
  have hm : minpoly F (qExpand K N (jqModC K)) = X - C (⟨qExpand K N (jqModC K), hN⟩ : F) :=
    minpoly.eq_X_sub_C (B := LaurentSeries K) (⟨qExpand K N (jqModC K), hN⟩ : F)
  rw [hm, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

theorem residue_expanded_minpoly_slot_root_of_identity (k N : ℕ) [NeZero k] [NeZero N]
    (ζ : Kˣ) (hP : residueExpandedJMinpoly K N N = slotProduct N ζ)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    (residueExpandedJMinpoly K (k * N) N).IsRoot (qExpand K k (slotValue ζ s.1 s.2)) := by
  have hr : (slotProduct N ζ).IsRoot (slotValue ζ s.1 s.2) := by
    apply (Polynomial.mem_roots (slotProduct_monic N ζ).ne_zero).mp
    rw [slotProduct_roots]
    exact Multiset.mem_map.mpr ⟨s, hs, rfl⟩
  rw [← hP] at hr
  have h := hr.map (f := qExpand K k)
  rwa [residueExpandedJMinpoly_qExpand] at h

theorem residue_expanded_minpoly_root_shape_of_identity (k N : ℕ) [NeZero k] [NeZero N]
    (ζ : Kˣ) (hP : residueExpandedJMinpoly K N N = slotProduct N ζ)
    (y : LaurentSeries K) (hy : (residueExpandedJMinpoly K (k * N) N).IsRoot y) :
    ∃ s ∈ indices N, y = qExpand K k (slotValue ζ s.1 s.2) := by
  classical
  rw [← residueExpandedJMinpoly_qExpand, hP, slotProduct, Polynomial.map_prod,
    Polynomial.IsRoot, Polynomial.eval_prod] at hy
  obtain ⟨s, hs, he⟩ := Finset.prod_eq_zero_iff.mp hy
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at he
  exact ⟨s, hs, he⟩

end
end Dubon2026.SourceFunctionField
