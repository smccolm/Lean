import Dubon2026.SourceOriginalFieldTowerDegree
import Dubon2026.SourceConjugateRemovedRootDistinction

/-! DUB-17/18 -> numerical modular genus -> composite degree and
generation -> conjugate-root induction. An actual original field embedding
sends every contained j-substitution to a root of its expanded minimal
polynomial. A proved lower-level product identity then supplies the exact
indexed Laurent shape. The product identity remains a lower-level
induction input; the actual embedding and expansion are used literally.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem expanded_minpoly_root_of_member
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F)
    (σ : F →+* LaurentSeries K) (A N : ℕ) [NeZero A] [NeZero N]
    (hbase : ∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ F),
      σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ A (z : LaurentSeries ℚ)))
    (hN : qExpand ℚ N jq ∈ F) :
    (expandedJMinpoly K A N).IsRoot (σ ⟨qExpand ℚ N jq, hN⟩) := by
  apply expanded_minpoly_root_of_relative_root F hj σ A N hbase
  have hm : minpoly F (qExpand ℚ N jq) = X - C (⟨qExpand ℚ N jq, hN⟩ : F) :=
    minpoly.eq_X_sub_C (B := LaurentSeries ℚ) (⟨qExpand ℚ N jq, hN⟩ : F)
  rw [hm, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

theorem expanded_minpoly_slot_root_of_identity (k N : ℕ) [NeZero k] [NeZero N]
    (ζ : Kˣ) (hP : expandedJMinpoly K N N = slotProduct N ζ)
    (s : Σ _ : ℕ, ℕ) (hs : s ∈ indices N) :
    (expandedJMinpoly K (k * N) N).IsRoot (qExpand K k (slotValue ζ s.1 s.2)) := by
  have hr : (slotProduct N ζ).IsRoot (slotValue ζ s.1 s.2) := by
    apply (Polynomial.mem_roots (slotProduct_monic N ζ).ne_zero).mp
    rw [slotProduct_roots]
    exact Multiset.mem_map.mpr ⟨s, hs, rfl⟩
  rw [← hP] at hr
  have h := hr.map (f := qExpand K k)
  rwa [expandedJMinpoly_qExpand] at h

theorem expanded_minpoly_root_shape_of_identity (k N : ℕ) [NeZero k] [NeZero N]
    (ζ : Kˣ) (hP : expandedJMinpoly K N N = slotProduct N ζ)
    (y : LaurentSeries K) (hy : (expandedJMinpoly K (k * N) N).IsRoot y) :
    ∃ s ∈ indices N, y = qExpand K k (slotValue ζ s.1 s.2) := by
  classical
  rw [← expandedJMinpoly_qExpand, hP, slotProduct, Polynomial.map_prod,
    Polynomial.IsRoot, Polynomial.eval_prod] at hy
  obtain ⟨s, hs, he⟩ := Finset.prod_eq_zero_iff.mp hy
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at he
  exact ⟨s, hs, he⟩

end
end Dubon2026.SourceFunctionField
