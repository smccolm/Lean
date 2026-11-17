import Dubon2026.SourceCurveSeparatingGenusMaximum
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation -> reverse genus -> tame exceptional
fibers. Translating a separating coordinate preserves its actual intermediate
field. Native degree and rational residue results therefore compute the full
multiplicity of each finite fiber, including the original j=0 and j=1728 fibers.
This discharges their multiplicity sums without any fiber-count hypothesis. -/

noncomputable section

namespace Dubon2026.SourceCurve

open IntermediateField
open scoped IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (t : F)

/-- A finite translation of the actual modular coordinate is transcendental. -/
private theorem coordinate_sub_transcendental (ht : Transcendental K t) (c : K) :
    Transcendental K (t - algebraMap K F c) := by
  intro h
  apply ht
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

/-- Translating the actual coordinate preserves its literal intermediate field. -/
private theorem coordinate_sub_adjoin (c : K) :
    K⟮t - algebraMap K F c⟯ = K⟮t⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr
      (K⟮t⟯.sub_mem (mem_adjoin_simple_self _ _) (K⟮t⟯.algebraMap_mem c))
  · apply adjoin_simple_le_iff.mpr
    have h := (K⟮t - algebraMap K F c⟯).add_mem
      (mem_adjoin_simple_self _ _) (IntermediateField.algebraMap_mem _ c)
    simpa only [sub_add_cancel] using h

variable [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]
variable (ht : Transcendental K t)
include ht

/-- Every finite coordinate fiber has total multiplicity equal to the coordinate degree. -/
theorem sum_fiber_orders_eq_finrank_separating [IsAlgClosed K] (c : K) :
    (∑ᶠ v : {v : Place K F //
        0 < v.ord (t - algebraMap K F c)},
      v.1.ord (t - algebraMap K F c)) =
        (Module.finrank K⟮t⟯ F : ℤ) := by
  haveI : FiniteDimensional K⟮t - algebraMap K F c⟯
      F := by
    rw [coordinate_sub_adjoin]
    infer_instance
  haveI : Algebra.IsSeparable K⟮t - algebraMap K F c⟯
      F := by
    rw [coordinate_sub_adjoin]
    infer_instance
  have h := sum_positive_orders_eq_finrank_separating _ (coordinate_sub_transcendental t ht c)
  have hr (v : Place K F) :=
    Module.finrank_of_bijective_algebraMap (place_residue_bijective_of_finite_coordinate t v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rw [coordinate_sub_adjoin] at h
  exact h

/-- Every complete finite j fiber has the computed total multiplicity. -/
theorem sum_fiber_orders_finset_separating [IsAlgClosed K] (c : K)
    (S : Finset (Place K F))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord
      (t - algebraMap K F c)) :
    (∑ v ∈ S, v.ord (t - algebraMap K F c)) =
      (Module.finrank K⟮t⟯ F : ℤ) := by
  have h := sum_fiber_orders_eq_finrank_separating t ht c
  have he : {v : Place K F |
      0 < v.ord (t - algebraMap K F c)} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem
    (f := fun v : Place K F =>
      v.ord (t - algebraMap K F c))
    {v | 0 < v.ord (t - algebraMap K F c)}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

end Dubon2026.SourceCurve
