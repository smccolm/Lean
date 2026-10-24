import Dubon2026.SourceCurveGeneratorOrders
import Dubon2026.SourceCurveRestrictionOrders
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! Positive order at a finite value of the rational coordinate is one
on the base field. The existing rational-generator degree argument gives
this without classifying rational places. The restriction-order formula
then identifies the extension's specialization order with its normalized
ramification order, as required for DUB-17/18 inertia cardinality. -/
namespace Dubon2026.SourceCurve.Place
open IntermediateField
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem rational_finite_value_order_eq_one (v : Place K (RatFunc K)) (a : K)
    (hv : 0 < v.ord (RatFunc.X - algebraMap K (RatFunc K) a)) :
    v.ord (RatFunc.X - algebraMap K (RatFunc K) a) = 1 := by
  let f : RatFunc K := RatFunc.X - algebraMap K (RatFunc K) a
  have hf : Transcendental K f := by
    intro h
    apply RatFunc.transcendental_X (K := K)
    simpa only [f, sub_add_cancel] using h.add (isAlgebraic_algebraMap a)
  have hgen : K⟮f⟯ = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X]
    apply adjoin_simple_le_iff.mpr
    have h := add_mem (mem_adjoin_simple_self K f) (IntermediateField.algebraMap_mem K⟮f⟯ a)
    simpa only [f, sub_add_cancel] using h
  have hle := SourceCurve.ord_generator_le_one f hf hgen v
  change v.ord (RatFunc.X - algebraMap K (RatFunc K) a) ≤ 1 at hle
  omega

theorem rational_specialization_order_eq_uniformizer_order
    {M : Type*} [Field M] [Algebra (RatFunc K) M] [Algebra K M]
    [IsScalarTower K (RatFunc K) M] [Algebra.IsIntegral (RatFunc K) M]
    (w : Place K M) (a : K)
    (hw : 0 < w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a)) :
    w.ord (algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a) =
      w.ord (algebraMap (RatFunc K) M (w.restrict (RatFunc K)).uniformizer) := by
  let f : RatFunc K := RatFunc.X - algebraMap K (RatFunc K) a
  have hf : algebraMap (RatFunc K) M f =
      algebraMap (RatFunc K) M RatFunc.X - algebraMap K M a := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply K (RatFunc K) M]
  have ho := w.ord_algebraMap_restrict f
  rw [hf] at ho
  have hr := w.ord_restricted_uniformizer_pos (F := RatFunc K)
  have hb : 0 < (w.restrict (RatFunc K)).ord f := by
    rw [ho] at hw
    exact (mul_pos_iff_of_pos_right hr).mp hw
  have hb1 : (w.restrict (RatFunc K)).ord f = 1 :=
    rational_finite_value_order_eq_one (w.restrict (RatFunc K)) a hb
  simpa only [hb1, one_mul] using ho

end
end Dubon2026.SourceCurve.Place
