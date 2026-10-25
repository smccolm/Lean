import Dubon2026.SourceCurveNormFiberEvaluation
import Dubon2026.SourceCurveFiberRegularIntegrality
import Dubon2026.SourceCurveRationalFunctionEvaluation

/-! DUB-17/18 -> Frobenius determinant -> Weil reciprocity and Hecke
adjointness -> evaluation of the actual field norm on a place fiber.
Fiber regularity supplies integrality, the native integral/field norm bridge
identifies the norm, and the proved ramified residue calculation gives the
full fiber product. No integrality or norm-evaluation certificate remains. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

omit [Algebra K E] [IsScalarTower K F E] in
theorem algebraMap_norm_integralClosureAt (v : Place K F) (c : integralClosureAt E v) :
    algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c) =
      Algebra.norm F (algebraMap (integralClosureAt E v) E c) := by
  letI : Module.Free v.toValuationSubring (integralClosureAt E v) :=
    Module.free_of_finite_type_torsion_free'
  rw [← Algebra.intNorm_eq_norm, Algebra.algebraMap_intNorm (A := v.toValuationSubring)
    (K := F) (L := E) (B := integralClosureAt E v)]

theorem norm_mem_of_fiber_ord_nonneg (v : Place K F) {f : E}
    (hord : ∀ w : Place K E, w.restrict F = v → 0 ≤ w.ord f) :
    Algebra.norm F f ∈ v.toValuationSubring := by
  obtain ⟨c, rfl⟩ := exists_integralClosureAt_of_fiber_ord_nonneg v hord
  rw [← algebraMap_norm_integralClosureAt]
  exact (Algebra.norm v.toValuationSubring c).property

theorem rationalEval_norm_eq_finprod_fiber (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {f : E} (hord : ∀ w : Place K E, w.restrict F = v → 0 ≤ w.ord f) :
    v.rationalEval hbase (Algebra.norm F f) =
      ∏ᶠ w : {w : Place K E // w.restrict F = v},
        (w.val.rationalEval (htop w.val) f) ^
          (w.val.ord (algebraMap F E v.uniformizer)).toNat := by
  obtain ⟨c, rfl⟩ := exists_integralClosureAt_of_fiber_ord_nonneg v hord
  rw [rationalEval_of_mem v hbase (norm_mem_of_fiber_ord_nonneg v hord)]
  have hn : (⟨Algebra.norm F (algebraMap (integralClosureAt E v) E c),
      norm_mem_of_fiber_ord_nonneg v hord⟩ : v.toValuationSubring) =
      Algebra.norm v.toValuationSubring c :=
    Subtype.ext (algebraMap_norm_integralClosureAt v c).symm
  rw [hn, rationalRegularEval_norm_eq_finprod_fiber v hbase htop]
  apply finprod_congr
  intro w
  rw [rationalEval_of_mem w.val (htop w.val)
    (integralClosureAt_mem_of_restrict_eq w.property c)]

end
end Dubon2026.SourceCurve.Place
