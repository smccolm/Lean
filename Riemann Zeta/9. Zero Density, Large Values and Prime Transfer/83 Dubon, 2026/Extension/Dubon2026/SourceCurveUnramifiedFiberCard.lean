import Dubon2026.SourceCurveFiberDegreeSum
import Dubon2026.SourceCurveCompletionEmbeddingValuation

/-! DUB-17/18 -> auxiliary point division -> compact cover geometry.
The proved ramification-degree sum gives the exact constant cardinal of
the actual restriction fibers when all ramification indices are one.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem card_unramified_restriction_fiber (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (hunram : ∀ w : Place K E, w.ramificationIndex (F := F) = 1) :
    Nat.card {w : Place K E // w.restrict F = v} = Module.finrank F E := by
  classical
  letI : Fintype {w : Place K E // w.restrict F = v} := Fintype.ofFinite _
  have h := sum_fiber_ramification v hbase htop
  have hone (w : {w : Place K E // w.restrict F = v}) :
      w.1.ord (algebraMap F E v.uniformizer) = 1 := by
    have hc := w.1.ramificationIndex_cast (F := F)
    rw [hunram] at hc
    simpa only [w.2, Nat.cast_one] using hc.symm
  simp only [finsum_eq_sum_of_fintype, hone, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast h

end
end Dubon2026.SourceCurve.Place
