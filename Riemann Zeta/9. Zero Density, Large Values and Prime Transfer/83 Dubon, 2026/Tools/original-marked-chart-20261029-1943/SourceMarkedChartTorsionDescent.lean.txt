import Dubon2026.SourceEllipticSpecializationTorsionRange
import Dubon2026.SourceEllipticOddBaseChange

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original-field
marked-point chart. Descend the constructed marked point along the embedding
of the algebraically closed j field. The existing actual torsion cardinality,
specialization-range theorem and injective native point map already supply
surjectivity on prime-to-characteristic torsion; no new torsion census or
point-lifting hypothesis is introduced. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticReduction SourceEllipticVelu.OddDiscriminant

theorem exists_exactOrder_point_preimage {F L : Type*} [Field F] [Field L]
    [IsAlgClosed F] [IsAlgClosed L] [DecidableEq F] [DecidableEq L]
    (W : WeierstrassCurve F) [W.IsElliptic] (f : F →+* L)
    (N : ℕ) (hN : (N : F) ≠ 0) (Q : (W.map f).toAffine.Point) (hQ : addOrderOf Q = N) :
    ∃ P : W.toAffine.Point, addOrderOf P = N ∧ pointMapHom f W P = Q := by
  let A := Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)
  let θ := (pointMapHom f W).comp A.subtype.toAddMonoidHom
  have hθ : Function.Injective θ := (pointMapHom_injective f W).comp Subtype.val_injective
  have hc : Nat.card {P : W.toAffine.Point // N • P = 0} = N ^ 2 := by
    let e : {P : W.toAffine.Point // N • P = 0} ≃ A :=
      Equiv.subtypeEquivRight fun P => by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    rw [Nat.card_congr e]
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
      using SourceEllipticTorsion.actual_torsion_cardinality W hN
  have hNL : (N : L) ≠ 0 := by
    simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hN
  have hkill : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  obtain ⟨P, hP⟩ := torsion_mem_specialization_range (W.map f) N hNL θ hθ hc Q hkill
  change pointMapHom f W P.val = Q at hP
  refine ⟨P.val, ?_, hP⟩
  rw [← addOrderOf_injective (pointMapHom f W) (pointMapHom_injective f W), hP, hQ]

end
end Dubon2026.SourceFunctionField.MarkedChart
