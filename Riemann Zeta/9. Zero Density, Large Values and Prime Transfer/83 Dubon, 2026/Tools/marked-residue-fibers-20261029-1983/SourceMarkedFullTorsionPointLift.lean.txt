import Dubon2026.SourceEllipticSpecializationTorsionRange
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> exhaustion of
the original marked chart over the finite torsion field. The native full
torsion range theorem lifts every exact-order point from the algebraic
closure. The finite Galois torsion-field construction supplies the explicit
N-squared cardinality premise; exact order is preserved by the actual
injective elliptic point map. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve SourceEllipticReduction

theorem exists_exactOrder_baseChange_preimage_of_full_torsion
    {k Ω B : Type*} [Field k] [Field Ω] [Field B] [IsAlgClosed B]
    [DecidableEq Ω] [DecidableEq B] [Algebra k Ω] [Algebra k B] [Algebra Ω B]
    [IsScalarTower k Ω B] (E : WeierstrassCurve k) [E.IsElliptic]
    (N : ℕ) (hN : (N : B) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2)
    (Q : (E.baseChange B).toAffine.Point) (hQ : addOrderOf Q = N) :
    ∃ P : (E.baseChange Ω).toAffine.Point, addOrderOf P = N ∧
      Affine.Point.map (W' := E) (IsScalarTower.toAlgHom k Ω B) P = Q := by
  let ι := IsScalarTower.toAlgHom k Ω B
  let T := Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (N : ℤ)
  let θ := (Affine.Point.map (W' := E) ι).comp T.subtype.toAddMonoidHom
  have hθ : Function.Injective θ := (Affine.Point.map_injective ι).comp Subtype.val_injective
  have hkill : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  obtain ⟨P, hP⟩ := torsion_mem_specialization_range (E.baseChange B) N hN θ hθ hfull Q hkill
  refine ⟨P.val, ?_, hP⟩
  change Affine.Point.map ι P.val = Q at hP
  rw [← addOrderOf_injective (Affine.Point.map (W' := E) ι) (Affine.Point.map_injective ι), hP, hQ]

end
end Dubon2026.SourceFunctionField.MarkedChart
