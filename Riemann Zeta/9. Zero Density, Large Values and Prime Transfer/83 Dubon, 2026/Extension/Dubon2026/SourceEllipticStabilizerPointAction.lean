import Dubon2026.SourceEllipticVariableAddEquiv

/-! DUB-17/18 -> modular good reduction -> reverse genus -> exceptional
fibers -> cyclic inertia orbits. The actual stabilizing coordinate change
acts on the native elliptic point group. Equality after the curve cast is
equivalent to the literal heterogeneous equality used in the source. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- The actual inverse coordinate map, with its stabilized curve identified. -/
def stabilizerPointEquiv (W : WeierstrassCurve K) (C : VariableChange K)
    (hC : C • W = W) : W.toAffine.Point ≃+ W.toAffine.Point :=
  (variableChangeAddEquiv C W.toAffine).symm.trans
    (AddEquiv.cast (M := fun V : WeierstrassCurve K => V.toAffine.Point) hC)

private theorem point_cast_eq_iff_heq {V W : WeierstrassCurve K}
    (h : V = W) (P : V.toAffine.Point) (Q : W.toAffine.Point) :
    AddEquiv.cast (M := fun U : WeierstrassCurve K => U.toAffine.Point) h P = Q ↔
      HEq P Q := by
  subst W
  exact heq_iff_eq.symm

theorem stabilizerPointEquiv_eq_iff_heq (W : WeierstrassCurve K)
    (C : VariableChange K) (hC : C • W = W) (P Q : W.toAffine.Point) :
    stabilizerPointEquiv W C hC P = Q ↔ HEq (vcInvFun C W.toAffine P) Q :=
  point_cast_eq_iff_heq hC _ _

end
end Dubon2026.SourceEllipticStabilizer
