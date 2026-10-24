import Dubon2026.SourceEllipticCompositeQuotientVariableChange
import Dubon2026.SourceEllipticCompositeQuotientBaseChange

/-! The j-invariant of the actual successive cyclic quotient, with field
and model compatibility derived from the literal quotient curves. This is
the original value map needed in the all-level modular-root bijection and
the DUB-17/18 inertia and exceptional-fiber census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- The j-invariant of the actual quotient by the original finite cyclic subgroup. -/
def cyclicQuotientJ (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) : F :=
  letI := (cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2).2
  (cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2).1.j

/-- The actual composite quotient value is unchanged by the original change of model. -/
theorem cyclicQuotientJ_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    cyclicQuotientJ (C • W) N hN (cyclicKernelVariableChange C W N H) =
      cyclicQuotientJ W N hN H := by
  letI := (cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2).2
  simp only [cyclicQuotientJ, cyclicQuotientCurve_variableChange, variableChange_j]

/-- The actual composite quotient value commutes with every original field embedding. -/
theorem cyclicQuotientJ_map
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
    (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    let hNK : (N : K) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hN
    cyclicQuotientJ (W.map f) N hNK (primeCyclicKernelMap f W N H) =
      f (cyclicQuotientJ W N hN H) := by
  intro hNK
  letI := (cyclicQuotientCurve N hN W H.1 H.2.1 H.2.2).2
  simp only [cyclicQuotientJ, cyclicQuotientCurve_map f N hN W H, map_j]

/-- The order-one quotient value is the original j-invariant. -/
theorem cyclicQuotientJ_one (W : WeierstrassCurve F) [W.IsElliptic]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 1}) :
    cyclicQuotientJ W 1 (by simp) H = W.j := by
  simp only [cyclicQuotientJ, cyclicQuotientCurve_one]

end
end Dubon2026.SourceEllipticVelu
