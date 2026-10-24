import Dubon2026.SourceEllipticTranscendentalCyclicRoots
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-! Instantiate the prime cyclic-root bijection at the literal rational
j-coordinate, using Mathlib's explicit elliptic model with prescribed j.
This discharges the generic-model transcendence input on the DUB-17/18
inertia-orbit chain; equivariance and the exceptional fibers remain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve
noncomputable section

/-- The original rational coordinate is transcendental after the actual field inclusion. -/
theorem transcendental_generic_j
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L] :
    Transcendental K (algebraMap (RatFunc K) L RatFunc.X) := by
  intro h
  exact RatFunc.transcendental_X
    ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K (RatFunc K) L)
      (algebraMap (RatFunc K) L).injective).mp h)

/-- The actual generic elliptic model has the proved prime cyclic-root bijection. -/
theorem generic_primeCyclicRootMap_bijective
    (K L : Type*) [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L]
    [DecidableEq L] [DecidableEq (RatFunc K)] [Algebra K L] [Algebra (RatFunc K) L]
    [IsScalarTower K (RatFunc K) L]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    Function.Bijective
      (primeCyclicRootMap ((ofJ (RatFunc.X : RatFunc K)).baseChange L) p
        (by exact_mod_cast ((_root_.map_ne_zero (algebraMap K L)).mpr hp))) := by
  apply primeCyclicRootMap_bijective_transcendental (K := K) _ p hp
  change Transcendental K ((ofJ (RatFunc.X : RatFunc K)).map
    (algebraMap (RatFunc K) L)).j
  rw [WeierstrassCurve.map_j, ofJ_j]
  exact transcendental_generic_j K L

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
