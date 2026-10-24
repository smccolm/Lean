import Dubon2026.SourceEllipticTwoCyclicRootMap

/-! Assemble the actual prime cyclic-subgroup-to-root map, including degree two.
The original subgroup domain, integral modular polynomial and all allowed
residue characteristics are retained. Non-CM injectivity and inertia
equivariance remain necessary for the downstream orbit census. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- The actual cyclic-subgroup map to the roots of the exact integral prime modular polynomial. -/
def primeCyclicRootMap (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} →
      {x : K // (relationAtSeed (modularPolynomial p) W.j).IsRoot x} := by
  by_cases hp2 : p = 2
  · subst p
    exact twoCyclicRootMap W hp
  · exact oddPrimeCyclicRootMap W p hp2 hp

/-- Every prime modular-polynomial root arises from an actual cyclic subgroup of the original curve. -/
theorem primeCyclicRootMap_surjective (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    Function.Surjective (primeCyclicRootMap W p hp) := by
  by_cases hp2 : p = 2
  · subst p
    simpa only [primeCyclicRootMap, dif_pos rfl] using twoCyclicRootMap_surjective W hp
  · simpa only [primeCyclicRootMap, dif_neg hp2] using oddPrimeCyclicRootMap_surjective W p hp2 hp

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
