import Dubon2026.SourceEllipticGenericCyclicRoots
import Dubon2026.SourceEllipticCyclicRootEquivariance

/-! DUB-17/18 -> original inertia -> good reduction -> exceptional-fiber census.
For the explicit generic elliptic curve, the actual prime cyclic-subgroup
orbits agree exactly with the integral modular-polynomial root orbits, for
every subgroup of base-field automorphisms (in particular inertia). Both
injectivity and equivariance are proved upstream, rather than assumed here.
This does not yet evaluate the orbit counts or their ramification weights. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve
noncomputable section

/-- The original generic cyclic-subgroup and modular-polynomial root orbit relations coincide. -/
theorem generic_prime_cyclic_root_orbit_iff
    (K L : Type*) [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L]
    [DecidableEq L] [DecidableEq (RatFunc K)] [Algebra K L]
    [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (G : Subgroup (L ≃ₐ[RatFunc K] L))
    (H₁ H₂ : {H : AddSubgroup ((ofJ (RatFunc.X : RatFunc K)).baseChange L).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = p}) :
    (∃ σ ∈ G, fixedCurveCyclicKernelMap σ.toRingHom
      ((ofJ (RatFunc.X : RatFunc K)).baseChange L)
      ((ofJ (RatFunc.X : RatFunc K)).map_baseChange σ.toAlgHom) p H₂ = H₁) ↔
    (∃ σ ∈ G, σ (primeCyclicRootMap ((ofJ (RatFunc.X : RatFunc K)).baseChange L) p
        (by exact_mod_cast ((_root_.map_ne_zero (algebraMap K L)).mpr hp)) H₂).1 =
      (primeCyclicRootMap ((ofJ (RatFunc.X : RatFunc K)).baseChange L) p
        (by exact_mod_cast ((_root_.map_ne_zero (algebraMap K L)).mpr hp)) H₁).1) := by
  have hpL : (p : L) ≠ 0 := by
    exact_mod_cast ((_root_.map_ne_zero (algebraMap K L)).mpr hp)
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, ?_⟩
    rw [← primeCyclicRootMap_galois (ofJ (RatFunc.X : RatFunc K)) σ p hpL H₂, h]
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, (generic_primeCyclicRootMap_bijective K L p hp).1 (Subtype.ext ?_)⟩
    exact (primeCyclicRootMap_galois (ofJ (RatFunc.X : RatFunc K)) σ p hpL H₂).trans h

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
