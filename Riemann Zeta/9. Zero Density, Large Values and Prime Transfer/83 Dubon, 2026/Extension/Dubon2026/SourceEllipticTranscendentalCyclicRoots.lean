import Dubon2026.SourceIntegralTranscendentalSeparability
import Dubon2026.SourceEllipticPrimeCyclicRootMap

/-! DUB-17/18 -> residual inertia -> good reduction -> cyclic subgroup orbit
census. The actual surjective cyclic-root map is bijective at transcendental
j by the proved separability and the existing actual cyclic-subgroup count.
No injectivity certificate or endomorphism-classification hypothesis is used.
Exceptional fibers and inertia equivariance remain separate obligations. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve
noncomputable section

/-- The exact modular polynomial has p+1 distinct roots at a transcendental j-coordinate. -/
theorem modularPolynomial_prime_root_card_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (j : L) (hj : Transcendental K j) :
    Nat.card {x : L // (relationAtSeed (modularPolynomial p) j).IsRoot x} = p + 1 := by
  classical
  let P := relationAtSeed (modularPolynomial p) j
  have hm : P.Monic := (modularPolynomial_monic p).map _
  have he : {x : L | P.IsRoot x} = P.rootSet L := by
    ext x
    simp [hm.mem_rootSet, Polynomial.aeval_def, Algebra.algebraMap_self, IsRoot.def]
  change Nat.card {x : L // x ∈ {x : L | P.IsRoot x}} = p + 1
  rw [he, Nat.card_eq_fintype_card]
  rw [card_rootSet_eq_natDegree
    (modularPolynomial_prime_separable_transcendental p hp j hj)
    (IsAlgClosed.splits _)]
  exact (modularPolynomial_monic p).natDegree_map _ |>.trans
    (modularPolynomial_prime_natDegree p)

/-- The actual cyclic-root map is bijective in the generic fiber. -/
theorem primeCyclicRootMap_bijective_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L]
    [DecidableEq L] [Algebra K L]
    (W : WeierstrassCurve L) [W.IsElliptic]
    (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) ≠ 0)
    (hj : Transcendental K W.j) :
    Function.Bijective (primeCyclicRootMap W p (by exact_mod_cast
      ((_root_.map_ne_zero (algebraMap K L)).mpr hpK))) := by
  have hpL : (p : L) ≠ 0 := by
    exact_mod_cast ((_root_.map_ne_zero (algebraMap K L)).mpr hpK)
  let C := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}
  have hc : Nat.card C = p + 1 := by
    have h := SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality
      (K := L) W hpL
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] at h
    exact h.trans (by simpa using
      SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out (by decide))
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply (primeCyclicRootMap_surjective W p hpL).bijective_of_nat_card_le
  change Nat.card C ≤ _
  rw [hc, modularPolynomial_prime_root_card_transcendental p hpK W.j hj]

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
