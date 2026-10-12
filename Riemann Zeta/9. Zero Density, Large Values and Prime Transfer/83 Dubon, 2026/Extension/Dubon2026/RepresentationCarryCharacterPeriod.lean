import Dubon2026.RepresentationCarryPeriod
import Dubon2026.ZModCarryPeriod

/-! # Exact original carry periods for arbitrary cyclic character values -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- An arbitrary original group element gives the literal sum of
addition carries along its actual character value, with the same coefficient. -/
theorem representationCarryCocycle_period_character (g : G) (N : ℕ) :
    representationCyclicTwoCochainPeriodSum A g N
        (representationCarryCocycle A χ a ha) =
      (∑ i ∈ Finset.range N,
        zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) • a := by
  change (∑ i ∈ Finset.range N,
    zmodAdditionCarry (χ (g ^ i)).toAdd (χ g).toAdd • a) = _
  simp_rw [χ.map_pow, toAdd_pow]
  exact Finset.sum_smul.symm

/-- The original cocycle period satisfies the exact character identity
along every closed original group period. No generator or coprimality
assumption is needed. -/
theorem representationCarryCocycle_period_mul (g : G) (N : ℕ) (hN : g ^ N = 1) :
    n • representationCyclicTwoCochainPeriodSum A g N
        (representationCarryCocycle A χ a ha) =
      (N * (χ g).toAdd.val) • a := by
  rw [representationCarryCocycle_period_character, smul_smul]
  have hz : N • (χ g).toAdd = 0 := by
    have h := congrArg (fun x => (χ x).toAdd) hN
    simpa only [map_pow, toAdd_pow, map_one, toAdd_one] using h
  rw [zmodAdditionCarry_sum_period _ N hz]

end
end Dubon2026
