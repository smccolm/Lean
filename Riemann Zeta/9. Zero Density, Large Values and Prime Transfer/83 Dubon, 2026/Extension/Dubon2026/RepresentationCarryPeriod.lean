import Dubon2026.RepresentationCarryCocycle
import Dubon2026.CyclicTwoCocyclePeriodSum

/-! # The exact original generator period of the actual carry cocycle -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G →* Multiplicative (ZMod n))
  (a : A) (ha : ∀ x, A.ρ x a = a)

/-- An actual cyclic character sending the original generator to one gives
an original carry cocycle whose complete generator period is the original coefficient. -/
theorem representationCarryCocycle_period (g : G)
    (hχ : χ g = Multiplicative.ofAdd 1) (hn : 1 < n) :
    representationCyclicTwoCochainPeriodSum A g n
      (representationCarryCocycle A χ a ha) = a := by
  change (∑ i ∈ Finset.range n,
    zmodAdditionCarry (χ (g ^ i)).toAdd (χ g).toAdd • a) = a
  simp_rw [χ.map_pow, hχ, toAdd_pow, toAdd_ofAdd,
    nsmul_eq_mul, mul_one]
  rw [← Finset.sum_smul, zmodAdditionCarry_sum_one hn, one_nsmul]

end
end Dubon2026
