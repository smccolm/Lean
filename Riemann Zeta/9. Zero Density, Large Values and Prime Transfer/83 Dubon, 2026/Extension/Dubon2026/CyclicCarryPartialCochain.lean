import Dubon2026.RepresentationCarryCocycle
import Dubon2026.CyclicTwoCocyclePeriodSum

/-! # An explicit original cochain compares a cyclic cocycle with its carry

Partial sums of the original generator column, with its actual value at
the identity retained, give the necessary coboundary. This works for the
original infinite field-unit coefficient, so the global cyclic carry
comparison needed by DUB-17 does not assume a finite norm quotient.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n))
  (g : G) (hχ : χ g = Multiplicative.ofAdd 1)

include hχ in
/-- The original generator raised to its literal cyclic index recovers the same group element. -/
theorem cyclicCarryIndex_pow (x : G) : g ^ (χ x).toAdd.val = x := by
  apply χ.injective
  rw [map_pow, hχ]
  apply Multiplicative.toAdd.injective
  change (χ x).toAdd.val • (1 : ZMod n) = (χ x).toAdd
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

omit [NeZero n] in
include hχ in
/-- The original index character gives an actual closed generator period. -/
theorem cyclicCarryIndex_period : g ^ n = 1 := by
  apply χ.injective
  rw [map_pow, hχ, χ.map_one]
  apply Multiplicative.toAdd.injective
  change n • (1 : ZMod n) = 0
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The literal partial-column cochain, retaining the original unnormalized identity value. -/
def cyclicCarryPartialCochain (c : groupCohomology.cocycles₂ A) (x : G) : A :=
  (∑ i ∈ Finset.range (χ x).toAdd.val, c (g ^ i, g)) - c (1, 1)

omit [NeZero n] in
include hχ in
/-- In a nontrivial actual cyclic group the partial-column cochain vanishes at the original generator. -/
theorem cyclicCarryPartialCochain_generator (hn : 1 < n) (c : groupCohomology.cocycles₂ A) :
    cyclicCarryPartialCochain A χ g c g = 0 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  simp only [cyclicCarryPartialCochain, hχ, toAdd_ofAdd,
    ZMod.val_one, Finset.sum_range_one, pow_zero, groupCohomology.cocycles₂_map_one_fst, sub_self]

include hχ in
/-- Adding the explicit coboundary makes the actual generator column precisely the original carry times the original period. -/
theorem cyclicCarryPartialCochain_column (hn : 1 < n)
    (c : groupCohomology.cocycles₂ A) (x : G) :
    c (x, g) + groupCohomology.d₁₂ A (cyclicCarryPartialCochain A χ g c) (x, g) =
      zmodAdditionCarry (χ x).toAdd (χ g).toAdd •
        representationCyclicTwoCochainPeriodSum A g n c := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have hj : (χ x).toAdd.val < n := ZMod.val_lt _
  have hm : (χ (x * g)).toAdd.val = ((χ x).toAdd.val + 1) % n := by
    rw [map_mul, hχ]
    change ((χ x).toAdd + (1 : ZMod n)).val = _
    rw [ZMod.val_add, ZMod.val_one]
  change c (x, g) + (A.ρ x (cyclicCarryPartialCochain A χ g c g) -
    cyclicCarryPartialCochain A χ g c (x * g) + cyclicCarryPartialCochain A χ g c x) = _
  rw [cyclicCarryPartialCochain_generator A χ g hχ hn c, map_zero]
  simp only [cyclicCarryPartialCochain, hm, hχ, toAdd_ofAdd,
    zmodAdditionCarry, ZMod.val_one]
  by_cases h : (χ x).toAdd.val + 1 < n
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, zero_nsmul,
      Finset.sum_range_succ, cyclicCarryIndex_pow χ g hχ x]
    abel
  · have he : (χ x).toAdd.val + 1 = n := by omega
    have hs : representationCyclicTwoCochainPeriodSum A g n c =
        (∑ i ∈ Finset.range (χ x).toAdd.val, c (g ^ i, g)) + c (x, g) := by
      change (∑ i ∈ Finset.range n, c (g ^ i, g)) = _
      calc
        (∑ i ∈ Finset.range n, c (g ^ i, g)) =
            ∑ i ∈ Finset.range ((χ x).toAdd.val + 1), c (g ^ i, g) :=
          congrArg (fun N : ℕ => ∑ i ∈ Finset.range N, c (g ^ i, g)) he.symm
        _ = _ := by rw [Finset.sum_range_succ, cyclicCarryIndex_pow χ g hχ x]
    rw [he, Nat.mod_self, Nat.div_self (by omega), Finset.sum_range_zero, one_nsmul, hs]
    abel

end
end Dubon2026
