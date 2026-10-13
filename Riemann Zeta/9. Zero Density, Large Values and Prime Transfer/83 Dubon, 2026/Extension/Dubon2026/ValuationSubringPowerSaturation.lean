import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-! # Power saturation of the original valuation-ring units

If an integer unit is an n-th power in its actual fraction field, its root
has valuation one and is an integer unit. This is the precise comparison
needed between the original Kummer local-power kernel and the selected
local integer-unit quotients on DUB-17's S-unit image-cardinality chain.
-/
namespace Dubon2026
noncomputable section
variable {K : Type} [Field K] (A : ValuationSubring K)

/-- Nonzero powers in the actual fraction field reflect powers among the
units of its original valuation subring. -/
theorem valuationSubring_unit_mem_power_range_iff
    (n : ℕ) (hn : n ≠ 0) (x : Aˣ) :
    x ∈ (powMonoidHom n : Aˣ →* Aˣ).range ↔
      Units.map A.subtype.toMonoidHom x ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Units.map A.subtype.toMonoidHom y, (map_pow _ _ _).symm⟩
  · rintro ⟨y, hy⟩
    have hy' : (y : K) ^ n = (x.val : K) := congrArg Units.val hy
    have hVal : A.valuation (y : K) ^ n = 1 := by
      rw [← map_pow, hy']
      exact A.valuation_unit x
    have hyVal : A.valuation (y : K) = 1 :=
      (pow_eq_one_iff_of_nonneg zero_le hn).mp hVal
    refine ⟨A.unitGroupMulEquiv ⟨y, hyVal⟩, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact hy'

end
end Dubon2026
