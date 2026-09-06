import GafniTao.WeightedSubfamilyEnergy
import GafniTao.LocalZeroCount

/-!
# Local multiplicity on an absolute dyadic zero shell

The signed sharp-mollifier detector is defined on the union of the positive
and negative dyadic height slabs.  This file proves that this literal shell is
contained in the symmetric zero set at height `2 * U`, and hence inherits the
already proved unit-bin multiplicity bound.  No zero-counting estimate is
postulated here.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The natural-valued local multiplicity cap used by the shell detector. -/
noncomputable def sharpShellLocalMultiplicityCap (U : Real) : Nat :=
  Nat.ceil (globalLocalZeroLogConstant * Real.log (2 * U))

/-- Each signed dyadic shell is a subset of the symmetric source zero set at
height `2 * U`. -/
theorem absoluteDyadicZeroSlab_subset_zeroSet
    (sigma U : Real) (hU : 0 <= U) :
    absoluteDyadicZeroSlab sigma U ⊆ zeroSet sigma (2 * U) := by
  rw [absoluteDyadicZeroSlab]
  apply Finset.union_subset
  · apply zerosInRect_subset_of_rect_subset
    exact ZeroRectangle_subset sigma 1 (-2 * U) (-U)
      sigma 1 (-(2 * U)) (2 * U) le_rfl le_rfl (by linarith) (by linarith)
  · apply zerosInRect_subset_of_rect_subset
    exact ZeroRectangle_subset sigma 1 U (2 * U)
      sigma 1 (-(2 * U)) (2 * U) le_rfl le_rfl (by linarith) le_rfl

/-- The exact unit-bin multiplicity bound inherited by a signed shell. -/
theorem absoluteDyadicZeroSlab_unitBin_multiplicity_le
    (sigma U : Real) (z : Int)
    (hsigma : 0 <= sigma)
    (hU : max (Real.exp 2) 8 <= 2 * U) :
    (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
        (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1),
        zeroMultiplicity rho) <= sharpShellLocalMultiplicityCap U := by
  have hU0 : 0 <= U := by
    have : 0 < 2 * U := lt_of_lt_of_le (by positivity) hU
    linarith
  have hSub :
      (absoluteDyadicZeroSlab sigma U).filter
          (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1) ⊆
        zeroLocalUnitBin sigma (2 * U) z := by
    intro rho hrho
    rw [Finset.mem_filter] at hrho
    rw [zeroLocalUnitBin, Finset.mem_filter]
    exact ⟨absoluteDyadicZeroSlab_subset_zeroSet sigma U hU0 hrho.1,
      hrho.2⟩
  have hSum :
      (∑ rho ∈ (absoluteDyadicZeroSlab sigma U).filter
          (fun y => (z : Real) <= y.im ∧ y.im < (z : Real) + 1),
          zeroMultiplicity rho) <=
        ∑ rho ∈ zeroLocalUnitBin sigma (2 * U) z,
          zeroMultiplicity rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro rho hrho hnot
    exact Nat.zero_le _
  have hFullReal := zeroLocalUnitBin_multiplicity_le_global_log
    sigma (2 * U) z hsigma hU
  have hCeil :
      globalLocalZeroLogConstant * Real.log (2 * U) <=
        (sharpShellLocalMultiplicityCap U : Real) := by
    exact Nat.le_ceil _
  have hFull :
      (∑ rho ∈ zeroLocalUnitBin sigma (2 * U) z,
          zeroMultiplicity rho) <= sharpShellLocalMultiplicityCap U := by
    exact_mod_cast hFullReal.trans hCeil
  exact hSum.trans hFull

#print axioms absoluteDyadicZeroSlab_subset_zeroSet
#print axioms absoluteDyadicZeroSlab_unitBin_multiplicity_le

end

end GafniTao
